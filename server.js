// Ghost Hunt multiplayer server. Run: npm install && node server.js
const http=require('http'),fs=require('fs'),path=require('path'),{WebSocketServer}=require('ws');
const T=32,CW=10,CH=8,W=41,H=25,RANGE=210,HALF=.42,PORT=process.env.PORT||3000,MAXP=15;
let grid,FL,MAP;
const rnd=(a,b)=>a+Math.random()*(b-a+1)|0;
// A new random mansion every round: random rooms and hallways, themed furniture (tile 3 blocks movement and light) and windows (tile 2)
// ---- random mansion generator: BSP rooms + hallways, themed furniture, windows on the outer walls ----
const MINW=4,MINH=3;
const BIG=['ballroom','billiards','dining','library','kitchen','crypt','gallery','parlor'],
 MID=['library','bedroom','office','nursery','kitchen','dining','parlor','crypt','gallery','storage','billiards'],
 SMALL=['bathroom','nursery','office','storage','bedroom','bathroom'];
function genMap(){
 for(let tries=0;tries<400;tries++){
  const g=Array.from({length:H},()=>Array(W).fill(1)),rooms=[],walls=[],doors=new Set();
  const carve=(x0,y0,x1,y1,hall)=>{for(let y=y0;y<=y1;y++)for(let x=x0;x<=x1;x++)g[y][x]=0;rooms.push({x0,y0,x1,y1,w:x1-x0+1,h:y1-y0+1,hall:!!hall,th:''})};
  const split=(x0,y0,x1,y1)=>{
   const w=x1-x0+1,h=y1-y0+1,canV=w>=2*MINW+1,canH=h>=2*MINH+1,big=w>20||h>13,a=w*h;
   if(!(canV||canH)||(!big&&Math.random()<(a<80?.85:a<170?.55:.2)))return carve(x0,y0,x1,y1);
   // sometimes carve a 2-3 tile hallway through the middle instead of a plain wall
   if(Math.random()<.3&&(w>=16||h>=11)){const cw=rnd(2,3);
    if(w>=2*MINW+cw+2&&(w>=h||h<2*MINH+cw+2)){const wx1=x0+MINW+rnd(0,w-(2*MINW+cw+2)),wx2=wx1+cw+1;
     walls.push({v:1,p:wx1,a:y0,b:y1},{v:1,p:wx2,a:y0,b:y1});carve(wx1+1,y0,wx1+cw,y1,true);split(x0,y0,wx1-1,y1);split(wx2+1,y0,x1,y1);return}
    if(h>=2*MINH+cw+2){const wy1=y0+MINH+rnd(0,h-(2*MINH+cw+2)),wy2=wy1+cw+1;
     walls.push({v:0,p:wy1,a:x0,b:x1},{v:0,p:wy2,a:x0,b:x1});carve(x0,wy1+1,x1,wy1+cw,true);split(x0,y0,x1,wy1-1);split(x0,wy2+1,x1,y1);return}}
   if(canV&&(!canH||Math.random()<w/(w+h*1.6))){const wx=x0+MINW+rnd(0,w-2*MINW-1);walls.push({v:1,p:wx,a:y0,b:y1});split(x0,y0,wx-1,y1);split(wx+1,y0,x1,y1)}
   else{const wy=y0+MINH+rnd(0,h-2*MINH-1);walls.push({v:0,p:wy,a:x0,b:x1});split(x0,y0,x1,wy-1);split(x0,wy+1,x1,y1)}};
  split(1,1,W-2,H-2);
  if(rooms.length<8)continue;
  // doors: every wall between two regions gets one or two openings (2 tiles wide when it fits)
  for(const wl of walls){const ok=i=>wl.v?g[i][wl.p]===1&&g[i][wl.p-1]===0&&g[i][wl.p+1]===0:g[wl.p][i]===1&&g[wl.p-1][i]===0&&g[wl.p+1][i]===0;
   const c=[];for(let i=wl.a;i<=wl.b;i++)if(ok(i))c.push(i);if(!c.length)continue;
   const n=1+(Math.random()<.4?1:0)+(wl.b-wl.a>14&&Math.random()<.5?1:0);
   for(let k=0;k<n;k++){const i=c[Math.random()*c.length|0],ids=ok(i+1)?[i,i+1]:ok(i-1)?[i-1,i]:[i];
    for(const j of ids){if(wl.v){g[j][wl.p]=0;doors.add(wl.p+','+j)}else{g[wl.p][j]=0;doors.add(j+','+wl.p)}}}}
  // themes
  const used={};const th=(rm,list)=>{const o=list.filter(t=>!(t=='ballroom'&&used.ballroom)).map(t=>[t,(used[t]||0)+Math.random()*.9]).sort((a,b)=>a[1]-b[1])[0][0];used[th]=1;used[o]=(used[o]||0)+1;return o};
  for(const rm of rooms.slice().sort((a,b)=>b.w*b.h-a.w*a.h)){
   const a=rm.w*rm.h,md=Math.min(rm.w,rm.h);
   rm.th=rm.hall?'hallway':a>=45&&md>=5?th(rm,BIG):a>=22&&md>=4?th(rm,MID):md>=4?th(rm,SMALL.concat(['bedroom'])):th(rm,['bathroom','storage','office'])}
  // furniture (retry until every floor tile can still be reached)
  let fin=null;
  for(let f=0;f<30&&!fin;f++){const r=furnish(g.map(r=>r.slice()),rooms,doors);if(r&&connected(r.g))fin=r}
  if(!fin)continue;
  const G2=fin.g;
  // windows on the outer walls (only where the room behind is free)
  const wn=[[],[],[],[]],st=[[],[],[],[]];let okW=true;
  const cand=s=>{const c=[];if(s%2==0){const y=s?H-1:0,iy=s?H-2:1;for(let x=1;x<W-2;x++)if(G2[iy][x]===0&&G2[iy][x+1]===0&&G2[y][x]===1&&G2[y][x+1]===1&&!doors.has(x+','+y))c.push(x)}
   else{const x=s==1?W-1:0,ix=s==1?W-2:1;for(let y=1;y<H-2;y++)if(G2[y][ix]===0&&G2[y+1][ix]===0&&G2[y][x]===1&&G2[y+1][x]===1)c.push(y)}return c};
  for(let s=0;s<4&&okW;s++){let c=cand(s);if(!c.length){okW=false;break}
   const want=rnd(2,s%2?3:4),taken=[];
   while(c.length&&taken.length<want){const p=c.splice(Math.random()*c.length|0,1)[0];if(taken.some(q=>Math.abs(q-p)<5))continue;taken.push(p)}
   for(const p of taken){if(s%2==0){G2[s?H-1:0][p]=G2[s?H-1:0][p+1]=2;wn[s].push([p*T,(s?H-1:0)*T,2*T,T])}else{const x=s==1?W-1:0;G2[p][x]=G2[p+1][x]=2;wn[s].push([x*T,p*T,T,2*T])}}}
  if(!okW)continue;
  for(let s=0;s<4;s++)for(const[x,y]of wn[s])for(let d=0;d<2;d++){
   if(s==0){const tx=x/T+d;let ty=1;while(G2[ty][tx]===0)ty++;st[0].push([tx*T,0,T,ty*T])}
   if(s==2){const tx=x/T+d;let ty=H-2;while(G2[ty][tx]===0)ty--;st[2].push([tx*T,(ty+1)*T,T,(H-1-ty)*T])}
   if(s==3){const ty=y/T+d;let tx=1;while(G2[ty][tx]===0)tx++;st[3].push([0,ty*T,tx*T,T])}
   if(s==1){const ty=y/T+d;let tx=W-2;while(G2[ty][tx]===0)tx--;st[1].push([(tx+1)*T,ty*T,(W-1-tx)*T,T])}}
  const fl=[];for(let y=0;y<H;y++)for(let x=0;x<W;x++)if(G2[y][x]===0)fl.push([x,y]);
  grid=G2;FL=fl;MAP={wn,st,sd:Math.random()*1e9|0,ob:fin.ob,ru:fin.ru,rm:rooms.map(r=>[r.x0,r.y0,r.w,r.h,r.th])};return}
 throw new Error('map generation failed')}
function connected(g){const fl=[];for(let y=0;y<H;y++)for(let x=0;x<W;x++)if(g[y][x]===0)fl.push([x,y]);
 const seen=new Set([fl[0][1]*W+fl[0][0]]),q=[fl[0]];
 for(let i=0;i<q.length;i++){const[x,y]=q[i];for(const[dx,dy]of[[1,0],[-1,0],[0,1],[0,-1]]){const nx=x+dx,ny=y+dy,k=ny*W+nx;if(g[ny]&&g[ny][nx]===0&&!seen.has(k)){seen.add(k);q.push([nx,ny])}}}
 return seen.size==fl.length}
// ---- themed furnishing. Objects are [type,x,y,w,h,quarterTurns,variant] (w,h = footprint after turning); blocking ones become tile 3 ----
function furnish(g,rooms,doors){
 const occ=Array.from({length:H},()=>Array(W).fill(0)),ob=[],ru=[],res=new Set(),pk=a=>a[Math.random()*a.length|0],coin=p=>Math.random()<p;
 for(const k of doors){res.add(k);const[x,y]=k.split(',').map(Number);for(const[dx,dy]of[[1,0],[-1,0],[0,1],[0,-1]])if(g[y+dy]&&g[y+dy][x+dx]===0)res.add((x+dx)+','+(y+dy))}
 const L2W=(o,lx,ly)=>o.r==0?[o.x+lx,o.y+ly]:o.r==1?[o.x+o.w-1-ly,o.y+lx]:o.r==2?[o.x+o.w-1-lx,o.y+o.h-1-ly]:[o.x+ly,o.y+o.h-1-lx];
 const inR=(rm,x,y)=>x>=rm.x0&&x<=rm.x1&&y>=rm.y0&&y<=rm.y1;
 const freeT=(rm,x,y)=>inR(rm,x,y)&&!occ[y][x]&&!res.has(x+','+y);
 function put(rm,t,cw,ch,x,y,r,block){const fw=r%2?ch:cw,fh=r%2?cw:ch;
  for(let j=0;j<fh;j++)for(let i=0;i<fw;i++)if(!freeT(rm,x+i,y+j))return null;
  for(let j=0;j<fh;j++)for(let i=0;i<fw;i++){occ[y+j][x+i]=block?1:2;if(block)g[y+j][x+i]=3}
  ob.push([t,x,y,fw,fh,r,rnd(0,9)]);return{x,y,w:fw,h:fh,r,cw,ch,t}}
 function place(rm,t,cw,ch,mode,block=true,rot=false){
  for(let a=0;a<40;a++){let r=0,x,y;const sw=rr=>rr%2?ch:cw,sh=rr=>rr%2?cw:ch;
   if(mode=='wall'){r=rnd(0,3);const fw=sw(r),fh=sh(r);if(rm.w<fw||rm.h<fh)continue;
    if(r==0){x=rnd(rm.x0,rm.x1-fw+1);y=rm.y0}else if(r==2){x=rnd(rm.x0,rm.x1-fw+1);y=rm.y1-fh+1}else if(r==3){x=rm.x0;y=rnd(rm.y0,rm.y1-fh+1)}else{x=rm.x1-fw+1;y=rnd(rm.y0,rm.y1-fh+1)}}
   else if(mode=='center'){r=rot&&coin(.5)?1:0;if(rot&&rm.w<rm.h)r=1;else if(rot)r=0;const fw=sw(r),fh=sh(r);if(rm.w-2<fw||rm.h-2<fh)continue;x=rnd(rm.x0+1,rm.x1-fw);y=rnd(rm.y0+1,rm.y1-fh)}
   else if(mode=='corner'){const fw=1,fh=1;x=coin(.5)?rm.x0:rm.x1;y=coin(.5)?rm.y0:rm.y1}
   else{r=rot?rnd(0,3):0;const fw=sw(r),fh=sh(r);if(rm.w<fw||rm.h<fh)continue;x=rnd(rm.x0,rm.x1-fw+1);y=rnd(rm.y0,rm.y1-fh+1)}
   const o=put(rm,t,cw,ch,x,y,r,block);if(o)return o}
  return null}
 const front=(o,i=0,d=1)=>L2W(o,i,o.ch-1+d); // tile in front of the object (local south)
 const chairsFront=(rm,o)=>{for(let i=0;i<o.cw;i++){const[x,y]=front(o,i);if(coin(.8))put(rm,'chair',1,1,x,y,(o.r+2)%4,false)}};
 const ringChairs=(rm,o)=>{for(let j=-1;j<=o.h;j++)for(let i=-1;i<=o.w;i++){const edge=i<0||j<0||i>=o.w||j>=o.h,corner=(i<0||i>=o.w)&&(j<0||j>=o.h);if(!edge||corner||!coin(.85))continue;
   const r=j<0?0:j>=o.h?2:i<0?3:1;put(rm,'chair',1,1,o.x+i,o.y+j,r,false)}};
 const rug=(rm,x,y,w,h,s)=>{x=Math.max(rm.x0,x);y=Math.max(rm.y0,y);w=Math.min(rm.x1-x+1,w);h=Math.min(rm.y1-y+1,h);if(w>=2&&h>=2)ru.push([x,y,w,h,s])};
 const rugAround=(rm,o,s)=>rug(rm,o.x-1,o.y-1,o.w+2,o.h+2,s),rugMid=(rm,s)=>{const w=Math.max(2,rm.w-4),h=Math.max(2,rm.h-3);rug(rm,rm.x0+((rm.w-w)>>1),rm.y0+((rm.h-h)>>1),w,h,s)};
 const row=(rm,types)=>{for(let a=0;a<30;a++){const s=rnd(0,3),n=types.length,len=s%2?rm.h:rm.w;if(len<n)continue;const st=rnd(0,len-n);let okAll=true;const pos=[];
   for(let i=0;i<n;i++){const x=s==0||s==2?rm.x0+st+i:s==1?rm.x1:rm.x0,y=s==0?rm.y0:s==2?rm.y1:rm.y0+st+i;if(!freeT(rm,x,y)){okAll=false;break}pos.push([x,y])}
   if(okAll){pos.forEach(([x,y],i)=>put(rm,types[i],1,1,x,y,s,true));return true}}return false};
 const plant=rm=>coin(.6)&&place(rm,'plant',1,1,'corner');
 for(const rm of rooms){const A=rm.w*rm.h,n=(a,b)=>rnd(a,b);
  switch(rm.th){
  case 'hallway':{const horiz=rm.w>=rm.h,len=horiz?rm.w:rm.h,wd=horiz?rm.h:rm.w;
   if(wd>=2)ru.push(horiz?[rm.x0,rm.y0+(wd>2?1:0),rm.w,wd>2?1:wd,5]:[rm.x0+(wd>2?1:0),rm.y0,wd>2?1:wd,rm.h,5]);
   const types=['statue','armor','plant','mirror','clock','stable','armor','statue'];
   for(let i=1;i<len-1;i+=rnd(2,4)){if(!coin(.75))continue;const side=wd>=3?rnd(0,1):coin(.5)?0:1,t=pk(types);
    if(horiz){const y=side?rm.y1:rm.y0;put(rm,t,1,1,rm.x0+i,y,side?2:0,true)}else{const x=side?rm.x1:rm.x0;put(rm,t,1,1,x,rm.y0+i,side?1:3,true)}}break}
  case 'library':{for(let i=0,k=Math.max(2,rm.w>>1)+n(0,1);i<k;i++)place(rm,'shelf',pk([1,2,2,3]),1,'wall');
   if(coin(.6))place(rm,'fire',2,1,'wall');const gl=place(rm,'globe',1,1,'any');
   const a1=place(rm,'armchair',1,1,'any',true,true);if(a1&&coin(.8))place(rm,'stable',1,1,'any');
   if(coin(.5)){const d=place(rm,'desk',2,1,'wall');if(d)chairsFront(rm,d)}rugMid(rm,0);plant(rm);break}
  case 'billiards':{const p=place(rm,'poolt',4,2,'center',true,true);if(p)rugAround(rm,p,1);else rugMid(rm,1);
   place(rm,'sofa',3,1,'wall');place(rm,'stable',1,1,'wall');if(coin(.5))place(rm,'shelf',2,1,'wall');
   for(let i=0;i<2;i++)place(rm,'stool',1,1,'any',false);place(rm,'clock',1,1,'wall');plant(rm);break}
  case 'dining':{const tw=Math.min(5,Math.max(3,rm.w-4)),t=place(rm,'dtable',tw,2,'center',true,true);if(t){ringChairs(rm,t);rugAround(rm,t,2)}
   place(rm,'sideb',2,1,'wall');if(coin(.6))place(rm,'shelf',2,1,'wall');if(coin(.5))place(rm,'clock',1,1,'wall');plant(rm);break}
  case 'bedroom':{const b=place(rm,'bed',2,3,'wall');if(b){for(const lx of[-1,2]){const[x,y]=L2W(b,lx,0);put(rm,'nstand',1,1,x,y,b.r,true)}rugAround(rm,b,3);
    const[tx,ty]=L2W(b,0,b.ch);if(coin(.6))put(rm,'trunk',2,1,tx,ty,(b.r+2)%4,true)}
   place(rm,'wardrobe',2,1,'wall');if(coin(.5))place(rm,'wardrobe',2,1,'wall');place(rm,'armchair',1,1,'any',true,true);place(rm,'mirror',1,1,'wall');plant(rm);break}
  case 'nursery':{const c=place(rm,'crib',2,2,'wall');if(c)rugAround(rm,c,4);else rugMid(rm,4);place(rm,'toychest',1,1,'wall');place(rm,'horse',1,1,'any',true,true);
   for(let i=0;i<3;i++)place(rm,'blocks',1,1,'any',false);place(rm,'armchair',1,1,'any',true,true);if(coin(.6))place(rm,'shelf',1,1,'wall');break}
  case 'kitchen':{const seq=['kfridge','kcab','ksink','kcab','kstove','kcab'].slice(0,Math.min(6,Math.max(3,rm.w-1)));row(rm,seq);if(coin(.6))row(rm,['kcab','kcab','kstove'].slice(0,Math.min(3,rm.h-1)));
   if(rm.w>=6&&rm.h>=5){const i=place(rm,'island',3,1,'center');if(i){for(let k=0;k<3;k++)if(coin(.7))put(rm,'stool',1,1,i.x+k,i.y+1,0,false)}}
   place(rm,'barrel',1,1,'corner');place(rm,'crate',1,1,'any');break}
  case 'bathroom':{place(rm,'tub',3,1,'wall');place(rm,'toilet',1,1,'wall');place(rm,'vanity',1,1,'wall');if(A>=14)place(rm,'mirror',1,1,'wall');ru.push([rm.x0+(rm.w>>1),rm.y0+(rm.h>>1),1,1,6]);break}
  case 'office':{const d=place(rm,'desk',2,1,'wall')||place(rm,'desk',2,1,'center');if(d)chairsFront(rm,d);
   for(let i=0,k=n(1,3);i<k;i++)place(rm,'shelf',pk([1,2]),1,'wall');for(let i=0,k=n(1,2);i<k;i++)place(rm,'cabinet',1,1,'wall');
   place(rm,'globe',1,1,'any');rugMid(rm,7);plant(rm);break}
  case 'ballroom':{const gp=place(rm,'grand',3,2,coin(.5)?'wall':'center',true,true);if(gp){const[bx,by]=front({...gp,cw:3,ch:2,x:gp.x,y:gp.y,w:gp.w,h:gp.h,r:gp.r},1,1);put(rm,'stool',1,1,bx,by,0,false)}
   rugMid(rm,8);for(let i=0;i<4;i++)place(rm,'statue',1,1,'corner');for(let i=0,k=n(2,4);i<k;i++)place(rm,'mirror',1,1,'wall');for(let i=0,k=n(2,3);i<k;i++)place(rm,'armchair',1,1,'wall');place(rm,'sofa',3,1,'wall');place(rm,'clock',1,1,'wall');break}
  case 'crypt':{for(let i=0,k=n(2,4);i<k;i++)place(rm,'coffin',1,2,rm.w>4&&rm.h>4&&coin(.5)?'center':'wall',true,true);place(rm,'altar',2,1,'wall');
   for(let i=0,k=n(2,4);i<k;i++)place(rm,'skull',1,1,'any',false);for(let i=0;i<2;i++)place(rm,'stable',1,1,'any');place(rm,'statue',1,1,'corner');break}
  case 'gallery':{for(let i=0,k=n(3,5);i<k;i++)place(rm,'statue',1,1,coin(.5)?'wall':'any');for(let i=0,k=n(2,4);i<k;i++)place(rm,'armor',1,1,'wall');for(let i=0,k=n(1,3);i<k;i++)place(rm,'mirror',1,1,'wall');
   place(rm,'bench',2,1,'any',false,true);rugMid(rm,9);break}
  case 'parlor':{for(let i=0,k=n(1,2);i<k;i++)place(rm,'sofa',pk([2,3]),1,'wall');for(let i=0,k=n(1,2);i<k;i++)place(rm,'armchair',1,1,'any',true,true);
   for(let i=0,k=n(1,2);i<k;i++)place(rm,'stable',1,1,'any');if(coin(.35))place(rm,'piano',2,1,'wall');if(coin(.5))place(rm,'shelf',2,1,'wall');if(coin(.5))place(rm,'fire',2,1,'wall');place(rm,'clock',1,1,'wall');rugMid(rm,pk([0,3]));plant(rm);break}
  default:{for(let i=0,k=n(4,Math.max(5,A>>2));i<k;i++)place(rm,pk(['crate','crate','barrel']),1,1,coin(.6)?'wall':'any');place(rm,'shelf',pk([1,2]),1,'wall');if(coin(.4))place(rm,'cabinet',1,1,'wall')}}
  if(rm.th!='hallway'&&coin(.25))place(rm,'plant',1,1,'corner')}
 return{g,ob,ru}}
const mapMsg=()=>({t:'m',g:grid.map(r=>r.join('')),wn:MAP.wn,st:MAP.st,sd:MAP.sd,ob:MAP.ob,ru:MAP.ru,rm:MAP.rm});
genMap();
const inStrip=(s,g)=>MAP.st[s].some(([x,y,w,h])=>g.x>x-9&&g.x<x+w+9&&g.y>y-9&&g.y<y+h+9);
const wall=(x,y)=>{const tx=x/T|0,ty=y/T|0;return x<0||y<0||tx>=W||ty>=H||grid[ty][tx]};
const blocked=(x,y,r)=>wall(x-r,y-r)||wall(x+r,y-r)||wall(x-r,y+r)||wall(x+r,y+r);
const move=(e,dx,dy)=>{if(!blocked(e.x+dx,e.y,e.r))e.x+=dx;if(!blocked(e.x,e.y+dy,e.r))e.y+=dy};
const dist=(a,b)=>Math.hypot(a.x-b.x,a.y-b.y);
const angd=(a,b)=>{let d=a-b;while(d>Math.PI)d-=2*Math.PI;while(d<-Math.PI)d+=2*Math.PI;return d};
function los(a,b,c,d){const n=Math.hypot(c-a,d-b)/6|0;for(let i=1;i<n;i++)if(wall(a+(c-a)*i/n,b+(d-b)*i/n))return false;return true}
// ghost magic: 4 purple circles appear near the hunters; MCT seconds later anyone inside one (radius MCR) loses all battery
const MCR=130,MCT=3;
const losW=(a,b,c,d)=>{const n=Math.hypot(c-a,d-b)/6|0;for(let i=1;i<n;i++){const v=wall(a+(c-a)*i/n,b+(d-b)*i/n);if(v===1||v===2||v===true)return false}return true};
function castMagic(hs,g){const alive=hs.filter(h=>!h.down),pool=alive.length?alive:hs.length?hs:[g],cs=[];
 for(let i=0;i<4;i++){const h=pool[Math.random()*pool.length|0];let c=null;
  for(let a=0;a<40&&!c;a++){const an=Math.random()*6.283,d=Math.random()*150,x=h.x+Math.cos(an)*d,y=h.y+Math.sin(an)*d,tx=x/T|0,ty=y/T|0;if(grid[ty]&&grid[ty][tx]===0)c=[x|0,y|0]}
  if(!c){const[x,y]=tc(pick(()=>true));c=[x|0,y|0]}cs.push(c)}
 R.mcs.push({t:0,c:cs})}
// a flashlight gets shorter and weaker as its battery drains: power runs from 1.0 (full) down to 0.35 (nearly empty)
const pw=h=>.35+.65*Math.max(0,Math.min(100,h.bat))/100;
const SUPT=30,sk=h=>h.sup>0?1.3:1,wt=h=>pw(h)*(h.sup>0?1.25:1);
const hit=(h,o)=>{const dx=o.x-h.x,dy=o.y-h.y,d=Math.hypot(dx,dy);if(d>RANGE*pw(h)*sk(h))return false;if(d<14)return true;
 return Math.abs(angd(Math.atan2(dy,dx),h.ang))<HALF*sk(h)&&los(h.x,h.y,o.x,o.y)};

const P=new Map();let lastK='',nid=1,ph='lobby',R=null,lastG=0,msg='',bo=5,awardId=0,gm='c',rn=5; // gm: 'r' = random turns as the ghost, 'c' = players choose their role

// match score: g = rounds won by the ghost, h = rounds won by the hunters, t = rounds needed to win the match
let M={g:0,h:0,t:3,fin:'',last:'',aw:null};
const pick=f=>{const c=FL.filter(f);return c[Math.random()*c.length|0]};
const tc=([x,y])=>[x*T+T/2,y*T+T/2];
const send=(p,o)=>{if(p.ws.readyState==1)p.ws.send(JSON.stringify(o))};
const hostId=()=>P.keys().next().value;
const hunters=()=>[...P.values()].filter(p=>p.rd&&p.id!=R.gid);
// players who left mid-match (p.away) see the lobby while the match carries on without them
function lobby(){
 const ps=[...P.values()].map(p=>[p.id,p.name,p.pref,p.away?1:0,p.pts||0]);
 for(const p of P.values())send(p,{t:'l',ps,host:hostId(),ph:p.away?'lobby':ph,mp:ph=='lobby'?0:ph=='awards'?2:1,msg,ms:[M.g,M.h,M.t],fin:M.fin,last:M.last,aw:M.aw,bo,rn,rk:ph=='over'?lastK:'',me:p.id,gm,rd:[M.r||0,M.rt||rn],md:M.mode||gm})}
function toLobby(m){ph='lobby';msg=m||'';for(const p of P.values()){p.away=false;p.rd=false}M.g=M.h=0;lobby()}
function startMatch(){
 const act=[...P.values()].filter(p=>!p.away);
 if(act.length<2)return;
 if(gm=='c'&&!act.some(p=>p.pref=='g'))return; // choose-your-role mode needs a volunteer ghost
 M={g:0,h:0,t:(bo+1)/2,fin:'',last:'',aw:null,used:new Set(),mode:gm,r:0,rt:rn};
 for(const p of P.values()){p.st={dmg:0,fa:0,rv:0};p.pts=0} // match-long stats for the awards
 begin()}
function leave(p){
 if(ph=='lobby'||p.away)return;
 const wasG=ph=='play'&&p.id==R.gid;p.away=true;p.rd=false;p.on=false;
 if(ph=='play'&&(wasG||!hunters().length))end('A player left: round cancelled','x');else lobby()}

function begin(){
 const act=[...P.values()].filter(p=>!p.away);
 if(act.length<2)return toLobby('Not enough players: back to the lobby');
 genMap();for(const p of act)send(p,mapMsg());
 // players who chose Ghost take turns haunting; if nobody did, everyone takes turns
 let gp;
 if(gm=='r'){ // everyone gets a turn at random before anyone repeats
  if(!M.used)M.used=new Set();let pool=act.filter(p=>!M.used.has(p.id));
  if(!pool.length){M.used.clear();pool=act.length>1?act.filter(p=>p.id!=lastG):act}
  gp=pool[Math.random()*pool.length|0];M.used.add(gp.id)}
 else{const vol=act.filter(p=>p.pref=='g'),pool=vol.length?vol:act;gp=pool.find(p=>p.id>lastG)||pool[0]}
 lastG=gp.id;
 const gid=gp.id,n=act.length-1,[gx,gy]=tc(FL.reduce((a,b)=>Math.hypot(b[0]*T+T/2-W*T/2,b[1]*T+T/2-H*T/2)<Math.hypot(a[0]*T+T/2-W*T/2,a[1]*T+T/2-H*T/2)?b:a)),hp=80+14*n;
 R={gid,time:180,lt:null,nf:10,ring:0,mcs:[],mb:[],pk:[],spawn:5,al:null,K:Math.min(6,Math.max(3,Math.ceil(n/3))),g:{x:gx,y:gy,r:9,hp,max:hp,dash:0,dcd:0,charge:0,lit:0,stun:0,vis:5,fcd:0}}; // the ghost starts in the middle of the map, visible for 5s
 for(let i=0;i<R.K;i++){const[x,y]=tc(pick(()=>true));R.pk.push({x,y})}
 R.sp=25+Math.random()*20;
 for(const p of P.values()){p.rd=!p.away;p.down=false;p.rev=0;p.bat=100;p.sup=0;p.on=false;p.revs=0;p.drag=0;if(p.rd&&p.id!=gid)[p.x,p.y]=tc(pick(([x,y])=>Math.hypot(x*T+T/2-gx,y*T+T/2-gy)>260))}
 ph='play';msg='';lobby()}

// after the last round of a match everyone sees the awards, then each player presses Return to Lobby
function awards(){ph='awards';msg='';lobby();const id=++awardId;setTimeout(()=>{if(ph=='awards'&&awardId==id)toLobby('')},90000)}
function end(m,k){ // k: h hunters win the round, g ghost wins the round, x cancelled (no score)
 ph='over';msg=m;lastK=k;
 if(k=='g')M.g++;else if(k=='h')M.h++;
 const rm=M.mode=='r';
 if(rm&&k!='x'){M.r++;for(const p of P.values()){if(k=='g'&&p.id==R.gid)p.pts=(p.pts||0)+1;else if(k=='h'&&p.rd&&p.id!=R.gid)p.pts=(p.pts||0)+1}}
 const done=rm?M.r>=M.rt:M.g>=M.t||M.h>=M.t;
 if(done){
  if(rm){const all=[...P.values()].filter(p=>p.pts!=null),mx=Math.max(0,...all.map(p=>p.pts)),w=all.filter(p=>p.pts==mx).map(p=>p.name);
   M.fin=mx>0?`${w.length>1?w.join(' & ')+' tie':w[0]+' wins'} with ${mx} point${mx==1?'':'s'}!`:'Nobody scored a point.'}
  else M.fin=`${M.g>M.h?'The ghost wins':'The hunters win'} the match, ${Math.max(M.g,M.h)} to ${Math.min(M.g,M.h)}!`;
  M.last=M.fin;
  const top=k2=>{let b=null;for(const p of P.values())if(p.st[k2]>0&&(!b||p.st[k2]>b.st[k2]))b=p;return b?[b.name,Math.round(b.st[k2])]:null};
  M.aw={bh:top('dmg'),sc:top('fa'),ls:top('rv')}}
 snap();lobby();
 setTimeout(()=>{if(ph!='over')return;if(done)awards();else begin()},done?6000:8000)}

function snap(){
 if(!R)return;const g=R.g,all=ph!='play',L=hunters().map(h=>[h.id,h.x|0,h.y|0,+h.ang.toFixed(2),h.on?1:0,h.down?1:0,+h.rev.toFixed(2),Math.round(h.bat),+Math.max(0,h.sup||0).toFixed(1),h.in&&h.in.on&&h.bat<=0?1:0]);
 for(const p of P.values()){
  if(p.away)continue;
  const isG=p.id==R.gid,ob=isG||!p.rd||all,d=ob?9999:dist(p,g);
  // the ghost's position is only sent when this player is allowed to see it
  send(p,{t:'s',ph,role:isG?'ghost':p.rd?'hunter':'spec',hs:L,g:(ob||g.lit>0||g.vis>0)?[g.x|0,g.y|0]:null,
   hp:g.hp,mx:g.max,time:R.time,bat:p.bat,gid:R.gid,pk:R.pk,sc:[M.g,M.h,M.t],lt:R.lt?[R.lt.s,+R.lt.t.toFixed(2)]:null,st:g.stun>0?1:0,al:R.al?[R.al.n,+R.al.t.toFixed(1)]:null,ring:R.ring,mc:R.mcs.map(m=>[+m.t.toFixed(2),m.c]),mb:R.mb.map(b=>[b.x,b.y,+b.t.toFixed(2)]),ch:g.charge,dc:g.dcd,near:p.down?0:d<80?2:d<150?1:0})}}

setInterval(()=>{
 if(ph!='play')return;
 const dt=1/30,g=R.g,gp=P.get(R.gid),hs=hunters();
 if(!gp)return end('The ghost left: round cancelled','x');
 R.time-=dt;R.ring=Math.max(0,R.ring-dt);
 // magic circles: after MCT seconds every hunter standing inside one (with a clear line to its centre) loses all battery
 for(const m of R.mcs)m.t+=dt;
 for(let i=R.mcs.length-1;i>=0;i--){const m=R.mcs[i];if(m.t<MCT)continue;R.mcs.splice(i,1);
  for(const h of hs)if(!h.down&&m.c.some(([x,y])=>dist(h,{x,y})<=MCR&&losW(x,y,h.x,h.y))){h.bat=0;h.sup=0;h.on=false}
  R.pk=R.pk.filter(q=>q.s||!m.c.some(([x,y])=>dist(q,{x,y})<=MCR));
  for(const[x,y]of m.c)R.mb.push({x,y,t:.7})}
 R.mb=R.mb.filter(b=>(b.t-=dt)>0);
if(R.al&&(R.al.t-=dt)<=0)R.al=null;
 // lightning: 1.5s of flickering windows as a warning, then 1.2s of light through that side's windows
 if(R.lt){R.lt.t+=dt;
  if(R.lt.t>=1.5&&R.lt.t<2.7&&!R.lt.hit&&inStrip(R.lt.s,g)){R.lt.hit=1;g.vis=Math.max(g.vis,4)} // lightning reveals the ghost to every hunter for 4s (no stun)
  if(R.lt.t>=2.7)R.lt=null}
 else{R.nf-=dt;if(R.nf<=0){R.lt={s:Math.random()*4|0,t:0,hit:0};R.nf=14+Math.random()*10}}
 for(const h of hs){
  if(h.down){if(!h.rbeam)h.rev=Math.max(0,h.rev-.1*dt);h.rbeam=0;continue}
  const i=h.in,l=Math.hypot(i.kx,i.ky)||1;
  move(h,i.kx/l*105*dt,i.ky/l*105*dt);h.ang=i.ang;h.on=!!i.on&&h.bat>0;
  if(h.sup>0){h.sup-=dt;if(h.sup<=0){h.sup=0;h.bat=Math.min(h.bat,100)}}
  if(h.on){h.bat-=100/30*dt;if(h.bat<=0){h.bat=0;h.on=false;h.sup=0}}
  for(let k=R.pk.length-1;k>=0;k--)if(dist(h,R.pk[k])<18){if(R.pk[k].s){h.sup=SUPT;h.bat=150}else if(h.bat<100)h.bat=Math.min(100,h.bat+60);R.pk.splice(k,1)}}
 if(R.pk.filter(q=>!q.s).length<R.K){R.spawn-=dt;if(R.spawn<=0){R.spawn=5;const[x,y]=tc(pick(()=>true));R.pk.push({x,y})}}else R.spawn=5;
 if(!R.pk.some(q=>q.s)&&!hs.some(h=>h.sup>0)){R.sp-=dt;if(R.sp<=0){R.sp=40+Math.random()*30;const[x,y]=tc(pick(()=>true));R.pk.push({x,y,s:1})}}
 g.stun=Math.max(0,g.stun-dt);g.vis=Math.max(0,g.vis-dt);g.fcd=Math.max(0,g.fcd-dt);
 const ip=g.stun>0?{kx:0,ky:0,dash:0,ch:0}:gp.in;if(g.stun>0)g.charge=0;g.dash=Math.max(0,g.dash-dt);g.dcd=Math.max(0,g.dcd-dt);
 if(ip.ch)g.charge=Math.min(1,g.charge+dt/10);
 else{if(g.charge>=1)castMagic(hs,g);g.charge=0}
 if(ip.dash&&g.dcd<=0&&!ip.ch){g.dash=.25;g.dcd=2}
 const l=Math.hypot(ip.kx,ip.ky)||1,sp=115*(ip.ch?.45:1)*(g.dash>0?2.6:1);
 const gx0=g.x,gy0=g.y;move(g,ip.kx/l*sp*dt,ip.ky/l*sp*dt);
 // a hunter who just fainted is dragged along with the ghost for up to 2.5s or 192px
 const gdx=g.x-gx0,gdy=g.y-gy0;
 for(const o of hs)if(o.down&&o.drag>0){o.drag-=dt;const ox=o.x,oy=o.y;move(o,gdx,gdy);o.dragd-=Math.hypot(o.x-ox,o.y-oy);if(o.dragd<=0)o.drag=0}
 let n=0,ne=0,chg=false;const hb=[];
 for(const h of hs){if(!h.on||h.down)continue;
  if(hit(h,g)){n++;hb.push(h);ne+=wt(h)}
  for(const o of hs)if(o.down&&hit(h,o)){o.rev+=dt/10*(h.sup>0?1.25:1);o.rbeam=1;if(o.rev>=1){o.down=false;o.rev=0;o.bat=Math.max(o.bat,40);o.drag=0;h.revs++;h.st.rv++}}}
 if(n){const dm=6*Math.pow(ne,.75)*dt;g.hp-=dm;for(const h of hb)h.st.dmg+=dm*wt(h)/ne;g.lit=.25;if(g.fcd<=0){g.stun=Math.max(g.stun,Math.min(1.2,.5+.15*n));g.fcd=3.5}}else g.lit=Math.max(0,g.lit-dt);
 for(const h of hs)if(!h.down&&dist(h,g)<19){h.down=true;h.on=false;h.rev=0;h.drag=2.5;h.dragd=192;chg=true;h.st.fa++}
 if(chg)R.al={n:hs.filter(h=>!h.down).length,t:3};
 if(g.hp<=0)end('The hunters win!','h');
 else if(hs.length&&hs.every(h=>h.down))end('The ghost wins!','g');
 else if(R.time<=0)end('Time’s up: the ghost survives!','g');
 else snap()},33);

// Title screens: any .jpg/.png/.webp you put in the images folder is offered to the page and shown at random
const IMG=/\.(jpe?g|png|webp|gif)$/i,MIME={'.jpg':'image/jpeg','.jpeg':'image/jpeg','.png':'image/png','.webp':'image/webp','.gif':'image/gif'};
const srv=http.createServer((q,s)=>{
 const u=(q.url||'/').split('?')[0];
 if(u.startsWith('/audio/')){
  const f=path.join(__dirname,'audio',path.basename(decodeURIComponent(u)));
  fs.readFile(f,(e,d)=>{if(e||!/\.mp3$/i.test(f)){s.statusCode=404;return s.end('Not found')}s.setHeader('Content-Type','audio/mpeg');s.setHeader('Cache-Control','public, max-age=86400');s.end(d)});return}
 if(u=='/logo.webp'){
  fs.readFile(path.join(__dirname,'logo.webp'),(e,d)=>{if(e){s.statusCode=404;return s.end('Not found')}s.setHeader('Content-Type','image/webp');s.setHeader('Cache-Control','public, max-age=86400');s.end(d)});return}
 if(u=='/api/splash'){
  fs.readdir(path.join(__dirname,'images'),(e,l)=>{s.setHeader('Content-Type','application/json');s.setHeader('Cache-Control','no-cache');s.end(JSON.stringify(e?[]:l.filter(f=>IMG.test(f)).sort()))});return}
 if(u.startsWith('/images/')){
  const f=path.join(__dirname,'images',path.basename(decodeURIComponent(u)));
  fs.readFile(f,(e,d)=>{if(e||!IMG.test(f)){s.statusCode=404;return s.end('Not found')}
   s.setHeader('Content-Type',MIME[path.extname(f).toLowerCase()]);s.setHeader('Cache-Control','public, max-age=86400');s.end(d)});return}
 s.setHeader('Content-Type','text/html; charset=utf-8');s.end(fs.readFileSync(__dirname+'/index.html'))});
const wss=new WebSocketServer({server:srv});
wss.on('connection',ws=>{
 let p=null;
 ws.on('message',raw=>{let m;try{m=JSON.parse(raw)}catch{return}
  if(m.t=='join'&&!p){
   if(P.size>=MAXP)return ws.send('{"t":"full"}');
   p={ws,id:nid++,name:String(m.name||'Player').slice(0,14),score:0,pts:0,st:{dmg:0,fa:0,rv:0},pref:'h',away:ph=='play',rd:false,x:0,y:0,r:9,ang:0,on:false,down:false,rev:0,bat:100,revs:0,in:{kx:0,ky:0,ang:0,on:0,dash:0,ch:0}};
   P.set(p.id,p);send(p,mapMsg());lobby()}
  else if(p&&m.t=='in'){const i=p.in,c=v=>Math.max(-1,Math.min(1,+v||0));i.kx=c(m.kx);i.ky=c(m.ky);i.ang=+m.ang||0;i.on=m.on?1:0;i.dash=m.dash?1:0;i.ch=m.ch?1:0}
  else if(p&&m.t=='role'){p.pref=m.v=='g'?'g':'h';lobby()}
  else if(p&&m.t=='bo'&&ph=='lobby'&&p.id==hostId()&&[1,3,5,7].includes(+m.v)){bo=+m.v;lobby()}
  else if(p&&m.t=='gm'&&ph=='lobby'&&p.id==hostId()&&(m.v=='r'||m.v=='c')){gm=m.v;lobby()}
  else if(p&&m.t=='rn'&&ph=='lobby'&&p.id==hostId()&&[3,5,7,10].includes(+m.v)){rn=+m.v;lobby()}
  else if(p&&m.t=='leave')leave(p);
  else if(p&&m.t=='back'&&ph=='awards'&&!p.away){p.away=true;if([...P.values()].every(q=>q.away))toLobby('');else lobby()}
  else if(p&&m.t=='start'&&ph=='lobby'&&p.id==hostId())startMatch()});
 ws.on('close',()=>{if(!p)return;P.delete(p.id);
  if(ph=='play'&&(p.id==R.gid||!hunters().length))end('A player left: round cancelled','x');else if(ph=='awards'&&[...P.values()].every(q=>q.away))toLobby('');else lobby()})});
srv.listen(PORT,()=>console.log('Ghost Hunt running on port '+PORT));
