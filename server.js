// Ghost Hunt multiplayer server. Run: npm install && node server.js
const http=require('http'),fs=require('fs'),{WebSocketServer}=require('ws');
const T=32,CW=10,CH=8,W=41,H=25,RANGE=210,HALF=.42,PORT=process.env.PORT||3000,MAXP=15;
let grid,FL,MAP;
const rnd=(a,b)=>a+Math.random()*(b-a+1)|0;
// A new random mansion every round: a 4x3 grid of rooms with randomly placed doors, furniture (tile 3) and windows (tile 2)
function genMap(){
 for(let tries=0;tries<200;tries++){
  const g=Array.from({length:H},(_,y)=>Array.from({length:W},(_,x)=>x%CW==0||y%CH==0?1:0));
  const soV=[],soH=[];
  for(let r=0;r<3;r++){const so=soV[r]=rnd(0,5);for(const wx of[10,20,30]){const o=[Math.random()<.7?so:rnd(0,5)];if(Math.random()<.3)o.push(rnd(0,5));for(const a of o)for(let d=0;d<2;d++)g[r*CH+1+a+d][wx]=0}}
  for(let c=0;c<4;c++){const so=soH[c]=rnd(0,7);for(const wy of[8,16]){const o=[Math.random()<.7?so:rnd(0,7)];if(Math.random()<.3)o.push(rnd(0,7));for(const a of o)for(let d=0;d<2;d++)g[wy][c*CW+1+a+d]=0}}
  for(let r=0;r<3;r++)for(let c=0;c<4;c++)for(let k=rnd(0,2);k>0;k--){const w=rnd(1,2),h=rnd(1,3),x=c*CW+rnd(2,9-w),y=r*CH+rnd(2,7-h);for(let j=0;j<h;j++)for(let i=0;i<w;i++)g[y+j][x+i]=3}
  const wn=[[],[],[],[]],st=[[],[],[],[]];
  const addWin=(s,b)=>{if(s%2==0){const x=b*CW+1+(Math.random()<.6?soH[b]:rnd(0,7)),y=s?H-1:0;g[y][x]=g[y][x+1]=2;wn[s].push([x*T,y*T,2*T,T])}else{const y=b*CH+1+(Math.random()<.6?soV[b]:rnd(0,5)),x=s==1?W-1:0;g[y][x]=g[y+1][x]=2;wn[s].push([x*T,y*T,T,2*T])}};
  for(let s=0;s<4;s++){const n=s%2?3:4;for(let b=0;b<n;b++)if(Math.random()<.75)addWin(s,b);if(!wn[s].length)addWin(s,rnd(0,n-1))}
  // light strips: from each window tile straight inward until a wall or furniture stops it (side: 0 top, 1 right, 2 bottom, 3 left)
  for(let s=0;s<4;s++)for(const[x,y]of wn[s])for(let d=0;d<2;d++){
   if(s==0){const tx=x/T+d;let ty=1;while(g[ty][tx]===0)ty++;st[0].push([tx*T,0,T,ty*T])}
   if(s==2){const tx=x/T+d;let ty=H-2;while(g[ty][tx]===0)ty--;st[2].push([tx*T,(ty+1)*T,T,(H-1-ty)*T])}
   if(s==3){const ty=y/T+d;let tx=1;while(g[ty][tx]===0)tx++;st[3].push([0,ty*T,tx*T,T])}
   if(s==1){const ty=y/T+d;let tx=W-2;while(g[ty][tx]===0)tx--;st[1].push([(tx+1)*T,ty*T,(W-1-tx)*T,T])}}
  const fl=[];for(let y=0;y<H;y++)for(let x=0;x<W;x++)if(g[y][x]===0)fl.push([x,y]);
  const seen=new Set([fl[0][1]*W+fl[0][0]]),q=[fl[0]];
  for(let i=0;i<q.length;i++){const[x,y]=q[i];for(const[dx,dy]of[[1,0],[-1,0],[0,1],[0,-1]]){const nx=x+dx,ny=y+dy,k=ny*W+nx;if(g[ny]&&g[ny][nx]===0&&!seen.has(k)){seen.add(k);q.push([nx,ny])}}}
  if(seen.size!=fl.length&&tries<199)continue;
  grid=g;FL=fl;MAP={wn,st,sd:Math.random()*1e9|0};return}}
const mapMsg=()=>({t:'m',g:grid.map(r=>r.join('')),wn:MAP.wn,st:MAP.st,sd:MAP.sd});
genMap();
const inStrip=(s,g)=>MAP.st[s].some(([x,y,w,h])=>g.x>x-9&&g.x<x+w+9&&g.y>y-9&&g.y<y+h+9);
const wall=(x,y)=>{const tx=x/T|0,ty=y/T|0;return x<0||y<0||tx>=W||ty>=H||grid[ty][tx]};
const blocked=(x,y,r)=>wall(x-r,y-r)||wall(x+r,y-r)||wall(x-r,y+r)||wall(x+r,y+r);
const move=(e,dx,dy)=>{if(!blocked(e.x+dx,e.y,e.r))e.x+=dx;if(!blocked(e.x,e.y+dy,e.r))e.y+=dy};
const dist=(a,b)=>Math.hypot(a.x-b.x,a.y-b.y);
const angd=(a,b)=>{let d=a-b;while(d>Math.PI)d-=2*Math.PI;while(d<-Math.PI)d+=2*Math.PI;return d};
function los(a,b,c,d){const n=Math.hypot(c-a,d-b)/6|0;for(let i=1;i<n;i++)if(wall(a+(c-a)*i/n,b+(d-b)*i/n))return false;return true}
const hit=(h,o)=>{const dx=o.x-h.x,dy=o.y-h.y,d=Math.hypot(dx,dy);if(d>RANGE)return false;if(d<14)return true;
 return Math.abs(angd(Math.atan2(dy,dx),h.ang))<HALF&&los(h.x,h.y,o.x,o.y)};

const P=new Map();let nid=1,ph='lobby',R=null,lastG=0,msg='',bo=5,awardId=0;
// match score: g = rounds won by the ghost, h = rounds won by the hunters, t = rounds needed to win the match
let M={g:0,h:0,t:3,fin:'',last:'',aw:null};
const pick=f=>{const c=FL.filter(f);return c[Math.random()*c.length|0]};
const tc=([x,y])=>[x*T+T/2,y*T+T/2];
const send=(p,o)=>{if(p.ws.readyState==1)p.ws.send(JSON.stringify(o))};
const hostId=()=>P.keys().next().value;
const hunters=()=>[...P.values()].filter(p=>p.rd&&p.id!=R.gid);
// players who left mid-match (p.away) see the lobby while the match carries on without them
function lobby(){
 const ps=[...P.values()].map(p=>[p.id,p.name,p.pref,p.away?1:0]);
 for(const p of P.values())send(p,{t:'l',ps,host:hostId(),ph:p.away?'lobby':ph,mp:ph=='lobby'?0:ph=='awards'?2:1,msg,ms:[M.g,M.h,M.t],fin:M.fin,last:M.last,aw:M.aw,bo,me:p.id})}
function toLobby(m){ph='lobby';msg=m||'';for(const p of P.values()){p.away=false;p.rd=false}M.g=M.h=0;lobby()}
function startMatch(){
 if([...P.values()].filter(p=>!p.away).length<2)return;
 M={g:0,h:0,t:(bo+1)/2,fin:'',last:'',aw:null};
 for(const p of P.values())p.st={dmg:0,fa:0,rv:0}; // match-long stats for the awards
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
 const vol=act.filter(p=>p.pref=='g'),pool=vol.length?vol:act,gp=pool.find(p=>p.id>lastG)||pool[0];lastG=gp.id;
 const gid=gp.id,n=act.length-1,[gx,gy]=tc(pick(([x,y])=>x>30&&y>15)),hp=80+14*n;
 R={gid,time:180,lt:null,nf:10,ring:0,pk:[],spawn:5,al:null,K:Math.min(6,Math.max(3,Math.ceil(n/3))),g:{x:gx,y:gy,r:9,hp,max:hp,dash:0,dcd:0,charge:0,lit:0,stun:0,vis:0,fcd:0}};
 for(let i=0;i<R.K;i++){const[x,y]=tc(pick(()=>true));R.pk.push({x,y})}
 for(const p of P.values()){p.rd=!p.away;p.down=false;p.rev=0;p.bat=100;p.on=false;p.revs=0;p.drag=0;if(p.rd&&p.id!=gid)[p.x,p.y]=tc(pick(([x])=>x<20))}
 ph='play';msg='';lobby()}

// after the last round of a match everyone sees the awards, then each player presses Return to Lobby
function awards(){ph='awards';msg='';lobby();const id=++awardId;setTimeout(()=>{if(ph=='awards'&&awardId==id)toLobby('')},90000)}
function end(m,k){ // k: h hunters win the round, g ghost wins the round, x cancelled (no score)
 ph='over';msg=m;
 if(k=='g')M.g++;else if(k=='h')M.h++;
 const done=M.g>=M.t||M.h>=M.t;
 if(done){M.fin=`${M.g>M.h?'The ghost wins':'The hunters win'} the match, ${Math.max(M.g,M.h)} to ${Math.min(M.g,M.h)}!`;M.last=M.fin;
  const top=k2=>{let b=null;for(const p of P.values())if(p.st[k2]>0&&(!b||p.st[k2]>b.st[k2]))b=p;return b?[b.name,Math.round(b.st[k2])]:null};
  M.aw={bh:top('dmg'),sc:top('fa'),ls:top('rv')}}
 snap();lobby();
 setTimeout(()=>{if(ph!='over')return;if(done)awards();else begin()},done?6000:8000)}

function snap(){
 if(!R)return;const g=R.g,all=ph!='play',L=hunters().map(h=>[h.id,h.x|0,h.y|0,+h.ang.toFixed(2),h.on?1:0,h.down?1:0,+h.rev.toFixed(2)]);
 for(const p of P.values()){
  if(p.away)continue;
  const isG=p.id==R.gid,ob=isG||!p.rd||all,d=ob?9999:dist(p,g);
  // the ghost's position is only sent when this player is allowed to see it
  send(p,{t:'s',ph,role:isG?'ghost':p.rd?'hunter':'spec',hs:L,g:(ob||g.lit>0||g.vis>0)?[g.x|0,g.y|0]:null,
   hp:g.hp,mx:g.max,time:R.time,bat:p.bat,pk:R.pk,sc:[M.g,M.h,M.t],lt:R.lt?[R.lt.s,+R.lt.t.toFixed(2)]:null,st:g.stun>0?1:0,al:R.al?[R.al.n,+R.al.t.toFixed(1)]:null,ring:R.ring,ch:g.charge,dc:g.dcd,near:p.down?0:d<80?2:d<150?1:0})}}

setInterval(()=>{
 if(ph!='play')return;
 const dt=1/30,g=R.g,gp=P.get(R.gid),hs=hunters();
 if(!gp)return end('The ghost left: round cancelled','x');
 R.time-=dt;R.ring=Math.max(0,R.ring-dt);if(R.al&&(R.al.t-=dt)<=0)R.al=null;
 // lightning: 1.5s of flickering windows as a warning, then 1.2s of light through that side's windows
 if(R.lt){R.lt.t+=dt;
  if(R.lt.t>=1.5&&R.lt.t<2.7&&!R.lt.hit&&inStrip(R.lt.s,g)){R.lt.hit=1;g.stun=3;g.vis=5}
  if(R.lt.t>=2.7)R.lt=null}
 else{R.nf-=dt;if(R.nf<=0){R.lt={s:Math.random()*4|0,t:0,hit:0};R.nf=14+Math.random()*10}}
 for(const h of hs){
  if(h.down){h.rev=Math.max(0,h.rev-.3*dt);continue}
  const i=h.in,l=Math.hypot(i.kx,i.ky)||1;
  move(h,i.kx/l*105*dt,i.ky/l*105*dt);h.ang=i.ang;h.on=!!i.on&&h.bat>0;
  if(h.on){h.bat-=12*dt;if(h.bat<=0){h.bat=0;h.on=false}}
  for(let k=R.pk.length-1;k>=0;k--)if(dist(h,R.pk[k])<18){h.bat=Math.min(100,h.bat+60);R.pk.splice(k,1)}}
 if(R.pk.length<R.K){R.spawn-=dt;if(R.spawn<=0){R.spawn=5;const[x,y]=tc(pick(()=>true));R.pk.push({x,y})}}else R.spawn=5;
 g.stun=Math.max(0,g.stun-dt);g.vis=Math.max(0,g.vis-dt);g.fcd=Math.max(0,g.fcd-dt);
 const ip=g.stun>0?{kx:0,ky:0,dash:0,ch:0}:gp.in;if(g.stun>0)g.charge=0;g.dash=Math.max(0,g.dash-dt);g.dcd=Math.max(0,g.dcd-dt);
 if(ip.ch)g.charge=Math.min(1,g.charge+dt/2.5);
 else{if(g.charge>=1){hs.forEach(h=>{h.bat=0;h.on=false});R.pk=[];R.ring=.6}g.charge=0}
 if(ip.dash&&g.dcd<=0&&!ip.ch){g.dash=.25;g.dcd=2}
 const l=Math.hypot(ip.kx,ip.ky)||1,sp=115*(ip.ch?.45:1)*(g.dash>0?2.6:1);
 const gx0=g.x,gy0=g.y;move(g,ip.kx/l*sp*dt,ip.ky/l*sp*dt);
 // a hunter who just fainted is dragged along with the ghost for up to 2.5s or 192px
 const gdx=g.x-gx0,gdy=g.y-gy0;
 for(const o of hs)if(o.down&&o.drag>0){o.drag-=dt;const ox=o.x,oy=o.y;move(o,gdx,gdy);o.dragd-=Math.hypot(o.x-ox,o.y-oy);if(o.dragd<=0)o.drag=0}
 let n=0,chg=false;const hb=[];
 for(const h of hs){if(!h.on||h.down)continue;
  if(hit(h,g)){n++;hb.push(h)}
  for(const o of hs)if(o.down&&hit(h,o)){o.rev+=dt/2+.3*dt;if(o.rev>=1){o.down=false;o.rev=0;o.bat=Math.max(o.bat,40);o.drag=0;chg=true;h.revs++;h.st.rv++}}}
 if(n){const dm=6*Math.pow(n,.75)*dt;g.hp-=dm;for(const h of hb)h.st.dmg+=dm/n;g.lit=.25;if(g.fcd<=0){g.stun=Math.max(g.stun,Math.min(1.2,.5+.15*n));g.fcd=3.5}}else g.lit=Math.max(0,g.lit-dt);
 for(const h of hs)if(!h.down&&dist(h,g)<19){h.down=true;h.on=false;h.rev=0;h.drag=2.5;h.dragd=192;chg=true;h.st.fa++}
 if(chg)R.al={n:hs.filter(h=>!h.down).length,t:3};
 if(g.hp<=0)end('The hunters win!','h');
 else if(hs.length&&hs.every(h=>h.down))end('The ghost wins!','g');
 else if(R.time<=0)end('Time’s up: the ghost survives!','g');
 else snap()},33);

const srv=http.createServer((q,s)=>{s.setHeader('Content-Type','text/html; charset=utf-8');s.end(fs.readFileSync(__dirname+'/index.html'))});
const wss=new WebSocketServer({server:srv});
wss.on('connection',ws=>{
 let p=null;
 ws.on('message',raw=>{let m;try{m=JSON.parse(raw)}catch{return}
  if(m.t=='join'&&!p){
   if(P.size>=MAXP)return ws.send('{"t":"full"}');
   p={ws,id:nid++,name:String(m.name||'Player').slice(0,14),score:0,st:{dmg:0,fa:0,rv:0},pref:'h',away:ph=='play',rd:false,x:0,y:0,r:9,ang:0,on:false,down:false,rev:0,bat:100,revs:0,in:{kx:0,ky:0,ang:0,on:0,dash:0,ch:0}};
   P.set(p.id,p);send(p,mapMsg());lobby()}
  else if(p&&m.t=='in'){const i=p.in,c=v=>Math.max(-1,Math.min(1,+v||0));i.kx=c(m.kx);i.ky=c(m.ky);i.ang=+m.ang||0;i.on=m.on?1:0;i.dash=m.dash?1:0;i.ch=m.ch?1:0}
  else if(p&&m.t=='role'){p.pref=m.v=='g'?'g':'h';lobby()}
  else if(p&&m.t=='bo'&&ph=='lobby'&&p.id==hostId()&&[1,3,5,7].includes(+m.v)){bo=+m.v;lobby()}
  else if(p&&m.t=='leave')leave(p);
  else if(p&&m.t=='back'&&ph=='awards'&&!p.away){p.away=true;if([...P.values()].every(q=>q.away))toLobby('');else lobby()}
  else if(p&&m.t=='start'&&ph=='lobby'&&p.id==hostId())startMatch()});
 ws.on('close',()=>{if(!p)return;P.delete(p.id);
  if(ph=='play'&&(p.id==R.gid||!hunters().length))end('A player left: round cancelled','x');else if(ph=='awards'&&[...P.values()].every(q=>q.away))toLobby('');else lobby()})});
srv.listen(PORT,()=>console.log('Ghost Hunt running on port '+PORT));
