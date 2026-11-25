// Ghost Hunt multiplayer server. Run: npm install && node server.js
const http=require('http'),fs=require('fs'),{WebSocketServer}=require('ws');
const T=32,CW=10,CH=8,W=41,H=25,RANGE=210,HALF=.42,PORT=process.env.PORT||3000,MAXP=15;
const grid=[],FL=[];
for(let y=0;y<H;y++){grid[y]=[];for(let x=0;x<W;x++){
 let w=x==0||y==0||x==W-1||y==H-1;const rx=x%CW,ry=y%CH;
 if(!w&&rx==0&&!(ry==3||ry==4))w=true;
 if(!w&&ry==0&&!(rx==4||rx==5))w=true;
 if(!w&&rx>0&&ry>0){if((rx==6||rx==7)&&(ry==1||ry==2))w=true;if((rx==2||rx==3)&&(ry==5||ry==6))w=true}
 grid[y][x]=w?1:0;if(!w)FL.push([x,y])}}
const wall=(x,y)=>{const tx=x/T|0,ty=y/T|0;return x<0||y<0||tx>=W||ty>=H||grid[ty][tx]};
const blocked=(x,y,r)=>wall(x-r,y-r)||wall(x+r,y-r)||wall(x-r,y+r)||wall(x+r,y+r);
const move=(e,dx,dy)=>{if(!blocked(e.x+dx,e.y,e.r))e.x+=dx;if(!blocked(e.x,e.y+dy,e.r))e.y+=dy};
const dist=(a,b)=>Math.hypot(a.x-b.x,a.y-b.y);
const angd=(a,b)=>{let d=a-b;while(d>Math.PI)d-=2*Math.PI;while(d<-Math.PI)d+=2*Math.PI;return d};
function los(a,b,c,d){const n=Math.hypot(c-a,d-b)/6|0;for(let i=1;i<n;i++)if(wall(a+(c-a)*i/n,b+(d-b)*i/n))return false;return true}
const hit=(h,o)=>{const dx=o.x-h.x,dy=o.y-h.y,d=Math.hypot(dx,dy);if(d>RANGE)return false;if(d<14)return true;
 return Math.abs(angd(Math.atan2(dy,dx),h.ang))<HALF&&los(h.x,h.y,o.x,o.y)};

const P=new Map();let nid=1,ph='lobby',R=null,rot=0,msg='';
const pick=f=>{const c=FL.filter(f);return c[Math.random()*c.length|0]};
const tc=([x,y])=>[x*T+T/2,y*T+T/2];
const send=(p,o)=>{if(p.ws.readyState==1)p.ws.send(JSON.stringify(o))};
const hostId=()=>P.keys().next().value;
const hunters=()=>[...P.values()].filter(p=>p.rd&&p.id!=R.gid);
function lobby(){const ps=[...P.values()].map(p=>[p.id,p.name,p.score]);for(const p of P.values())send(p,{t:'l',ps,host:hostId(),ph,msg,me:p.id})}

function begin(){
 const ids=[...P.keys()];
 if(ids.length<2){ph='lobby';msg='';return lobby()}
 const gid=ids[rot++%ids.length],n=ids.length-1,[gx,gy]=tc(pick(([x,y])=>x>30&&y>15)),hp=80+14*n;
 R={gid,time:180,flash:0,nf:10,ring:0,pk:[],spawn:3,g:{x:gx,y:gy,r:9,hp,max:hp,dash:0,dcd:0,charge:0,lit:0}};
 for(const p of P.values()){p.rd=true;p.down=false;p.rev=0;p.bat=100;p.on=false;p.revs=0;if(p.id!=gid)[p.x,p.y]=tc(pick(([x])=>x<20))}
 ph='play';msg='';lobby()}

function end(m,k){ // k: h hunters win, g ghost wins, d draw, x cancelled
 ph='over';msg=m;const hs=hunters(),gp=P.get(R.gid),dn=hs.filter(h=>h.down).length;
 if(k!='x')hs.forEach(h=>h.score+=(k=='h'?2:0)+h.revs);
 if(gp&&k!='x')gp.score+=dn+(k=='g'?3:0);
 snap();lobby();setTimeout(()=>{if(ph=='over')begin()},9000)}

function snap(){
 if(!R)return;const g=R.g,all=ph!='play',L=hunters().map(h=>[h.id,h.x|0,h.y|0,+h.ang.toFixed(2),h.on?1:0,h.down?1:0,+h.rev.toFixed(2)]);
 for(const p of P.values()){
  const isG=p.id==R.gid,ob=isG||!p.rd||all,d=ob?9999:dist(p,g);
  // the ghost's position is only sent when this player is allowed to see it
  send(p,{t:'s',ph,role:isG?'ghost':p.rd?'hunter':'spec',hs:L,g:(ob||g.lit>0||R.flash>0)?[g.x|0,g.y|0]:null,
   hp:g.hp,mx:g.max,time:R.time,bat:p.bat,pk:R.pk,fl:R.flash,ring:R.ring,ch:g.charge,dc:g.dcd,near:p.down?0:d<80?2:d<150?1:0})}}

setInterval(()=>{
 if(ph!='play')return;
 const dt=1/30,g=R.g,gp=P.get(R.gid),hs=hunters();
 if(!gp)return end('The ghost left: round cancelled','x');
 R.time-=dt;R.flash=Math.max(0,R.flash-dt);R.ring=Math.max(0,R.ring-dt);R.nf-=dt;
 if(R.nf<=0){R.flash=.5;R.nf=12+Math.random()*10}
 for(const h of hs){
  if(h.down){h.rev=Math.max(0,h.rev-.3*dt);continue}
  const i=h.in,l=Math.hypot(i.kx,i.ky)||1;
  move(h,i.kx/l*105*dt,i.ky/l*105*dt);h.ang=i.ang;h.on=!!i.on&&h.bat>0;
  if(h.on){h.bat-=12*dt;if(h.bat<=0){h.bat=0;h.on=false}}
  for(let k=R.pk.length-1;k>=0;k--)if(dist(h,R.pk[k])<18){h.bat=Math.min(100,h.bat+60);R.pk.splice(k,1)}}
 R.spawn-=dt;
 if(R.spawn<=0){R.spawn=4;if(R.pk.length<3&&hs.some(h=>!h.down&&h.bat<40)){const[x,y]=tc(pick(()=>true));R.pk.push({x,y})}}
 const ip=gp.in;g.dash=Math.max(0,g.dash-dt);g.dcd=Math.max(0,g.dcd-dt);
 if(ip.ch)g.charge=Math.min(1,g.charge+dt/2.5);
 else{if(g.charge>=1){hs.forEach(h=>{h.bat=0;h.on=false});R.pk=[];R.ring=.6}g.charge=0}
 if(ip.dash&&g.dcd<=0&&!ip.ch){g.dash=.25;g.dcd=2}
 const l=Math.hypot(ip.kx,ip.ky)||1,sp=115*(ip.ch?.45:1)*(g.dash>0?2.6:1);
 move(g,ip.kx/l*sp*dt,ip.ky/l*sp*dt);
 let n=0;
 for(const h of hs){if(!h.on||h.down)continue;
  if(hit(h,g))n++;
  for(const o of hs)if(o.down&&hit(h,o)){o.rev+=dt/2+.3*dt;if(o.rev>=1){o.down=false;o.rev=0;o.bat=Math.max(o.bat,40);h.revs++}}}
 if(n){g.hp-=6*Math.pow(n,.75)*dt;g.lit=.25}else g.lit=Math.max(0,g.lit-dt);
 for(const h of hs)if(!h.down&&dist(h,g)<19){h.down=true;h.on=false;h.rev=0}
 if(g.hp<=0)end('The hunters win!','h');
 else if(hs.length&&hs.every(h=>h.down))end('The ghost wins!','g');
 else if(R.time<=0)end('Time’s up: a draw','d');
 else snap()},33);

const srv=http.createServer((q,s)=>{s.setHeader('Content-Type','text/html; charset=utf-8');s.end(fs.readFileSync(__dirname+'/index.html'))});
const wss=new WebSocketServer({server:srv});
wss.on('connection',ws=>{
 let p=null;
 ws.on('message',raw=>{let m;try{m=JSON.parse(raw)}catch{return}
  if(m.t=='join'&&!p){
   if(P.size>=MAXP)return ws.send('{"t":"full"}');
   p={ws,id:nid++,name:String(m.name||'Player').slice(0,14),score:0,rd:false,x:0,y:0,r:9,ang:0,on:false,down:false,rev:0,bat:100,revs:0,in:{kx:0,ky:0,ang:0,on:0,dash:0,ch:0}};
   P.set(p.id,p);send(p,{t:'m',g:grid.map(r=>r.join(''))});lobby()}
  else if(p&&m.t=='in'){const i=p.in,c=v=>Math.max(-1,Math.min(1,+v||0));i.kx=c(m.kx);i.ky=c(m.ky);i.ang=+m.ang||0;i.on=m.on?1:0;i.dash=m.dash?1:0;i.ch=m.ch?1:0}
  else if(p&&m.t=='start'&&ph=='lobby'&&p.id==hostId())begin()});
 ws.on('close',()=>{if(!p)return;P.delete(p.id);
  if(ph=='play'&&(p.id==R.gid||!hunters().length))end('A player left: round cancelled','x');else lobby()})});
srv.listen(PORT,()=>console.log('Ghost Hunt running on port '+PORT));
