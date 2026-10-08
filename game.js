/* ONE TAKE GAME #004 — 文字サーキットレース
   No dependencies. Shape analysis, raster collisions, racing simulation and art are all local. */
(() => {
  'use strict';
  const $ = id => document.getElementById(id);
  const clamp = (v,a,b) => Math.max(a, Math.min(b,v));
  const lerp = (a,b,t) => a+(b-a)*t;
  const rand = (a,b) => a+Math.random()*(b-a);
  const TAU = Math.PI*2;
  const W=420,H=570;
  const PALETTE = [
    {name:'あか',hex:'#ff6077'}, {name:'あお',hex:'#5689f8'},
    {name:'みどり',hex:'#39c68e'}, {name:'きいろ',hex:'#ffcf55'},
    {name:'ピンク',hex:'#ef8bdb'}, {name:'しろ',hex:'#ffffff'}
  ];
  const CPUS = ['一','山','口','人','犬','猫','愛','金','火','水','草','龍','★','！','？','空','花','七','A','B','3','♡','森','川'];
  const COURSES = [
    {id:'A',name:'スピード',road:91,turns:[
      [207,498],[306,478],[351,421],[342,349],[306,303],[342,247],[329,161],
      [266,91],[160,90],[95,151],[107,245],[80,314],[85,406],[135,477]
    ],pads:[{at:.20,type:'speed'},{at:.44,type:'slow'},{at:.71,type:'speed'}]},
    {id:'B',name:'コーナー',road:91,turns:[
      [221,499],[312,468],[350,405],[314,345],[290,299],[349,236],[319,156],
      [248,84],[149,108],[77,177],[133,253],[77,327],[91,415],[153,490]
    ],pads:[{at:.15,type:'speed'},{at:.36,type:'slow'},{at:.64,type:'speed'},{at:.82,type:'slow'}]},
    {id:'C',name:'バランス',road:90,turns:[
      [199,493],[285,490],[342,449],[340,361],[311,286],[350,220],[313,131],
      [243,89],[167,99],[87,165],[103,265],[73,364],[98,444],[153,494]
    ],pads:[{at:.24,type:'speed'},{at:.52,type:'slow'},{at:.76,type:'speed'}]}
  ];
  const dom={
    title:$('titleScreen'),race:$('raceScreen'),result:$('resultScreen'),
    input:$('glyphInput'),error:$('inputError'),preview:$('previewCanvas'),
    canvas:$('raceCanvas'),stats:$('stats'),player:$('entryPlayer'),
    hint:$('courseHint'),start:$('startButton'),countdown:$('countdown'),
    toast:$('raceToast'),boost:$('boostButton'),boostCount:$('boostCount'),
    standings:$('standings'),lap:$('lapLabel'),time:$('timeLabel'),
    position:$('placeBadge'),raceCourse:$('raceCourse')
  };
  const ctx=dom.canvas.getContext('2d');
  const pctx=dom.preview.getContext('2d');
  let mute=true, audio=null;
  let selectedColor=0, currentGlyph=null, proposedChar='猫';
  let previewCpu=[], selectedCourse=0;
  let state={phase:'title',cars:[],track:null,elapsed:0,countdown:0,boostLeft:3,
    resultWait:0,toastLeft:0,toastText:'',wallHits:0,carHits:0,padHits:{speed:0,slow:0},playerRecord:false,newRecord:false};
  const shapeCache=new Map();
  const inkCache=new Map();
  const savedKey='one-take-game-004-best-lap-v1';

  function glyphCount(value) {
    if (typeof Intl.Segmenter==='function') return [...new Intl.Segmenter('ja',{granularity:'grapheme'}).segment(value)].length;
    return Array.from(value).length;
  }
  function validChar(value) {
    if (!value || !value.trim()) return false;
    if (glyphCount(value)!==1) return false;
    if (/\s/u.test(value) || /[\u0000-\u001f]/u.test(value)) return false;
    return true;
  }
  function makeCanvas(w,h){const c=document.createElement('canvas');c.width=w;c.height=h;return c;}
  function buildShape(char){
    if(shapeCache.has(char)) return shapeCache.get(char);
    const canvas=makeCanvas(192,192),cx=canvas.getContext('2d',{willReadFrequently:true});
    cx.textAlign='center';cx.textBaseline='middle';cx.fillStyle='#fff';
    let fontSize=145;
    const family='"Hiragino Kaku Gothic ProN","Yu Gothic","Meiryo",system-ui,sans-serif';
    cx.font=`900 ${fontSize}px ${family}`;
    const measure=cx.measureText(char);
    if(measure.width>166) fontSize*=166/measure.width;
    cx.font=`900 ${fontSize}px ${family}`;
    cx.fillText(char,96,96);
    const raw=cx.getImageData(0,0,192,192).data;
    let x0=192,y0=192,x1=-1,y1=-1,count=0,sumX=0,sumY=0;
    for(let y=0;y<192;y++) for(let x=0;x<192;x++){
      if(raw[(y*192+x)*4+3]<65) continue;
      x0=Math.min(x0,x);y0=Math.min(y0,y);x1=Math.max(x1,x);y1=Math.max(y1,y);
    }
    if(x1<0){ x0=75;y0=75;x1=116;y1=116;cx.fillRect(80,80,30,30); }
    // Work in actual painted bounds; no common rectangular collider is created.
    const w=x1-x0+1,h=y1-y0+1;
    const alpha=new Uint8Array(w*h);
    const bitmap=makeCanvas(w,h),bx=bitmap.getContext('2d');
    bx.drawImage(canvas,x0,y0,w,h,0,0,w,h);
    const img=bx.getImageData(0,0,w,h).data;
    const allEdge=[],allFill=[];
    let asym=0,paired=0,transitions=0;
    for(let y=0;y<h;y++){
      let was=false;
      for(let x=0;x<w;x++){
        let a=img[(y*w+x)*4+3], filled=a>=65;
        alpha[y*w+x]=filled?1:0;
        if(filled){count++;sumX+=x;sumY+=y;}
        if(filled!==was){transitions++;was=filled;}
      }
    }
    for(let y=0;y<h;y+=2) for(let x=0;x<Math.ceil(w/2);x+=2){
      const l=alpha[y*w+x],r=alpha[y*w+(w-1-x)];
      if(l||r){paired++;if(l!==r)asym++;}
    }
    const bodyW=w*Math.min(37/Math.max(w,h),.6),bodyH=h*Math.min(37/Math.max(w,h),.6);
    for(let y=0;y<h;y++) for(let x=0;x<w;x++){
      if(!alpha[y*w+x])continue;
      const edge=x===0||y===0||x===w-1||y===h-1||!alpha[y*w+x-1]||!alpha[y*w+x+1]||!alpha[(y-1)*w+x]||!alpha[(y+1)*w+x];
      const pt={x:(.5-(y+.5)/h)*bodyH,y:((x+.5)/w-.5)*bodyW};
      if(edge)allEdge.push(pt);
      if((x+y)%3===0)allFill.push(pt);
    }
    const pick=(array,max)=>{
      if(array.length<=max)return array;
      let selected=[];for(let i=0;i<max;i++)selected.push(array[Math.floor(i*array.length/max)]);return selected;
    };
    const coverage=count/(w*h),areaNorm=clamp(count/(145*145*.40),0,1.25);
    const weight=clamp(.22+.65*areaNorm,.18,.92);
    const aspect=(w-h)/Math.max(w,h);
    const symmetry=1-asym/Math.max(1,paired);
    const centerBias=Math.abs(sumX/Math.max(count,1)/w-.5)*2;
    const complexity=clamp(transitions/Math.max(1,h)*.19,0,1);
    const stability=clamp(.49+.24*aspect+.16*(symmetry-.5)-.18*centerBias-.06*complexity,.21,.83);
    const speed=clamp(.54+.12*(.55-weight)+.09*aspect+.03*(symmetry-.5),.34,.76);
    const accel=clamp(.56+.25*(.54-weight)-.045*complexity,.35,.79);
    const shape={char,bitmap,alpha,w,h,bodyW,bodyH,area:count,areaNorm,
      weight,stability,speed,accel,coverage,symmetry,complexity,centerBias,
      contour:pick(allEdge,88),sample:pick(allFill,88),colors:new Map()};
    shapeCache.set(char,shape);
    return shape;
  }
  function tinted(shape,color){
    if(shape.colors.has(color))return shape.colors.get(color);
    let canvas=makeCanvas(shape.w,shape.h),c=canvas.getContext('2d');
    c.drawImage(shape.bitmap,0,0);c.globalCompositeOperation='source-in';c.fillStyle=color;c.fillRect(0,0,shape.w,shape.h);
    c.globalCompositeOperation='source-over';shape.colors.set(color,canvas);return canvas;
  }
  function formatTime(t) {
    if(!Number.isFinite(t))return '--:--.--';
    const ct=Math.max(0,Math.round(t*100));return `${String(Math.floor(ct/6000)).padStart(2,'0')}:${String(Math.floor(ct/100)%60).padStart(2,'0')}.${String(ct%100).padStart(2,'0')}`;
  }
  function bestStored(){ try{let n=Number(localStorage.getItem(savedKey));return Number.isFinite(n)&&n>0?n:Infinity;}catch(e){return Infinity;} }
  function saveBest(value){try{localStorage.setItem(savedKey,String(value));return true;}catch(e){return false;}}
  function playSound(kind){
    if(mute)return;
    try{
      audio ||= new (window.AudioContext||window.webkitAudioContext)();
      if(audio.state==='suspended')audio.resume();
      const notes={count:[[440,.07]],go:[[660,.08],[990,.18]],boost:[[320,.07],[550,.1],[780,.13]],speed:[[700,.1]],slow:[[220,.12]],wall:[[125,.06]],lap:[[550,.07],[760,.08]],finish:[[570,.12],[760,.13],[980,.24]],record:[[720,.08],[960,.08],[1200,.23]]}[kind]||[];
      let t=audio.currentTime+.005;
      for(const [freq,dur] of notes){
        const osc=audio.createOscillator(),gain=audio.createGain();osc.type=kind==='wall'?'triangle':'sine';
        osc.frequency.setValueAtTime(freq,t);gain.gain.setValueAtTime(.0001,t);
        gain.gain.exponentialRampToValueAtTime(.045,t+.012);
        gain.gain.exponentialRampToValueAtTime(.0001,t+dur);
        osc.connect(gain).connect(audio.destination);osc.start(t);osc.stop(t+dur+.01);t+=dur*.76;
      }
    }catch(e){/* Sound is optional and never blocks play. */}
  }
  function toggleMute(){mute=!mute;document.querySelectorAll('[data-mute]').forEach(btn=>{
    btn.textContent=mute?'🔇 OFF':'🔊 ON';btn.setAttribute('aria-label',mute?'音声をオンにする':'音声をミュートにする');
  });if(!mute){try{audio ||= new (window.AudioContext||window.webkitAudioContext)();audio.resume();}catch(e){}}}

  function drawCar(c,g,atX,atY,angle,scale=1,preview=false){
    const s=c.shape;
    g.save();g.translate(atX,atY);g.rotate(angle+Math.PI/2);g.scale(scale,scale);
    const tw=clamp(s.bodyW*.22,3.6,6.5),th=clamp(s.bodyH*.37,6,10);
    const side=Math.max(1,s.bodyW*.34),fore=Math.max(1,s.bodyH*.42);
    g.shadowColor='#14163370';g.shadowBlur=preview?7:3;g.shadowOffsetY=preview?2:1;
    g.fillStyle='#35364d';
    for(const x of [-side,side])for(const y of [-fore,fore]){roundRect(g,x-tw/2,y-th/2,tw,th,2);g.fill();}
    g.shadowColor='transparent';
    g.fillStyle='#f8f5f1';
    for(const x of [-side,side]){g.fillRect(x-tw*.26,-fore-th*.37,tw*.52,1.1);g.fillRect(x-tw*.26,fore+th*.37,tw*.52,1.1);}
    g.shadowColor='#1424439c';g.shadowBlur=preview?8:3;g.shadowOffsetY=1;
    // Bitmap itself is ink-only, so gaps inside 口, 山, 人 and other glyphs remain empty.
    g.drawImage(tinted(s,c.color),-s.bodyW/2,-s.bodyH/2,s.bodyW,s.bodyH);
    g.shadowColor='transparent';
    if(!preview && c.player){g.strokeStyle='#fff';g.lineWidth=1.1;g.beginPath();g.arc(0,0,Math.max(s.bodyW,s.bodyH)*.69,0,TAU);g.stroke();}
    g.restore();
  }
  function roundRect(c,x,y,w,h,r){
    const a=Math.min(r,w/2,h/2);c.beginPath();c.moveTo(x+a,y);c.arcTo(x+w,y,x+w,y+h,a);
    c.arcTo(x+w,y+h,x,y+h,a);c.arcTo(x,y+h,x,y,a);c.arcTo(x,y,x+w,y,a);c.closePath();
  }
  function paintPreview(){
    const c=pctx,w=dom.preview.width,h=dom.preview.height;
    c.clearRect(0,0,w,h);
    c.strokeStyle='#bdd7e7';c.lineWidth=2;c.setLineDash([10,13]);
    c.beginPath();c.moveTo(0,h/2);c.lineTo(w,h/2);c.stroke();c.setLineDash([]);
    for(let i=0;i<9;i++){c.fillStyle=i%2?'#d4e6f2':'#ffffffa6';c.fillRect(i*43,0,21,6);c.fillRect(i*43,h-6,21,6);}
    if(!currentGlyph)return;
    const demo={shape:currentGlyph,color:PALETTE[selectedColor].hex,player:false};
    drawCar(demo,c,w/2,h/2,-Math.PI/2,2.3,true);
    c.fillStyle='#819bae';c.font='800 9px system-ui';c.textAlign='left';
    c.fillText('FRONT ↑',12,15);
  }
  function barLevel(v){return clamp(Math.round(1+v*4),1,5);}
  function updateStats(){
    dom.stats.innerHTML='';
    if(!currentGlyph)return;
    const stats=[['SPEED',currentGlyph.speed],['ACCEL',currentGlyph.accel],
      ['STABILITY',currentGlyph.stability],['WEIGHT',currentGlyph.weight]];
    for(const [name,n] of stats){const el=document.createElement('div');el.className='stat';
      const span=document.createElement('span');span.textContent=name;
      const bars=document.createElement('div');bars.className='stat-bars';
      for(let i=0;i<5;i++){const b=document.createElement('i');if(i<barLevel(n))b.className='on';bars.appendChild(b);}
      el.append(span,bars);dom.stats.appendChild(el);
    }
  }
  function checkInput(){
    const v=dom.input.value;
    if(!validChar(v)){
      dom.error.textContent=v.trim()?'1文字だけ入力してください':'好きな1文字を入力してください';
      currentGlyph=null;dom.player.textContent='？';paintPreview();updateStats();return false;
    }
    const changed=v!==proposedChar;
    dom.error.textContent='';proposedChar=v;currentGlyph=buildShape(v);
    if(changed&&previewCpu.length&&state.phase==='title')chooseEntrants();
    dom.player.textContent=v;paintPreview();updateStats();return true;
  }
  function randomCpu(except){
    const pool=CPUS.filter(x=>x!==except),out=[];
    while(out.length<3){const index=Math.floor(Math.random()*pool.length);out.push(pool.splice(index,1)[0]);}
    return out;
  }
  function chooseEntrants(){
    previewCpu=randomCpu(proposedChar);selectedCourse=Math.floor(Math.random()*COURSES.length);
    dom.hint.textContent=`COURSE ${COURSES[selectedCourse].id} · ${COURSES[selectedCourse].name}`;
    for(let i=0;i<3;i++)$('entryCpu'+(i+1)).textContent=previewCpu[i];
  }
  function setPhase(phase){state.phase=phase;
    dom.title.classList.toggle('hidden',phase!=='title');
    dom.race.classList.toggle('hidden',!['countdown','racing','settling'].includes(phase));
    dom.result.classList.toggle('hidden',phase!=='result');
  }
  function makeTrack(layout){
    const pts=[];const raw=layout.turns;
    // Smooth closed centripetal-ish Catmull-Rom interpolation, sampled at fixed world scale.
    for(let i=0;i<raw.length;i++){
      const a=raw[(i-1+raw.length)%raw.length],b=raw[i],c=raw[(i+1)%raw.length],d=raw[(i+2)%raw.length];
      for(let s=0;s<34;s++){
        const t=s/34,t2=t*t,t3=t2*t;
        const evalAt=j=>.5*((2*b[j])+(-a[j]+c[j])*t+(2*a[j]-5*b[j]+4*c[j]-d[j])*t2+(-a[j]+3*b[j]-3*c[j]+d[j])*t3);
        pts.push({x:evalAt(0),y:evalAt(1)});
      }
    }
    const lens=[0];let len=0;
    for(let i=0;i<pts.length;i++){
      const a=pts[i],b=pts[(i+1)%pts.length];len+=Math.hypot(b.x-a.x,b.y-a.y);lens.push(len);
    }
    return {...layout,pts,lens,length:len,pads:layout.pads.map(p=>({...p,d:p.at*len}))};
  }
  function sample(track,s){
    const L=track.length;let v=((s%L)+L)%L;
    let lo=0,hi=track.pts.length;
    while(lo+1<hi){let mid=(lo+hi)>>1;if(track.lens[mid]<=v)lo=mid;else hi=mid;}
    const a=track.pts[lo],b=track.pts[(lo+1)%track.pts.length];
    const t=clamp((v-track.lens[lo])/(track.lens[lo+1]-track.lens[lo]||1),0,1);
    const dx=b.x-a.x,dy=b.y-a.y,l=Math.hypot(dx,dy)||1;
    return {x:lerp(a.x,b.x,t),y:lerp(a.y,b.y,t),tx:dx/l,ty:dy/l,nx:-dy/l,ny:dx/l,angle:Math.atan2(dy,dx)};
  }
  function curveAt(track,d){
    const a=sample(track,d-18),b=sample(track,d+18);
    return Math.atan2(a.tx*b.ty-a.ty*b.tx,a.tx*b.tx+a.ty*b.ty)/36;
  }
  function spawnCar(char,color,player,gridIndex,cpuIndex){
    const shape=buildShape(char);
    const slot=[0,2,1,3][gridIndex]; // grid rows staggered, two lanes
    const offset=[-19,19,-19,19][slot];
    const progress=[-31,-31,-74,-74][slot];
    const c={char,color,player,index:cpuIndex,shape,progress,offset,velocity:0,
      lane:offset+rand(-2,2),seed:rand(0,TAU),skill:player?1:rand(.980,1.022),
      finishTime:null,finished:false,finishStamp:0,laps:0,lapTimes:[],lastLapTime:0,
      boostTimer:0,padTimer:0,padKind:'',padEffect:'',coolWall:0,coolCar:0,trail:[],
      wobble:rand(.85,1.25),x:0,y:0,tx:1,ty:0,nx:0,ny:1,angle:0};
    positionCar(c);return c;
  }
  function positionCar(c){const p=sample(state.track,c.progress);
    c.x=p.x+p.nx*c.offset;c.y=p.y+p.ny*c.offset;
    c.tx=p.tx;c.ty=p.ty;c.nx=p.nx;c.ny=p.ny;c.angle=p.angle;
  }
  function startRace(){
    if(!checkInput())return;
    if(previewCpu.includes(proposedChar))chooseEntrants();
    state.track=makeTrack(COURSES[selectedCourse]);
    const pool=[{char:proposedChar,color:PALETTE[selectedColor].hex,player:true},
      ...previewCpu.map((char,i)=>({char,color:['#5c8bf2','#41c28a','#ffb83f'][i],player:false}))];
    // Rearrange grid positions each run, but player remains a recognizable entrant.
    const randomSlots=[0,1,2,3];for(let i=3;i>0;i--){const j=Math.floor(rand(0,i+1));[randomSlots[i],randomSlots[j]]=[randomSlots[j],randomSlots[i]];}
    state.cars=pool.map((v,i)=>spawnCar(v.char,v.color,v.player,randomSlots[i],i));
    state.elapsed=0;state.countdown=3.84;state.boostLeft=3;state.resultWait=0;
    state.playerRecord=false;state.newRecord=false;state.toastLeft=0;state.toastText='';
    state.wallHits=0;state.carHits=0;state.padHits={speed:0,slow:0};
    dom.countdown.textContent='3';dom.boostCount.textContent='× 3';dom.boost.disabled=true;
    dom.raceCourse.textContent=`COURSE ${COURSES[selectedCourse].id} · ${COURSES[selectedCourse].name}`;
    setPhase('countdown');updateHud();render();
  }
  function countdownStep(dt){
    state.countdown=Math.max(0,state.countdown-dt);
    const label=state.countdown>3?'3':state.countdown>2?'2':state.countdown>1?'1':state.countdown>0?'GO!':'';
    if(label!==dom.countdown.textContent){
      dom.countdown.textContent=label;
      if(label)playSound(label==='GO!'?'go':'count');
    }
    if(state.countdown<=0){state.elapsed=0;setPhase('racing');dom.boost.disabled=false;}
  }
  function boost(){
    if(state.phase!=='racing'||state.boostLeft<=0)return;
    const p=state.cars.find(c=>c.player);
    if(!p||p.finished)return;
    state.boostLeft--;p.boostTimer=1.72;p.velocity+=5;
    dom.boostCount.textContent=`× ${state.boostLeft}`;
    dom.boost.classList.add('active');playSound('boost');showToast('BOOST! ⚡',.72);
  }
  function showToast(s,seconds=.6){state.toastText=s;state.toastLeft=seconds;dom.toast.textContent=s;dom.toast.classList.add('show');}
  function padAt(track,d){
    const p=((d%track.length)+track.length)%track.length;
    for(const pad of track.pads){let delta=Math.abs(p-pad.d);delta=Math.min(delta,track.length-delta);if(delta<28)return pad.type;}
    return null;
  }
  function contactWalls(c,dt){
    const limit=state.track.road/2-4;
    let peak=0;
    // Every contour vertex is tested against its own nearest road station.
    // This is not a shared car rectangle, nor a radius-only approximation.
    for(const v of c.shape.contour){
      const px=c.x+c.tx*v.x+c.nx*v.y,py=c.y+c.ty*v.x+c.ny*v.y;
      const road=sample(state.track,c.progress+v.x);
      const lateral=(px-road.x)*road.nx+(py-road.y)*road.ny;
      if(Math.abs(lateral)>Math.abs(peak))peak=lateral;
    }
    if(Math.abs(peak)>limit){
      state.wallHits++;
      const excess=Math.abs(peak)-limit;
      c.offset-=Math.sign(peak)*Math.min(11,excess*.76+1.1);
      if(c.coolWall<=0){c.velocity*=.945+.024*c.shape.stability;
        if(c.player){playSound('wall');showToast('ガードレール！',.4);}
        c.coolWall=.42;
      }
      c.offset=clamp(c.offset,-27,27);
      positionCar(c);
    }
  }
  function sampleOverlap(a,b){
    // Broad phase is only an optimization. Acceptance uses actual opaque glyph pixels.
    const radii=(Math.max(a.shape.bodyW,a.shape.bodyH)+Math.max(b.shape.bodyW,b.shape.bodyH))*.54;
    if((a.x-b.x)**2+(a.y-b.y)**2>radii*radii)return false;
    function pointsOfAInsideB(one,two){
      const s=two.shape;
      for(const p of one.shape.sample){
        const x=one.x+one.tx*p.x+one.nx*p.y,y=one.y+one.ty*p.x+one.ny*p.y;
        const dx=x-two.x,dy=y-two.y;
        const localForward=dx*two.tx+dy*two.ty;
        const localLateral=dx*two.nx+dy*two.ny;
        const ix=Math.floor((localLateral/s.bodyW+.5)*s.w);
        const iy=Math.floor((.5-localForward/s.bodyH)*s.h);
        if(ix>=0&&iy>=0&&ix<s.w&&iy<s.h&&s.alpha[iy*s.w+ix])return true;
      }
      return false;
    }
    return pointsOfAInsideB(a,b)||pointsOfAInsideB(b,a);
  }
  function carContacts(){
    const cars=state.cars;
    for(let i=0;i<cars.length;i++)for(let j=i+1;j<cars.length;j++){
      const a=cars[i],b=cars[j];if(a.finished||b.finished)continue;
      if(!sampleOverlap(a,b))continue;
      state.carHits++;
      const delta=a.offset-b.offset;
      let sign=Math.sign(delta);
      if(!sign)sign=a.index<b.index?-1:1;
      const total=a.shape.weight+b.shape.weight+.25;
      a.offset=clamp(a.offset+sign*1.7*(b.shape.weight+.15)/total,-27,27);
      b.offset=clamp(b.offset-sign*1.7*(a.shape.weight+.15)/total,-27,27);
      if(a.progress>=b.progress){b.velocity=Math.max(36,b.velocity-4.5);a.velocity=Math.min(145,a.velocity+1.8);}
      else{a.velocity=Math.max(36,a.velocity-4.5);b.velocity=Math.min(145,b.velocity+1.8);}
      if(a.coolCar<=0)a.coolCar=.18;if(b.coolCar<=0)b.coolCar=.18;
      positionCar(a);positionCar(b);
    }
  }
  function finishCar(c){
    c.finished=true;c.finishTime=state.elapsed;c.finishStamp=state.elapsed;
    if(c.player){playSound('finish');showToast('FINISH!',1.3);state.resultWait=0;dom.boost.disabled=true;}
  }
  function updateCar(c,dt){
    if(c.finished)return;
    const st=c.shape;
    c.boostTimer=Math.max(0,c.boostTimer-dt);
    c.padTimer=Math.max(0,c.padTimer-dt);
    c.coolWall=Math.max(0,c.coolWall-dt);
    c.coolCar=Math.max(0,c.coolCar-dt);
    const pad=padAt(state.track,c.progress);
    if(pad){if(c.padKind!==pad){state.padHits[pad]++;c.padTimer=pad==='speed'?1.2:.92;c.padKind=pad;c.padEffect=pad;
      if(c.player){playSound(pad);showToast(pad==='speed'?'SPEED UP!':'SLOW ZONE',.65);}
    }}else c.padKind='';
    const curv=curveAt(state.track,c.progress);
    const turn=Math.abs(curv);
    const stability=st.stability;
    const cornerPenalty=clamp(turn*(11.7+(1-stability)*7),0,.28);
    const boosted=c.boostTimer>0;
    const maxSpeed=(119+(st.speed-.5)*20)*c.skill;
    let target=maxSpeed*(1-cornerPenalty);
    if(c.padTimer>0)target*=c.padEffect==='speed'?1.16:.82;
    if(boosted)target*=1.29;
    const acceleration=79+(st.accel-.5)*47;
    c.velocity=clamp(c.velocity+(target>c.velocity?acceleration:-acceleration*1.8)*dt,0,Math.max(target,c.velocity));
    if(c.velocity>target)c.velocity=Math.max(target,c.velocity-acceleration*1.8*dt);
    const old=c.progress;
    c.progress+=Math.max(9,c.velocity)*dt;
    // Curvature, ink asymmetry and grip affect lane choice; never lock cars to a spline.
    const lateralForce=curv*c.velocity*c.velocity*.058*(1.20-stability)*(boosted?1.34:1);
    const drift=clamp(lateralForce,-19,19);
    const wiggle=Math.sin(c.progress*.023+c.seed)*(1-stability)*3*c.wobble;
    const desired=clamp(c.lane+drift+wiggle,-27,27);
    c.offset+=clamp(dt*(2.9+stability),0,1)*(desired-c.offset);
    positionCar(c);
    contactWalls(c,dt);
    const L=state.track.length;
    for(let lap=c.laps+1;lap<=3;lap++){
      // A lap requires a full, monotonically increasing travelled course-length.
      // Merely crossing/touching the start line does not affect the counter.
      if(old<lap*L && c.progress>=lap*L){
        c.laps=lap;const lapTime=state.elapsed-c.lastLapTime;
        c.lapTimes.push(lapTime);c.lastLapTime=state.elapsed;
        if(c.player&&lap<3){playSound('lap');showToast(`LAP ${lap+1} / 3`,.85);}
        if(lap===3){finishCar(c);break;}
      }
    }
    if(boosted&&Math.random()<.6)c.trail.push({x:c.x-c.tx*12,y:c.y-c.ty*12,life:.38});
    c.trail.forEach(p=>p.life-=dt);c.trail=c.trail.filter(p=>p.life>0).slice(-18);
  }
  function simulate(dt){
    if(state.phase==='countdown'){countdownStep(dt);return;}
    if(!['racing','settling'].includes(state.phase))return;
    state.elapsed+=dt;
    state.toastLeft=Math.max(0,state.toastLeft-dt);
    if(!state.toastLeft)dom.toast.classList.remove('show');
    for(const car of state.cars)updateCar(car,dt);
    carContacts();
    const p=state.cars.find(c=>c.player);
    if(p.finished){
      state.resultWait+=dt;
      state.phase='settling';
      if(state.cars.every(c=>c.finished)||state.resultWait>=4.2){showResult();return;}
    }
    updateHud();
  }
  function racingOrder(){return [...state.cars].sort((a,b)=>{
    if(a.finished&&b.finished)return a.finishTime-b.finishTime;
    if(a.finished)return -1;if(b.finished)return 1;
    return b.progress-a.progress;
  });}
  function updateHud(){
    if(!state.cars.length)return;
    const ranking=racingOrder(),player=state.cars.find(c=>c.player),rank=ranking.indexOf(player)+1;
    dom.position.innerHTML=`${rank}<small>位</small>`;
    dom.lap.textContent=`LAP ${clamp(player.laps+1,1,3)} / 3`;
    dom.time.textContent=`TIME ${formatTime(player.finishTime??state.elapsed)}`;
    dom.standings.replaceChildren();
    for(let i=0;i<ranking.length;i++){
      let car=ranking[i],div=document.createElement('div');div.className='rank-item'+(car.player?' is-player':'');
      const num=document.createElement('span');num.className='rank-num';num.textContent=`${i+1}`;
      const glyph=document.createElement('span');glyph.className='rank-char';glyph.style.color=car.color;glyph.textContent=car.char;
      const ident=document.createElement('small');ident.textContent=car.player?'YOU':`CPU ${car.index}`;
      div.append(num,glyph,ident);dom.standings.appendChild(div);
    }
    dom.boost.classList.toggle('active',player.boostTimer>0);
    dom.boost.disabled=state.phase!=='racing'||state.boostLeft<=0;
  }
  function showResult(){
    const player=state.cars.find(c=>c.player);
    const L=state.track.length;
    const final=state.cars.map(c=>({...c,officialTime:c.finishTime??(state.elapsed+(3*L-c.progress)/Math.max(c.velocity,60))}));
    final.sort((a,b)=>a.officialTime-b.officialTime);
    const placement=final.findIndex(c=>c.player)+1;
    const playerLap=Math.min(...player.lapTimes);
    const oldRecord=bestStored();const newRecord=Number.isFinite(playerLap)&&playerLap<oldRecord-.00001;
    if(newRecord)saveBest(playerLap);
    state.newRecord=newRecord;
    const ordinals=['1st','2nd','3rd','4th'];
    $('resultKicker').textContent=placement===1?'CHAMPION!':'FINISH!';
    $('resultSubtitle').textContent=`COURSE ${state.track.id} · ${state.track.name} · 3周完走！`;
    const podium=$('resultPodium');podium.replaceChildren();
    for(let i=0;i<3;i++){const c=final[i],d=document.createElement('div');d.className='podium-item'+(c.player?' is-player':'');
      const glyph=document.createElement('span');glyph.className='podium-glyph';glyph.textContent=c.char;glyph.style.color=c.color;
      const caption=document.createElement('small');caption.textContent=`${ordinals[i]} ${c.player?'PLAYER':'CPU'}`;
      d.append(glyph,caption);podium.appendChild(d);
    }
    const list=$('resultStandings');list.replaceChildren();
    final.forEach((c,i)=>{const row=document.createElement('div');row.className='result-row'+(c.player?' player-row':'');
      const ord=document.createElement('span');ord.className='ordinal';ord.textContent=ordinals[i];
      const gly=document.createElement('span');gly.className='car-glyph';gly.style.color=c.color;gly.textContent=c.char;
      const ident=document.createElement('span');ident.className='identity';ident.textContent=c.player?'PLAYER':`CPU ${c.index}`;
      const time=document.createElement('span');time.className='result-time';time.textContent=(c.finishTime===null?'≈':'')+formatTime(c.officialTime);
      row.append(ord,gly,ident,time);list.appendChild(row);
    });
    $('resultPlace').textContent=ordinals[placement-1];
    $('resultTime').textContent=formatTime(player.finishTime??state.elapsed);
    $('resultLap').textContent=formatTime(playerLap);
    $('recordLabel').textContent=newRecord?'★ NEW RECORD! ★':placement===1?'★ YOU WIN! ★':'';
    $('allTimeBest').textContent=`歴代 BEST LAP ${formatTime(bestStored())}`;
    setPhase('result');if(newRecord)playSound('record');
  }
  function trackPath(c,t){
    c.beginPath();const a=t.pts;c.moveTo(a[0].x,a[0].y);
    for(let i=1;i<a.length;i++)c.lineTo(a[i].x,a[i].y);c.closePath();
  }
  function background(c,t){
    const bg=c.createLinearGradient(0,0,420,570);bg.addColorStop(0,'#d2f6c3');bg.addColorStop(1,'#9bdfa8');
    c.fillStyle=bg;c.fillRect(0,0,W,H);
    c.save();
    for(let row=0;row<16;row++)for(let col=0;col<13;col++){
      const x=(col*37+row*17)%W,y=row*39;
      c.fillStyle=(col+row)%4===0?'#ecffd250':'#79cb9a25';
      c.beginPath();c.arc(x,y,2.2+(col%3),0,TAU);c.fill();
    }
    // Playground decals intentionally avoid the road surface.
    c.fillStyle='#fdfce3';c.textAlign='center';c.font='1000 18px system-ui';
    c.fillText('MOJI',210,246);c.fillStyle='#ef9098';c.font='1000 19px system-ui';c.fillText('CIRCUIT',210,266);
    c.font='1000 12px system-ui';c.fillStyle='#71ac91';c.fillText(`COURSE ${t.id}`,210,284);
    c.lineWidth=3;c.strokeStyle='#fff7';
    for(const [x,y,r] of [[205,317,17],[211,198,17],[180,355,9]]){
      c.beginPath();c.arc(x,y,r,0,TAU);c.stroke();
    }
    for(let i=0;i<7;i++){
      const x=155+(i*43)%145,y=365+(i%2)*15;
      c.fillStyle=i%2?'#ffb8a8':'#fff4a8';
      c.beginPath();for(let a=0;a<5;a++){
        const ang=-Math.PI/2+a*TAU/5,px=x+Math.cos(ang)*5,py=y+Math.sin(ang)*5;
        if(a===0)c.moveTo(px,py);else c.lineTo(px,py);
      }c.closePath();c.fill();
    }
    c.restore();
  }
  function drawRoad(c,t){
    c.save();c.lineJoin='round';c.lineCap='round';
    trackPath(c,t);c.strokeStyle='#607e89a6';c.lineWidth=t.road+23;c.stroke();
    trackPath(c,t);c.strokeStyle='#fb6e76';c.lineWidth=t.road+18;c.stroke();
    trackPath(c,t);c.strokeStyle='#fff8ef';c.lineWidth=t.road+18;c.setLineDash([15,16]);c.stroke();c.setLineDash([]);
    trackPath(c,t);c.strokeStyle='#475f8b';c.lineWidth=t.road+3;c.stroke();
    trackPath(c,t);c.strokeStyle='#fffaee';c.lineWidth=t.road-1;c.stroke();
    trackPath(c,t);c.strokeStyle='#e3d9c5';c.lineWidth=1.5;c.setLineDash([8,18]);c.stroke();c.setLineDash([]);
    for(const pad of t.pads)drawPad(c,t,pad);
    // Racing-direction start line across the road; tiles are orthogonal to its tangent.
    const p=sample(t,0);
    c.translate(p.x,p.y);c.rotate(p.angle);
    const across=t.road-6,tile=7;
    for(let row=0;row<2;row++)for(let i=0;i<Math.ceil(across/tile);i++){
      c.fillStyle=(row+i)%2?'#252946':'#fff';
      c.fillRect(-row*tile,-across/2+i*tile,tile,Math.min(tile,across-i*tile));
    }
    c.restore();
  }
  function drawPad(c,t,pad){
    const p=sample(t,pad.d);
    c.save();c.translate(p.x,p.y);c.rotate(p.angle);
    const fast=pad.type==='speed',w=47,h=t.road-13;
    c.fillStyle=fast?'#58d9ed':'#e8c083';c.strokeStyle=fast?'#319fc6':'#ce9a62';c.lineWidth=2;
    roundRect(c,-w/2,-h/2,w,h,6);c.fill();c.stroke();
    c.fillStyle=fast?'#e8fcff':'#a07755';
    if(fast){for(let j=-1;j<=1;j++){
      c.beginPath();c.moveTo(-8+j*10,-10);c.lineTo(7+j*10,0);c.lineTo(-8+j*10,10);
      c.lineWidth=4;c.lineCap='round';c.lineJoin='round';c.strokeStyle='#e9faff';c.stroke();
    }}else{
      for(let x=-14;x<19;x+=10)for(let y=-21;y<26;y+=15){c.beginPath();c.arc(x+(y%3),y,2.2,0,TAU);c.fill();}
      c.fillStyle='#fff3d3';c.font='1000 11px system-ui';c.textAlign='center';c.fillText('SLOW',0,4);
    }
    c.restore();
  }
  function drawCarOnTrack(c,car){
    if(car.finished && state.elapsed-car.finishStamp>1.1)return;
    c.save();if(car.finished)c.globalAlpha=Math.max(0,1-(state.elapsed-car.finishStamp)/1.1);
    for(const p of car.trail){
      c.globalAlpha=(p.life/.38)*.45;c.fillStyle=car.player?'#87f4ff':'#fff';
      c.beginPath();c.arc(p.x,p.y,3.4,0,TAU);c.fill();
    }
    c.globalAlpha=1;
    if(car.boostTimer>0){
      const glow=c.createRadialGradient(car.x,car.y,3,car.x,car.y,32);
      glow.addColorStop(0,'#98faff9a');glow.addColorStop(1,'#86d8ff00');
      c.fillStyle=glow;c.beginPath();c.arc(car.x,car.y,32,0,TAU);c.fill();
      c.strokeStyle='#cfffffc9';c.lineWidth=1.3;
      for(let i=0;i<3;i++){
        const lateral=(i-1)*10,back=20+i*8;
        c.beginPath();c.moveTo(car.x-car.tx*back+car.nx*lateral,car.y-car.ty*back+car.ny*lateral);
        c.lineTo(car.x-car.tx*(back+15)+car.nx*lateral,car.y-car.ty*(back+15)+car.ny*lateral);c.stroke();
      }
    }
    // Tiny identification only for the human player; the glyph remains the body.
    if(car.player){
      c.fillStyle='#222d52bb';c.beginPath();c.arc(car.x+car.nx*24-car.tx*5,car.y+car.ny*24-car.ty*5,9,0,TAU);c.fill();
      c.fillStyle='#fff';c.font='1000 10px system-ui';c.textAlign='center';c.textBaseline='middle';
      c.fillText('P',car.x+car.nx*24-car.tx*5,car.y+car.ny*24-car.ty*5+1);
    }
    drawCar(car,c,car.x,car.y,car.angle,1);
    c.restore();
  }
  function render(){
    if(!state.track)return;
    ctx.clearRect(0,0,W,H);
    background(ctx,state.track);drawRoad(ctx,state.track);
    // Further racers are drawn first; all positions remain in common world units.
    for(const car of [...state.cars].sort((a,b)=>a.y-b.y))drawCarOnTrack(ctx,car);
    ctx.fillStyle='#fffdf9aa';roundRect(ctx,10,10,106,25,10);ctx.fill();
    ctx.fillStyle='#566e86';ctx.font='1000 12px system-ui';ctx.textBaseline='middle';ctx.textAlign='center';
    ctx.fillText(`COURSE ${state.track.id}`,63,22);
    if(state.phase==='countdown'){
      ctx.fillStyle='#293c6b2b';ctx.fillRect(0,0,W,H);
    }
  }
  let lastFrame=performance.now();
  function animationFrame(time){
    const dt=clamp((time-lastFrame)/1000,0,.05);lastFrame=time;
    if(state.phase==='countdown'||state.phase==='racing'||state.phase==='settling'){
      simulate(dt);if(state.phase!=='result')render();
    }
    requestAnimationFrame(animationFrame);
  }
  function init(){
    const colorBox=$('colorOptions');
    PALETTE.forEach((p,i)=>{
      const btn=document.createElement('button');btn.type='button';btn.className='color-dot';btn.style.background=p.hex;
      btn.setAttribute('aria-label',p.name);btn.setAttribute('aria-pressed',String(i===selectedColor));
      btn.addEventListener('click',()=>{
        selectedColor=i;$('colorName').textContent=p.name;
        colorBox.querySelectorAll('button').forEach((b,j)=>b.setAttribute('aria-pressed',String(i===j)));
        paintPreview();
      });colorBox.appendChild(btn);
    });
    dom.input.addEventListener('input',checkInput);
    dom.input.addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();dom.input.blur();dom.start.click();}});
    dom.start.addEventListener('click',startRace);
    dom.boost.addEventListener('click',boost);
    dom.race.addEventListener('pointerdown',e=>{
      if(e.target.closest('button'))return;
      boost();
    });
    $('retryButton').addEventListener('click',()=>{chooseEntrants();startRace();});
    $('changeButton').addEventListener('click',()=>{chooseEntrants();setPhase('title');});
    document.querySelectorAll('[data-mute]').forEach(btn=>btn.addEventListener('click',toggleMute));
    window.addEventListener('keydown',e=>{
      if(state.phase!=='racing'||e.repeat)return;
      if(e.code==='Space'||(e.code==='Enter'&&document.activeElement?.tagName!=='BUTTON')){
        e.preventDefault();boost();
      }
    });
    window.addEventListener('resize',()=>{if(state.phase==='title')paintPreview();});
    checkInput();chooseEntrants();setPhase('title');requestAnimationFrame(animationFrame);
  }
  // Browser smoke-test hook: advances the same update function used in real play.
  // Not used by players; useful for reproducing every course/character combination.
  window.__OTG_TEST__={
    snapshot:()=>({phase:state.phase,time:state.elapsed,course:state.track?.id,
      cars:state.cars.map(c=>({char:c.char,player:c.player,progress:c.progress,
        laps:c.laps,finished:c.finished,finishTime:c.finishTime,lapTimes:c.lapTimes,
        speed:c.velocity,offset:c.offset,bodyW:c.shape.bodyW,bodyH:c.shape.bodyH,
        contour:c.shape.contour.length,area:c.shape.area})),
      boosts:state.boostLeft,muted:mute,record:bestStored(),wallHits:state.wallHits,carHits:state.carHits,padHits:state.padHits}),
    advance:(seconds)=>{
      const steps=Math.ceil(Math.min(120,seconds)*60),dt=seconds/steps;
      for(let i=0;i<steps;i++){if(state.phase==='result')break;simulate(dt);}
      if(state.phase!=='result')render();return state.phase;
    },
    setCourse:(i)=>{selectedCourse=clamp(i,0,COURSES.length-1);dom.hint.textContent=`COURSE ${COURSES[selectedCourse].id} · ${COURSES[selectedCourse].name}`;},
    inspectGlyph:char=>{const s=buildShape(char);return{char:s.char,width:s.bodyW,height:s.bodyH,area:s.area,
      symmetry:s.symmetry,complexity:s.complexity,stats:{speed:s.speed,accel:s.accel,stability:s.stability,weight:s.weight},edge:s.contour.length};},
    intersects:()=>{const c=state.cars;return c.length>1?sampleOverlap(c[0],c[1]):false;},
    pathLength:()=>state.track?.length,
    key:savedKey
  };
  init();
})();
