/* Menu subscription retirement probe: open the home page's dropdown three
   times via the synced event funnel and assert the nsmenu_ subscription
   count stays at 1 (one live menu per dropdown lineage). Before the fix
   every open added one. */
const { spawn } = require('child_process');
const http = require('http');
const WebSocket = require('ws');
const CHROME = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const SESSION = 'menuprobe' + Math.floor(Date.now() / 1000);
const URL = 'http://localhost:8080/croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId=' + SESSION + '&pwd=test&appId=org.newspeaklanguage.evprobe&apiKey=none&reflector=ws://localhost:9090&files=/files';
function getJson(port, path) { return new Promise((res, rej) => { http.get({host:'127.0.0.1',port,path}, r => { let b=''; r.on('data',c=>b+=c); r.on('end',()=>{try{res(JSON.parse(b))}catch(e){rej(e)}}); }).on('error', rej); }); }
async function main() {
  const proc = spawn(CHROME, ['--headless=new','--remote-debugging-port=9477','--remote-allow-origins=*','--user-data-dir=/tmp/cq-menu-'+SESSION,'--no-first-run','--disable-gpu','--disable-background-timer-throttling','about:blank'], {stdio:'ignore'});
  let page; for (let i=0;i<100;i++){ try { const t=await getJson(9477,'/json'); page=t&&t.find(x=>x.type==='page'); if(page)break;}catch(e){} await new Promise(r=>setTimeout(r,300)); }
  const ws = new WebSocket(page.webSocketDebuggerUrl,{perMessageDeflate:false});
  await new Promise(r=>ws.on('open',r));
  let id=0; const pending=new Map(); const log=[];
  const send=(m,p)=>new Promise(res=>{const mid=++id;pending.set(mid,res);ws.send(JSON.stringify({id:mid,method:m,params:p||{}}));});
  ws.on('message',raw=>{try{const m=JSON.parse(raw); if(m.id&&pending.has(m.id)){pending.get(m.id)(m.result);pending.delete(m.id);return;}
    if(m.method==='Runtime.consoleAPICalled'){const a=m.params.args.map(x=>x.value!==undefined?String(x.value):(x.description||x.type)).join(' ');log.push('['+m.params.type+'] '+a);}}catch(e){}});
  await send('Runtime.enable');
  const ev = async e => { const r = await send('Runtime.evaluate',{expression:e,returnByValue:true}); return r&&r.result&&r.result.value; };
  await send('Page.navigate',{url:URL});
  for (let i=0;i<120;i++){ const t=await ev('document.body?document.body.innerText:""'); if (typeof t==='string'&&t.includes('Workspaces')) break; await new Promise(r=>setTimeout(r,1500)); }
  await new Promise(r=>setTimeout(r,4000));
  const MENUKEYS = "Array.from(newspeakSubscriptions.keys()).filter(k=>k.indexOf('nsmenu_')===0)";
  const DDID = await ev("(function(){var k=Array.from(newspeakSubscriptions.keys()).find(k=>k.indexOf('nsdropdownmenu_')===0);return k?k.slice('nsdropdownmenu_'.length).split('model_')[0]:null})()");
  console.log('dropdown lineage id:', JSON.stringify(DDID), '| nsmenu keys at boot:', await ev(MENUKEYS+'.length'));
  for (let n=1; n<=3; n++) {
    await ev(`nsPublish('nsdropdownmenu_','dropDownMenu_click',${JSON.stringify(DDID)}); 'PUB'`);
    await new Promise(r=>setTimeout(r,3000));
    console.log('after open '+n+': nsmenu keys =', await ev(MENUKEYS+'.length'), JSON.stringify(await ev(MENUKEYS)));
  }
  const finalCount = await ev(MENUKEYS+'.length');
  console.log('MENU LEAK BOUNDED (1 key after 3 opens):', finalCount === 1 ? 'PASS' : 'FAIL ('+finalCount+')');
  console.log('menu visible:', await ev("document.body.innerText.length") , 'chars; errors:', log.filter(l=>l.startsWith('[error]')).length);
  proc.kill();
}
main().catch(e=>{console.error(e);process.exit(1);});
