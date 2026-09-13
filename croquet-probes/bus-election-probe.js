/* Does a BUS completion go out ONCE per session, via the elected initiator?

   The probe IS the external agent: it holds an SSE subscription to /_ns/bus,
   answers completion_request with a completion_response, and counts how many
   requests reach it. That count is the measurement - a bus completion is
   billed and non-idempotent exactly like an HTTP one, so two clients must
   produce one request, and a late joiner's replay must produce none.

   Needs the front door running with --bus.  Run: node bus-election-probe.js */
const http=require('http');
const { sleep, launchBrowser, click, waitFor, bootIDE, evalDoIt, makeChecker } = require('./harness');
const ORIGIN='http://localhost:8080', AGENT='probeagent', CHAT='ProbeBusChat';
const REPLY='BUS-REPLY-424242';
const SESSION='bus'+Math.floor(Date.now()/1000);
const URL_C=ORIGIN+'/croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId='
  +SESSION+'&pwd=test&appId=org.newspeaklanguage.busel&apiKey=none&reflector=ws://localhost:9090&files=/files';
const { check, summary } = makeChecker();
let requests=0, seenCorr=[];

function get(path){return new Promise((res,rej)=>{http.get(ORIGIN+path,r=>{let b='';r.on('data',c=>b+=c);r.on('end',()=>res(b))}).on('error',rej)})}
function post(path,obj,token){return new Promise((res,rej)=>{const d=JSON.stringify(obj);
  const rq=http.request(ORIGIN+path,{method:'POST',headers:{'Content-Type':'application/json','X-NS-Token':token,'Content-Length':Buffer.byteLength(d)}},r=>{let b='';r.on('data',c=>b+=c);r.on('end',()=>res(b))});
  rq.on('error',rej); rq.end(d)})}

// The agent: hold the SSE open, answer completion_request addressed to AGENT.
async function startAgent(token){
  return new Promise((resolve)=>{
    /* Named: the IDE asks /_ns/bus/agents whether the addressee is reachable
       here before entering the election, and an unnamed subscriber is a
       listener rather than an addressable agent. */
    const req=http.get(ORIGIN+'/_ns/bus?token='+encodeURIComponent(token)+'&name='+encodeURIComponent(AGENT),res=>{
      let buf='';
      res.on('data',chunk=>{ buf+=chunk;
        let i; while((i=buf.indexOf('\n\n'))>=0){
          const frame=buf.slice(0,i); buf=buf.slice(i+2);
          const line=frame.split('\n').find(l=>l.startsWith('data:'));
          if(!line) continue;
          let msg; try{ msg=JSON.parse(line.slice(5).trim()) }catch(e){ continue }
          if(msg.kind==='completion_request' && msg.to===AGENT){
            requests++; seenCorr.push(msg.corr_id);
            post('/_ns/bus',{to:msg.from,from:AGENT,kind:'completion_response',corr_id:msg.corr_id,
              response:{id:'msg_1',type:'message',role:'assistant',
                content:[{type:'text',text:REPLY}],stop_reason:'end_turn',
                usage:{input_tokens:1,output_tokens:1}}},token).catch(()=>{});
          }
        }
      });
      resolve(req);
    });
  });
}
/* One bus completion through BusProvider, which now goes via the host's
   coordinated performer: only the elected client reaches the bus at all. */
const DOIT = "[:g | [ | p msgs | p:: platform aiAccess BusProvider agentName: '"+AGENT+"' chat: '"+CHAT+"' port: ide aiSupport. "
  + "msgs:: platform collections List new. p addUserText: 'ping' toMessages: msgs. "
  + "(p complete: (p messagesAsRequestPayload: msgs) system: '' notices: platform collections List new tools: nil maxTokens: 16) "
  + "then: [:r | g at: 'reply' put: (p extractTextFromResponse: r). nil ] "
  + "onError: [:e | g at: 'reply' put: 'ERR ' , e printString. nil ] ] "
  + "on: Exception do: [:e | g at: 'reply' put: 'RAISED ' , e printString ]. 'GO'] value: platform js global";

async function main(){
  const cfg=JSON.parse(await get('/_ns/config'));
  if(!cfg.bus){ console.log('front door has no bus (start it with --bus)'); process.exitCode=1; return; }
  const token=JSON.parse(await get('/_ns/token')).token;
  const agent=await startAgent(token);
  console.log('agent "'+AGENT+'" listening; reply='+REPLY);
  await sleep(1500);

  const A=await launchBrowser({port:9811,tag:'bus-a',session:SESSION}); if(!await bootIDE(A,URL_C)){check('A boots',false,A.logs.slice(-4).join(' | '));return done([A],agent)}
  const B=await launchBrowser({port:9812,tag:'bus-b',session:SESSION}); if(!await bootIDE(B,URL_C)){check('B boots',false,B.logs.slice(-4).join(' | '));return done([A,B],agent)}
  await sleep(4000);

  console.log('\n--- one bus completion, two live clients ---');
  const ra=await evalDoIt(A,DOIT,'reply',60);
  check('A gets the agent reply', ra===REPLY, JSON.stringify(ra));
  let rb; for(let i=0;i<30;i++){ await sleep(1500); rb=await B.v('window.reply'); if(rb!==undefined)break; }
  check('B gets the SAME reply (shared, not its own)', rb===REPLY, JSON.stringify(rb));
  check('the agent saw EXACTLY ONE request', requests===1, 'requests='+requests+' corr='+JSON.stringify(seenCorr));

  console.log('\n--- late joiner ---');
  const C=await launchBrowser({port:9813,tag:'bus-c',session:SESSION});
  if(!await bootIDE(C,URL_C)){check('C boots',false,C.logs.slice(-4).join(' | '))}
  else{ await sleep(8000);
    check('replay did NOT re-issue the bus request', requests===1, 'requests='+requests);
    const orph=C.logs.filter(l=>l.includes('no subscriber'));
    check('joiner replay is orphan-free', orph.length===0, orph.slice(0,2).join(' | ')); }
  const errs=[A,B].map(b=>b.logs.filter(l=>l.startsWith('[error]')));
  console.log('  console errors A/B:', errs.map(e=>e.length).join('/'));
  errs.flat().slice(0,4).forEach(l=>console.log('    '+l.slice(0,240)));
  return done([A,B,C],agent);
}
function done(bs,agent){ bs.forEach(b=>{try{b.proc.kill()}catch(e){}}); try{agent.destroy()}catch(e){}
  summary(); }
main().catch(e=>{console.error(e);process.exit(1)});
