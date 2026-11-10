/* Does an outbound bus send happen ONCE per session, or once per client?

   The tool loop runs on every client - that is how a synchronized session
   re-derives state - so a tool whose effect LEAVES the image is delivered once
   per participant unless it is coordinated. This drives the real path: a mock
   provider answers the first completion with a tool_call for send_to_agent,
   the IDE runs the tool, and this probe - subscribed to /_ns/bus as the target
   agent - counts what actually arrives.

   Two clients. Expected: exactly ONE message.  Run: node outbound-once-probe.js */
const http=require('http');
const { sleep, launchBrowser, bootIDE, evalDoIt, makeChecker } =
  require('/Users/gbracha/newspeak/dev/web/newspeak/croquet-probes/harness');
const { check, summary } = makeChecker();
const ORIGIN='http://localhost:8080', AGENT='outboundprobe';
const MOCK_PORT=8095, MOCK='http://localhost:'+MOCK_PORT+'/v1';
const SESSION='outb'+Math.floor(Date.now()/1000), DOC='OutboundProbeChat';
const URL_C=ORIGIN+'/croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId='
  +SESSION+'&pwd=test&appId=org.newspeaklanguage.outb&apiKey=none&reflector=ws://localhost:9090&files=/files';
let posts=0, received=[];
function mock(){
  const cors=r=>{r.setHeader('Access-Control-Allow-Origin','*');
    r.setHeader('Access-Control-Allow-Methods','GET,POST,OPTIONS');
    r.setHeader('Access-Control-Allow-Headers','Content-Type,Authorization')};
  return http.createServer((req,res)=>{ cors(res);
    if(req.method==='OPTIONS'){res.writeHead(204);return res.end()}
    if(req.url.endsWith('/models')){res.writeHead(200,{'Content-Type':'application/json'});
      return res.end(JSON.stringify({object:'list',data:[{id:'mock-alpha',display_name:'Mock Alpha'}]}))}
    if(req.url.endsWith('/chat/completions')){
      const turn=++posts; let b=''; req.on('data',c=>b+=c);
      return req.on('end',()=>{ res.writeHead(200,{'Content-Type':'application/json'});
        if(turn===1){   // first turn: ask the IDE to use send_to_agent
          res.end(JSON.stringify({id:'c1',object:'chat.completion',choices:[{index:0,
            message:{role:'assistant',content:null,tool_calls:[{id:'call_1',type:'function',
              function:{name:'send_to_agent',arguments:JSON.stringify({agent_name:AGENT,message:'hello from the IDE'})}}]},
            finish_reason:'tool_calls'}],usage:{prompt_tokens:1,completion_tokens:1}}));
        } else {        // after the tool result: a plain answer
          res.end(JSON.stringify({id:'c2',object:'chat.completion',
            choices:[{index:0,message:{role:'assistant',content:'done'},finish_reason:'stop'}],
            usage:{prompt_tokens:1,completion_tokens:1}}));
        }});
    }
    res.writeHead(404);res.end('no')}).listen(MOCK_PORT);
}
function get(path){return new Promise((res,rej)=>{http.get(ORIGIN+path,r=>{let b='';r.on('data',c=>b+=c);r.on('end',()=>res(b))}).on('error',rej)})}
async function listen(token){   // the probe IS the target agent
  return new Promise(resolve=>{
    // Subscribed BY NAME: since bus locality a client posts only to an agent its
    // own front door lists (/_ns/bus/agents), and an anonymous stream is not listed.
    const req=http.get(ORIGIN+'/_ns/bus?token='+encodeURIComponent(token)+'&name='+encodeURIComponent(AGENT),res=>{
      let buf='';
      res.on('data',ch=>{ buf+=ch; let i;
        while((i=buf.indexOf('\n\n'))>=0){ const f=buf.slice(0,i); buf=buf.slice(i+2);
          const l=f.split('\n').find(x=>x.startsWith('data:')); if(!l) continue;
          let m; try{ m=JSON.parse(l.slice(5).trim()) }catch(e){ continue }
          if(m.to===AGENT && m.kind!=='completion_request') received.push(m);
        }});
      resolve(req);
    });
  });
}
const START = "[:g | [ | sub chat | sub:: ide aiSupport IDEChatSetupSubject onModel: platform aiAccess OpenAICompatibleProvider. "
  + "sub providerName: 'openai-compat'. sub baseUrl: '"+MOCK+"'. sub apiKey: 'x'. sub modelName: 'mock-alpha'. sub docName: '"+DOC+"'. "
  + "chat:: sub startChat. g at: 'started' put: (chat isNil ifTrue: ['NIL'] ifFalse: ['OK']) ] "
  + "on: Exception do: [:e | g at: 'started' put: 'ERR ' , e printString ]. 'GO'] value: platform js global";
const SEND = "[:g | [ | doc subj p | doc:: ide namespacing Root at: '"+DOC+"' ifAbsent: [nil]. "
  + "subj:: ide aiSupport chatSubjectFor: doc. p:: subj sendText: 'please contact the agent'. "
  + "p isNil ifTrue: [ g at: 'sent' put: 'NO PROMISE' ] ifFalse: [ "
  + "p then: [:r | subj markComplete. g at: 'sent' put: 'SENT'. nil ] "
  + "onError: [:e | g at: 'sent' put: 'REJ ' , e printString. nil ] ] ] "
  + "on: Exception do: [:e | g at: 'sent' put: 'ERR ' , e printString ]. 'GO'] value: platform js global";
(async()=>{
  const cfg=JSON.parse(await get('/_ns/config'));
  if(!cfg.bus){ console.log('front door has no bus (start it with --bus)'); process.exitCode=1; return }
  const token=JSON.parse(await get('/_ns/token')).token;
  const agent=await listen(token);
  const srv=mock(); await sleep(600);
  const A=await launchBrowser({port:9841,tag:'outb-a',session:SESSION});
  if(!await bootIDE(A,URL_C)){check('A boots',false,A.logs.slice(-4).join(' | '));return fin([A],srv,agent)}
  const B=await launchBrowser({port:9842,tag:'outb-b',session:SESSION});
  if(!await bootIDE(B,URL_C)){check('B boots',false,B.logs.slice(-4).join(' | '));return fin([A,B],srv,agent)}
  await sleep(4000);
  check('chat started', (await evalDoIt(A,START,'started',40))==='OK', JSON.stringify(await A.v('window.started')));
  await sleep(5000);
  const sent=await evalDoIt(A,SEND,'sent',60);
  console.log('  send result:', JSON.stringify(sent));
  await sleep(12000);
  console.log('  agent received:', JSON.stringify(received.map(m=>m.kind+' from '+m.from+': '+String(m.text).slice(0,40))));
  check('the tool actually fired (agent got the message)', received.length>=1, 'received='+received.length);
  check('the agent received it EXACTLY ONCE, not once per client', received.length===1, 'received='+received.length);
  fin([A,B],srv,agent);
})().catch(e=>{console.error(e);process.exit(1)});
function fin(bs,srv,agent){bs.forEach(b=>{try{b.proc.kill()}catch(e){}});
  try{srv.close()}catch(e){} try{agent.destroy()}catch(e){} summary()}
