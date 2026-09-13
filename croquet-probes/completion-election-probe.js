/* Does a model completion go out ONCE per session, via the elected initiator?

   A mock OpenAI-compatible endpoint counts POSTs to /v1/chat/completions
   ITSELF, so exactly-once is measured at the server rather than inferred from
   client-side fetch counters. Credential-free: OpenAICompatibleProvider needs
   no API key.

     A and B are live. A evaluates one completion; under Croquet the evaluate
     is a synchronized action, so both clients run it.
       - both clients get the SAME reply
       - the provider saw exactly ONE request
     A late joiner C then replays, and must still leave the count at one.

   Run: node completion-election-probe.js
*/
const { sleep, launchBrowser, click, waitFor, bootIDE, evalDoIt, makeChecker } = require('./harness');
const MOCK_PORT=8098, MOCK='http://localhost:'+MOCK_PORT+'/v1';
const REPLY='MOCK-REPLY-777';
const SESSION='cmpl'+Math.floor(Date.now()/1000);
const URL_C='http://localhost:8080/croquetpsoup.html?snapshot=CroquetHopscotchWebIDE-TEST.vfuel&sessionId='
  +SESSION+'&pwd=test&appId=org.newspeaklanguage.cmpl&apiKey=none&reflector=ws://localhost:9090&files=/files';
const http=require('http');
const { check, summary } = makeChecker();

let posts=0;
function mockServer(){
  const cors = res => { res.setHeader('Access-Control-Allow-Origin','*');
    res.setHeader('Access-Control-Allow-Methods','GET,POST,OPTIONS');
    res.setHeader('Access-Control-Allow-Headers','Content-Type,Authorization'); };
  return http.createServer((req,res)=>{
    cors(res);
    if(req.method==='OPTIONS'){ res.writeHead(204); return res.end(); }
    if(req.url.endsWith('/models')){
      res.writeHead(200,{'Content-Type':'application/json'});
      return res.end(JSON.stringify({object:'list',data:[{id:'mock-alpha',display_name:'Mock Alpha'}]}));
    }
    if(req.url.endsWith('/chat/completions') && req.method==='POST'){
      posts++;
      let b=''; req.on('data',c=>b+=c);
      return req.on('end',()=>{ res.writeHead(200,{'Content-Type':'application/json'});
        res.end(JSON.stringify({id:'cmpl-1',object:'chat.completion',
          choices:[{index:0,message:{role:'assistant',content:REPLY},finish_reason:'stop'}],
          usage:{prompt_tokens:1,completion_tokens:1}})); });
    }
    res.writeHead(404); res.end('no');
  }).listen(MOCK_PORT);
}
const DOIT = "[:g | [ | p msgs | p:: platform aiAccess OpenAICompatibleProvider apiKey: '' model: 'mock-alpha' baseUrl: '"+MOCK+"'. "
  + "msgs:: platform collections List new. p addUserText: 'hello' toMessages: msgs. "
  + "(p complete: (p messagesAsRequestPayload: msgs) system: '' tools: nil maxTokens: 16) "
  + "then: [:r | g at: 'reply' put: ((((r at: 'choices') at: 0) at: 'message') at: 'content'). nil ] "
  + "onError: [:e | g at: 'reply' put: 'ERR ' , e printString. nil ] ] "
  + "on: Exception do: [:e | g at: 'reply' put: 'RAISED ' , e printString ]. 'GO'] value: platform js global";

async function main(){
  const srv=mockServer(); await sleep(500);
  console.log('mock provider on '+MOCK+'   reply='+REPLY);
  const A=await launchBrowser({port:9801,tag:'cmpl-a',session:SESSION}); if(!await bootIDE(A,URL_C)){check('A boots',false,A.logs.slice(-4).join(' | '));return done([A],srv)}
  const B=await launchBrowser({port:9802,tag:'cmpl-b',session:SESSION}); if(!await bootIDE(B,URL_C)){check('B boots',false,B.logs.slice(-4).join(' | '));return done([A,B],srv)}
  await sleep(3000);
  console.log('\n--- one completion, two live clients ---');
  const ra=await evalDoIt(A,DOIT,'reply',40);
  check('A gets the completion', ra===REPLY, JSON.stringify(ra));
  let rb; for(let i=0;i<25;i++){ await sleep(1500); rb=await B.v('window.reply'); if(rb!==undefined)break; }
  check('B gets the SAME completion (shared, not its own)', rb===REPLY, JSON.stringify(rb));
  check('the provider saw EXACTLY ONE request', posts===1, 'POSTs='+posts);

  console.log('\n--- late joiner ---');
  const C=await launchBrowser({port:9803,tag:'cmpl-c',session:SESSION});
  if(!await bootIDE(C,URL_C)){check('C boots',false,C.logs.slice(-4).join(' | '))}
  else{
    await sleep(6000);
    check('replay did NOT re-issue the completion', posts===1, 'POSTs='+posts);
    const orph=C.logs.filter(l=>l.includes('no subscriber'));
    check('joiner replay is orphan-free', orph.length===0, orph.slice(0,2).join(' | '));
  }
  const errA=A.logs.filter(l=>l.startsWith('[error]')), errB=B.logs.filter(l=>l.startsWith('[error]'));
  console.log('  console errors A/B:', errA.length+'/'+errB.length);
  errA.concat(errB).slice(0,5).forEach(l=>console.log('    '+l.slice(0,300)));
  return done([A,B,C],srv);
}
function done(bs,srv){ bs.forEach(b=>{try{b.proc.kill()}catch(e){}}); try{srv.close()}catch(e){}
  summary(); }
main().catch(e=>{console.error(e);process.exit(1)});
