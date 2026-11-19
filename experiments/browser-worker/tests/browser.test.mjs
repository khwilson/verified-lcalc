import test from 'node:test';
import assert from 'node:assert/strict';
import {generateKeyPairSync,sign} from 'node:crypto';
import {canonical,requestLine,sha256,verifyManifest} from '../web/protocol.mjs';
import {mountVolunteer} from '../web/widget.mjs';
const {privateKey,publicKey}=generateKeyPairSync('ed25519');
const pem=publicKey.export({type:'spki',format:'pem'});
const manifest={schema:'lcalc.wasm-worker.v1',abi:'lcalc-worker-text-v1',files:{}};
const signed={manifest,signature:sign(null,Buffer.from(canonical(manifest)),privateKey).toString('base64')};

test('exact integer transport, canonical JSON, signatures and hashes',async()=>{
 assert.equal(requestLine({ainvs:['0','-1','1','-10','-20'],conductor:'11'}),'0\t-1\t1\t-10\t-20\t11\t53\t0\t1\t16');
 assert.throws(()=>requestLine({ainvs:['0','01','1','2','3'],conductor:'11'}));
 assert.equal(canonical({z:['1'],a:{x:true}}),'{"a":{"x":true},"z":["1"]}');
 assert.equal(await sha256(new TextEncoder().encode('abc')),'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad');
 assert.deepEqual(await verifyManifest(signed,pem),manifest);
 await assert.rejects(()=>verifyManifest({...signed,manifest:{...manifest,abi:'tampered'}},pem));
});
class Element{
 constructor(){this.textContent='';this.disabled=false;this.checked=false;this.listeners={};this.children=[];}
 addEventListener(name,fn){this.listeners[name]=fn;}
 append(x){this.children.push(x);}
 replaceChildren(){this.children=[];}
}
function dom(){
 const elements=Object.fromEntries(['output','[data-start]','[data-stop]','input'].map(x=>[x,new Element()]));
 const shadow={innerHTML:'',querySelector:s=>elements[s],replaceChildren:()=>{}};
 globalThis.location=new URL('http://localhost:8787');
 globalThis.document={createElement:()=>new Element()};
 globalThis.window={addEventListener(){},removeEventListener(){}};
 return {container:{attachShadow:()=>shadow},shadow,elements};
}
function transport(){
 const calls=[];globalThis.fetch=async(url,options={})=>{
  if(options.signal?.aborted)throw Error('aborted');
  const path=new URL(url).pathname;calls.push(path);
  let value;
  if(path==='/v1/worker')value=signed;
  else if(path==='/v1/jobs/claim')value={job_id:'a'.repeat(64),lease_token:'token',subject:{},label:'11.a1'};
  else if(path.endsWith('/release'))value={released:true};
  else if(path==='/v1/submissions')value={submission_id:'b'.repeat(48)};
  else if(path.includes('/v1/submissions/'))value={status:'accepted',certificate_id:'c'.repeat(64)};
  else throw Error('Unexpected path '+path);
  return {ok:true,json:async()=>value};
 };return calls;
}
class MockWorker{
 constructor(stall=false){this.stall=stall;this.terminated=false;}
 postMessage(data){
  if(data.type==='initialize')queueMicrotask(()=>this.onmessage({data:{type:'ready'}}));
  else if(!this.stall)queueMicrotask(()=>this.onmessage({data:{type:'result',result:{schema:'test-witness'}}}));
 }
 terminate(){this.terminated=true;}
}
test('widget stays idle until opt-in, labels never enter HTML, accepted receipt is displayed',async()=>{
 const {container,shadow,elements}=dom();const calls=transport();const widget=mountVolunteer(container,{api:location.origin,curve:'<img onerror=evil>',publicKey:pem,workerFactory:()=>new MockWorker()});
 assert.equal(calls.length,0);assert.ok(!shadow.innerHTML.includes('<img'));assert.ok(elements.output.textContent.includes('<img'));
 await widget.start();assert.ok(elements.output.textContent.includes('Certificate accepted'));assert.equal(elements.output.children.length,1);assert.ok(!elements['[data-start]'].disabled);widget.destroy();
});
test('stop rejects pending computation, releases lease and allows restart',async()=>{
 const {container,elements}=dom();const calls=transport();let worker;
 const widget=mountVolunteer(container,{api:location.origin,publicKey:pem,workerFactory:()=>worker=new MockWorker(true)});
 const run=widget.start();
 for(let i=0;i<100&&!calls.includes('/v1/jobs/claim');i++)await new Promise(r=>setTimeout(r,5));
 assert.ok(calls.includes('/v1/jobs/claim'));
 await widget.stop();await run;assert.ok(worker.terminated);assert.ok(!elements['[data-start]'].disabled);assert.ok(calls.some(p=>p.endsWith('/release')));
 widget.destroy();
});
