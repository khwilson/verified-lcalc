import {verifyManifest} from './protocol.mjs';
const delay=ms=>new Promise(resolve=>setTimeout(resolve,ms));
export function mountVolunteer(container,{api,curve=null,publicKey=null,workerURL=new URL('./compute-worker.mjs',import.meta.url),workerFactory=null}={}) {
  api=new URL(api,location.href).href.replace(/\/$/,'');
  const clientId=crypto.randomUUID();let active=false,worker=null,job=null,renewal=null,accepted=0,stopped=false,controller=null,cancelWait=null,workerBlob=null;
  const shadow=container.attachShadow({mode:'open'});
  shadow.innerHTML=`<style>:host{display:block;font:15px system-ui;max-width:38rem}section{border:1px solid #c9ced4;border-radius:8px;padding:18px;background:#fafbfc;color:#17212d}h3{font-size:17px;margin:0 0 8px}p{line-height:1.5;margin:8px 0}button{font:inherit;padding:8px 13px;border-radius:5px;border:1px solid #9ba7b4;background:white;cursor:pointer}button.primary{background:#245581;color:white;border-color:#245581}button:disabled{opacity:.5;cursor:default}label{display:block;margin:12px 0}output{display:block;line-height:1.5;margin:12px 0}small{color:#4c5969}a{color:#174f86}</style><section><h3>Help certify an elliptic curve</h3><p>Your browser can compute a candidate Lean certificate. The service checks it before publishing a proof.</p><label><input type="checkbox"> Keep contributing while this window is open</label><button class="primary" data-start>Compute a certificate</button> <button data-stop disabled>Stop</button><output role="status" aria-live="polite">Ready.</output><small>Analytic certificates currently use an explicit modularity assumption. You can stop at any time.</small></section>`;
  const output=shadow.querySelector('output'),start=shadow.querySelector('[data-start]'),stop=shadow.querySelector('[data-stop]'),continuous=shadow.querySelector('input');
  // A label is text, never executable markup.
  output.textContent=curve?`Ready for ${curve}.`:'Ready.';
  async function request(path,body,signal=controller?.signal) {
    const response=await fetch(api+path,{method:body===undefined?'GET':'POST',credentials:'omit',signal,headers:body===undefined?{}:{'Content-Type':'application/json'},body:body===undefined?undefined:JSON.stringify(body)});
    const value=await response.json();if(!response.ok)throw Error(value.error||'Service request failed');return value;
  }
  function waitMessage(expected,payload) {
    return new Promise((resolve,reject)=>{
      cancelWait=()=>reject(Error('Stopped'));
      worker.onmessage=({data})=>{if(data.type==='error'){cancelWait=null;reject(Error(data.message));}else if(data.type===expected){cancelWait=null;resolve(data);}};
      worker.onerror=()=>reject(Error('This browser could not run the Lean worker. A browser with WebAssembly Memory64 support is required.'));
      worker.postMessage(payload);
    });
  }
  async function initialize() {
    output.textContent='Loading the Lean computation worker…';
    if(!publicKey) {
      if(!['127.0.0.1','localhost'].includes(new URL(api).hostname))throw Error('Configure the pinned service public key before contributing.');
      const response=await fetch(api+'/v1/public-key',{credentials:'omit',signal:controller.signal});publicKey=await response.text();
    }
    const manifest=await verifyManifest(await request('/v1/worker'),publicKey);
    if(workerFactory)worker=workerFactory();
    else {
      const url=new URL(workerURL,location.href);
      if(url.origin===location.origin)worker=new Worker(url,{type:'module'});
      else {workerBlob=URL.createObjectURL(new Blob([`import ${JSON.stringify(url.href)};`],{type:'text/javascript'}));worker=new Worker(workerBlob,{type:'module'});}
    }
    await waitMessage('ready',{type:'initialize',manifest,base:api});
    if(workerBlob){URL.revokeObjectURL(workerBlob);workerBlob=null;}
  }
  async function release(inconclusive=false) {
    clearInterval(renewal);renewal=null;
    if(job){const current=job;job=null;try{await request(`/v1/jobs/${current.job_id}/release`,{lease_token:current.lease_token,inconclusive},null);}catch{/* Expired or already submitted. */}}
  }
  async function run() {
    if(active)return;active=true;stopped=false;controller=new AbortController();start.disabled=true;stop.disabled=false;
    try {
      await initialize();
      do {
        if(stopped)break;
        job=await request('/v1/jobs/claim',{client_id:clientId,...(curve?{label:curve}:{})});
        if(!job){output.textContent=curve?'No queued work for this curve.':'No queued work is currently available.';break;}
        const current=job;output.textContent=`Computing ${job.label||'an elliptic curve'}…`;
        renewal=setInterval(()=>request(`/v1/jobs/${current.job_id}/renew`,{lease_token:current.lease_token}).catch(()=>{}),45000);
        const {result}=await waitMessage('result',{type:'compute',subject:job.subject});
        if(stopped)break;
        if(result.status==='inconclusive'){output.textContent='This curve needs more arithmetic or numerical work.';await release(true);}
        else {
          output.textContent='Submitting the candidate for kernel validation…';
          const receipt=await request('/v1/submissions',{job_id:job.job_id,lease_token:job.lease_token,certificate:result});
          clearInterval(renewal);renewal=null;job=null;
          let status;
          do {await delay(2000);if(stopped)break;status=await request('/v1/submissions/'+receipt.submission_id);}while(['pending','validating'].includes(status.status));
          if(stopped)break;
          if(status.status!=='accepted')throw Error(status.error||'The candidate did not pass validation.');
          accepted++;output.textContent=`Certificate accepted. ${accepted} contribution${accepted===1?'':'s'} accepted this session. `;
          const link=document.createElement('a');link.href=api+'/v1/certificates/'+status.certificate_id;link.textContent='View proof manifest';link.target='_blank';link.rel='noopener';output.append(link);
        }
      } while(continuous.checked&&!curve&&!stopped);
    } catch(error){if(!stopped)output.textContent=String(error.message||error);}
    finally{await release();worker?.terminate();worker=null;if(workerBlob){URL.revokeObjectURL(workerBlob);workerBlob=null;}cancelWait=null;controller=null;active=false;start.disabled=false;stop.disabled=true;}
  }
  async function halt(){stopped=true;controller?.abort();cancelWait?.();worker?.terminate();await release();output.textContent='Stopped. You can contribute again whenever you choose.';}
  start.addEventListener('click',run);stop.addEventListener('click',halt);
  const close=()=>{stopped=true;controller?.abort();cancelWait?.();worker?.terminate();clearInterval(renewal);};window.addEventListener('pagehide',close,{once:true});
  return {start:run,stop:halt,destroy:()=>{close();window.removeEventListener('pagehide',close);shadow.replaceChildren();}};
}
