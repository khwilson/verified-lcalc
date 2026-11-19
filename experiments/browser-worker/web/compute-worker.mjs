import {requestLine,sha256} from './protocol.mjs';
let engine;
async function checkedFile(base,file) {
  const url=new URL(file.path,base);
  if(url.origin!==new URL(base).origin)throw Error('Worker asset origin mismatch');
  const response=await fetch(url,{credentials:'omit'});if(!response.ok)throw Error('Worker download failed');
  const bytes=await response.arrayBuffer();if(bytes.byteLength!==file.size||await sha256(bytes)!==file.sha256)throw Error('Worker asset hash mismatch');
  return bytes;
}
self.onmessage=async({data})=>{
  try {
    if(data.type==='initialize') {
      const manifest=data.manifest;
      if(manifest.schema!=='lcalc.wasm-worker.v1'||manifest.abi!=='lcalc-worker-text-v1')throw Error('Unsupported worker version');
      const loader=await checkedFile(data.base,manifest.files.loader);
      const wasm=await checkedFile(data.base,manifest.files.wasm);
      const blob=URL.createObjectURL(new Blob([loader],{type:'text/javascript'}));
      try {
        const create=(await import(blob)).default;
        engine=await create({wasmBinary:new Uint8Array(wasm),printErr:()=>{}});
        if(engine.ccall('lcalc_worker_init','number',[],[])!==0)throw Error('Lean runtime initialization failed');
      } finally {URL.revokeObjectURL(blob);}
      self.postMessage({type:'ready'});
    } else if(data.type==='compute') {
      if(!engine)throw Error('Worker is not initialized');
      const result=JSON.parse(engine.ccall('lcalc_worker_compute','string',['string'],[requestLine(data.subject)]));
      self.postMessage({type:'result',result});
    }
  } catch(error) {self.postMessage({type:'error',message:String(error.message||error)});}
};
