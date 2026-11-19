// Run by build_wasm.py before it publishes a browser manifest.
import {pathToFileURL} from 'node:url';
import {readFile} from 'node:fs/promises';
import {execFileSync} from 'node:child_process';
import assert from 'node:assert/strict';
const [loader,worker]=process.argv.slice(2);
const create=(await import(pathToFileURL(loader))).default;
const engine=await create({wasmBinary:new Uint8Array(await readFile(loader.replace(/\.mjs$/,'.wasm')))});
assert.equal(engine.ccall('lcalc_worker_init','number',[],[]),0);
const subjects=[['0','-1','1','-10','-20','11'],['0','0','1','-1','0','37'],['0','1','0','-40','84','112']];
for(const subject of subjects){
 const line=[...subject,'53','0','1','16'].join('\t');
 const native=JSON.parse(execFileSync(worker,['compute',line],{timeout:600000}));
 assert.notEqual(native.status,'inconclusive','Parity fixture must exercise a real certificate');
 const wasm=JSON.parse(engine.ccall('lcalc_worker_compute','string',['string'],[line]));
 assert.deepEqual(wasm,native);
 console.log(`Native/WASM exact certificate match for conductor ${subject[5]}`);
}
