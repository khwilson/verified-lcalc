import {verificationStatus} from './verification-status.mjs';
import {createGenerationQueue} from './generation-queue.mjs';
import {summarizeTasks} from './task-status.mjs';
const $=id=>document.getElementById(id);
const curveLabels=new Map();
const say=text=>{$('status').textContent=text;};
async function api(path,body,method){
 const headers={};if(body!==undefined)headers['Content-Type']='application/json';if($('token').value)headers.Authorization='Bearer '+$('token').value;
 const r=await fetch(path,{method:method||(body===undefined?'GET':'POST'),headers,body:body===undefined?undefined:JSON.stringify(body)});
 if(!r.ok){let text;try{text=JSON.stringify((await r.json()).detail);}catch{text=await r.text();}throw Error(text||r.statusText);}return r;
}
const json=async(path,body,method)=>(await api(path,body,method)).json();
function option(select,value,label){const o=document.createElement('option');o.value=value;o.textContent=label;select.append(o);}
function td(row,text){const cell=document.createElement('td');cell.textContent=text;row.append(cell);return cell;}
function selected(table){return [...$(table).querySelectorAll('input:checked')].map(e=>e.value);}
function checkbox(row,id){const c=document.createElement('input');c.type='checkbox';c.value=id;c.setAttribute('aria-label','Select '+id);const cell=td(row,'');cell.append(c);}
function guard(fn){return async event=>{event?.preventDefault();try{await fn();}catch(e){say(e.message);}};}
const params=()=>new URLSearchParams({source_id:$('source').value,environment_id:$('environment').value});
async function loadCurves(){
 if(!$('source').value){say('Import a source snapshot first.');return;}
 const q=new URLSearchParams({source_id:$('source').value});if($('conductor').value)q.set('conductor',$('conductor').value);
 const rows=await json('/v1/curves?'+q);$('curves').replaceChildren();$('all-curves').checked=false;
 for(const c of rows){curveLabels.set(c.id,c.label);const r=document.createElement('tr');checkbox(r,c.id);td(r,c.label);td(r,c.conductor);td(r,JSON.stringify(c.subject.ainvs));$('curves').append(r);}
 $('curve-caption').textContent=`Showing ${rows.length} curves (first page, up to 100). Use API pagination or CLI for larger selections.`;
}
let proofTimer;
let proofRequest = 0;
async function loadProofs(){
 clearTimeout(proofTimer);
 const request=++proofRequest;
 if(!$('source').value||!$('environment').value)return;
 const scope=params().toString();
 const rows=await json('/v1/proof-versions?'+scope);
 if(request!==proofRequest||scope!==params().toString())return;
 const chosen=new Set(selected('proofs'));
 $('proofs').replaceChildren();$('all-proofs').checked=false;
 for(const p of rows){const r=document.createElement('tr');checkbox(r,p.id);r.querySelector('input').checked=chosen.has(p.id);td(r,p.curve_id.slice(0,12));td(r,p.statement.analytic_rank);const status=td(r,verificationStatus(p).label);status.title=p.last_check?.error||'';td(r,p.last_accepted_check?.checked_at||'Never');const c=td(r,'');const a=document.createElement('a');a.href='/v1/proof-versions/'+p.id+'/source';a.textContent='View Lean source';c.append(a);const details=document.createElement('details');const summary=document.createElement('summary');summary.textContent='Import theorem';const code=document.createElement('pre');code.textContent=`import ${p.module}\n\n#check ${p.module}.analytic_rank`;details.append(summary,code);c.append(details);$('proofs').append(r);}
 $('all-proofs').checked=rows.length>0&&rows.every(p=>chosen.has(p.id));
 if(rows.some(p=>verificationStatus(p).active))proofTimer=setTimeout(()=>guard(async()=>{await loadProofs();await loadCampaigns();})(),2000);
}
let taskTimer;
let taskState = '';
async function loadTasks(){
 clearTimeout(taskTimer);
 if(!$('environment').value)return;
 const scope=params().toString();
 const rows=await json('/v1/tasks?'+scope);
 if(scope!==params().toString())return;
 $('tasks').replaceChildren();
 for(const t of rows){const r=document.createElement('tr');td(r,t.curve_id?.slice(0,12)||'');td(r,t.status);td(r,t.error||(t.status==='pending'?'Waiting for a worker with the matching installation':t.status==='running'?'Computing witness and unchecked Lean source':t.status==='succeeded'?'Unchecked candidate ready below':''));$('tasks').append(r);}
 const summary=summarizeTasks(rows);
 $('task-caption').textContent=summary.text;
 const state=JSON.stringify([scope,rows.map(t=>[t.id,t.status])]);
 if(state!==taskState){taskState=state;await loadProofs();}
 if(summary.active)taskTimer=setTimeout(()=>guard(loadTasks)(),2000);
}
window.addEventListener('pagehide',()=>{clearTimeout(taskTimer);clearTimeout(proofTimer);});
async function loadCampaigns(){
 const rows=await json('/v1/campaigns');$('campaigns').replaceChildren();
 for(const c of rows){const detail=await json('/v1/campaigns/'+c.id);const r=document.createElement('tr');td(r,c.name);td(r,c.created_at);const cell=td(r,`${detail.members.filter(m=>['succeeded','failed','inconclusive'].includes(m.status)).length}/${detail.members.length} finished `);if(detail.complete){const a=document.createElement('a');a.href='/v1/campaigns/'+c.id+'/report';a.textContent='Signed report (includes source comparisons)';cell.append(a);}$('campaigns').append(r);}
}
async function loadSchedules(){
 const rows=await json('/v1/schedules');$('schedules').replaceChildren();
 for(const s of rows){const r=document.createElement('tr');td(r,s.name);td(r,s.next_due);td(r,s.limit);td(r,s.enabled?'Enabled':'Paused');const button=document.createElement('button');button.textContent=s.enabled?'Pause':'Resume';button.onclick=guard(async()=>{await json('/v1/schedules/'+s.id,{enabled:!s.enabled},'PATCH');await loadSchedules();});td(r,'').append(button);$('schedules').append(r);}
}
async function refresh(){
 const oldSource=$('source').value,oldEnv=$('environment').value;
 const [sources,environments,stats]=await Promise.all([json('/v1/sources'),json('/v1/environments'),json('/v1/stats')]);
 $('source').replaceChildren();$('environment').replaceChildren();for(const s of sources)option($('source'),s.id,s.name+' · '+s.id.slice(0,8));for(const e of environments)option($('environment'),e.id,e.id.slice(0,12)+' · '+e.manifest.lean);
 if([...$('source').options].some(o=>o.value===oldSource))$('source').value=oldSource;if([...$('environment').options].some(o=>o.value===oldEnv))$('environment').value=oldEnv;
 await loadCurves();await loadProofs();await loadTasks();await loadCampaigns();await loadSchedules();say(`${stats.curve} curve inputs · ${stats.proof_version} proof candidates · ${stats.verification} verification attempts`);
}
$('refresh').onclick=guard(refresh);$('load').onclick=guard(loadCurves);$('proofs-refresh').onclick=guard(async()=>{await loadProofs();await loadTasks();await loadCampaigns();});
$('import').onsubmit=guard(async()=>{const f=$('source-file').files[0];if(!f)throw Error('Choose an input JSON file');if(f.size>1500000)throw Error('Use the CLI for files over 1.5 MiB');const raw=JSON.parse(await f.text());const inputs=Array.isArray(raw)?raw:(raw.inputs||raw.cases);await json('/v1/sources',{name:$('source-name').value,inputs,provenance:{filename:f.name}});await refresh();});
const generationQueue=createGenerationQueue({
 dialog:$('generation-queue'),body:$('queue-jobs'),summary:$('queue-summary'),
 progress:$('queue-progress'),generateButton:$('generate'),
 submit:body=>json('/v1/generate',body),getTask:id=>json('/v1/tasks/'+encodeURIComponent(id)),
 onUpdate:async()=>{await loadTasks();},onError:say,
});
$('generate').onclick=guard(()=>generationQueue.start(selected('curves'),$('environment').value,new Map(curveLabels)));
$('view-queue').onclick=()=>generationQueue.open();
$('close-queue').onclick=()=>$('generation-queue').close();
window.addEventListener('pagehide',()=>generationQueue.dispose());
$('check').onclick=guard(async()=>{const r=await json('/v1/campaigns',{name:'Browser selection '+new Date().toISOString(),proof_version_ids:selected('proofs'),source_id:$('source').value});say('Verification campaign queued: '+r.id);await loadProofs();await loadCampaigns();});
$('export').onclick=guard(async()=>{const response=await api('/v1/bundles',{proof_version_ids:selected('proofs')});const url=URL.createObjectURL(await response.blob());const a=document.createElement('a');a.href=url;a.download='lcalc-candidates.zip';a.click();setTimeout(()=>URL.revokeObjectURL(url),10000);say('Downloaded unchecked proof candidates. The bundle must be checked before use.');});
$('schedule').onsubmit=guard(async()=>{const r=await json('/v1/schedules',{name:'Periodic source check',source_id:$('source').value,environment_id:$('environment').value,interval_seconds:Number($('interval').value),limit:Number($('schedule-limit').value)});say('Schedule created: '+r.id);await loadSchedules();});
for(const [all,table] of [['all-curves','curves'],['all-proofs','proofs']])$(all).onchange=()=>{for(const c of $(table).querySelectorAll('input'))c.checked=$(all).checked;};
$('environment').onchange=guard(async()=>{await loadProofs();await loadTasks();});
$('source').onchange=guard(async()=>{await loadCurves();await loadProofs();await loadTasks();});
guard(refresh)();
