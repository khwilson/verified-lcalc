export const canonical = value => {
  if (value === null || typeof value !== 'object') return JSON.stringify(value);
  if (Array.isArray(value)) return '['+value.map(canonical).join(',')+']';
  return '{'+Object.keys(value).sort().map(k=>JSON.stringify(k)+':'+canonical(value[k])).join(',')+'}';
};
export const hex = bytes => Array.from(new Uint8Array(bytes),b=>b.toString(16).padStart(2,'0')).join('');
export async function sha256(bytes) { return hex(await crypto.subtle.digest('SHA-256',bytes)); }
export function requestLine(subject) {
  if(!subject || !Array.isArray(subject.ainvs) || subject.ainvs.length!==5) throw Error('Invalid curve input');
  for(const n of [...subject.ainvs,subject.conductor]) if(typeof n!=='string'||! /^(0|-[1-9][0-9]*|[1-9][0-9]*)$/.test(n)) throw Error('Expected exact decimal strings');
  return [...subject.ainvs,subject.conductor,'53','0','1','16'].join('\t');
}
export async function verifyManifest(reply,pem) {
  const der=Uint8Array.from(atob(pem.replace(/-----[^-]+-----|\s/g,'')),c=>c.charCodeAt(0));
  const key=await crypto.subtle.importKey('spki',der,{name:'Ed25519'},false,['verify']);
  const signature=Uint8Array.from(atob(reply.signature),c=>c.charCodeAt(0));
  if(!await crypto.subtle.verify('Ed25519',key,signature,new TextEncoder().encode(canonical(reply.manifest))))throw Error('Worker manifest signature is invalid');
  return reply.manifest;
}
