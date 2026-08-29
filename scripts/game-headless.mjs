#!/usr/bin/env node
import { spawn } from "node:child_process";
import { once } from "node:events";
import readline from "node:readline";

const edge = "C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe";
const port = Number(process.env.GAME_CDP_PORT || (9200 + (process.pid % 700)));
const url = process.env.GAME_URL || "http://127.0.0.1:4174/index.html?creative";
const profile = process.env.GAME_PROFILE || (process.cwd() + "\\work\\edge-profile");
const child = spawn(edge, ["--headless=new", "--disable-gpu", "--no-sandbox", `--remote-debugging-port=${port}`, "--user-data-dir=" + profile, "about:blank"], { stdio: "ignore", detached: true });
const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));
let page;
for (let i = 0; i < 50; i++) {
  try { page = await (await fetch(`http://127.0.0.1:${port}/json/new?${encodeURIComponent(url)}`, { method: "PUT" })).json(); break; }
  catch { await sleep(100); }
}
if (!page?.webSocketDebuggerUrl) throw new Error("Edge CDP did not start");
const socket = new WebSocket(page.webSocketDebuggerUrl);
await new Promise((resolve, reject) => { socket.onopen = resolve; socket.onerror = reject; });
let nextId = 1; const pending = new Map();
const dialogs = [];
let ready = false;
socket.onmessage = event => {
  const message = JSON.parse(event.data);
  if (message.method === "Page.javascriptDialogOpening") {
    dialogs.push({ type: message.params.type, message: message.params.message });
    void cdp("Page.handleJavaScriptDialog", { accept: true });
    return;
  }
  if (message.id && pending.has(message.id)) { pending.get(message.id)(message); pending.delete(message.id); }
};
function cdp(method, params = {}) { return new Promise(resolve => { const id = nextId++; pending.set(id, resolve); socket.send(JSON.stringify({ id, method, params })); }); }
async function evaluate(expression) { const result = await cdp("Runtime.evaluate", { expression, awaitPromise: true, returnByValue: true }); return result.result?.result?.value ?? result.result?.exceptionDetails; }
async function run(args, waitMs = 1200) {
  await sleep(waitMs);
  await cdp("Page.enable");
  const [verb, ...rest] = args;
  if (verb === "eval") return evaluate(rest.join(" "));
  if (verb === "click") return evaluate(`document.querySelector(${JSON.stringify(rest[0])})?.click(); true`);
  if (verb === "key") return evaluate(`document.dispatchEvent(new KeyboardEvent('keydown',{key:${JSON.stringify(rest[0])},bubbles:true})); true`);
  if (verb === "hold") return evaluate(`(async()=>{const key=${JSON.stringify(rest[0])},ms=Number(${JSON.stringify(rest[1]??'100')})||100;document.dispatchEvent(new KeyboardEvent('keydown',{code:key.startsWith('Key')?key:'Key'+key.toUpperCase(),key,bubbles:true}));await new Promise(r=>setTimeout(r,ms));document.dispatchEvent(new KeyboardEvent('keyup',{code:key.startsWith('Key')?key:'Key'+key.toUpperCase(),key,bubbles:true}));return {key,ms};})()`);
  if (verb === "drag") {
    const dx = Number(rest[0]), dy = Number(rest[1]), ms = Number(rest[2] ?? 300);
    if (![dx, dy, ms].every(Number.isFinite)) throw new Error("drag expects dx dy [ms]");
    const metrics = await evaluate(`(()=>{const c=document.querySelector('canvas'),r=c.getBoundingClientRect();return{x:r.left+r.width/2,y:r.top+r.height/2,w:r.width,h:r.height};})()`);
    const steps = Math.max(2, Math.ceil(ms / 16));
    await cdp("Input.dispatchMouseEvent", { type: "mousePressed", x: metrics.x, y: metrics.y, button: "left", buttons: 1, clickCount: 1 });
    for (let i = 1; i <= steps; i++) {
      await cdp("Input.dispatchMouseEvent", { type: "mouseMoved", x: metrics.x + dx * i / steps, y: metrics.y + dy * i / steps, button: "left", buttons: 1 });
      await sleep(ms / steps);
    }
    await cdp("Input.dispatchMouseEvent", { type: "mouseReleased", x: metrics.x + dx, y: metrics.y + dy, button: "left", buttons: 0, clickCount: 1 });
    return evaluate(`(()=>({tile:globalThis.deductriumGame.hyperGui.world.currentTile,cam:globalThis.deductriumGame.hyperGui.world.localCamMat}))()`);
  }
  if (verb === "rotate") {
    const angle = Number(rest[0]);
    if (!Number.isFinite(angle)) throw new Error("rotate expects radians");
    const canvas = await evaluate(`(()=>{const c=document.querySelector('canvas'),r=c.getBoundingClientRect(),size=Math.min(r.width,r.height);return{x:r.left+r.width/2,y:r.top+r.height/2,radius:size*.498};})()`);
    await cdp("Input.dispatchMouseEvent", { type: "mousePressed", x: canvas.x + canvas.radius, y: canvas.y, button: "left", buttons: 1, clickCount: 1 });
    for (let i = 1; i <= 12; i++) {
      const step = angle * i / 12;
      await cdp("Input.dispatchMouseEvent", { type: "mouseMoved", x: canvas.x + canvas.radius * Math.cos(step), y: canvas.y + canvas.radius * Math.sin(step), button: "left", buttons: 1 });
      await sleep(10);
    }
    await cdp("Input.dispatchMouseEvent", { type: "mouseReleased", x: canvas.x + canvas.radius * Math.cos(angle), y: canvas.y + canvas.radius * Math.sin(angle), button: "left", buttons: 0, clickCount: 1 });
    return evaluate(`(()=>({tile:globalThis.deductriumGame.hyperGui.world.currentTile,cam:globalThis.deductriumGame.hyperGui.world.localCamMat}))()`);
  }
  if (verb === "move") {
    const place = rest.join(" ").trim();
    if (!place) throw new Error("move expects a tile name or hash");
    const target = await evaluate(`(async()=>{const {nameMap}=await import('/js/hy/maploader.js');const target=nameMap.get(${JSON.stringify(place)})??${JSON.stringify(place)};if(!/^(?:|[0-9]+(?:,[0-9]+)*)$/.test(target))throw new Error('unknown place: '+${JSON.stringify(place)});return target;})()`);
    const canvas = await evaluate(`(()=>{const c=document.querySelector('canvas'),r=c.getBoundingClientRect(),size=Math.min(r.width,r.height);return{x:r.left+r.width/2,y:r.top+r.height/2,radius:size*.498};})()`);
    const visited = [], blocked = [];
    for (let step = 0; step < 1000; step++) {
      const route = await evaluate(`(async()=>{const g=globalThis.deductriumGame,w=g.hyperGui.world,{blockMap}=await import('/js/hy/maploader.js'),target=${JSON.stringify(target)},excluded=new Set(${JSON.stringify(blocked.map(item => item.tile))}),start=w.currentTile.join(',');if(start===target)return[];const q=[w.currentTile.slice()],prev=new Map([[start,null]]);while(q.length&&prev.size<10000){const t=q.shift(),h=t.join(',');if(h===target)break;for(let d=0;d<w.atlasTile.p;d++){const[n]=w.atlasTile.getNeighborAndDir(t,d,true),nh=n.join(','),b=blockMap.get(nh);if(prev.has(nh)||!b||b.type===1||(excluded.has(nh)&&nh!==target))continue;prev.set(nh,h);q.push(n);}}if(!prev.has(target))return null;const path=[];for(let h=target;h!==start;h=prev.get(h))path.push(h);return path.reverse();})()`);
      if (route === null) return { ok: false, target, visited, blocked, error: "no unblocked mapped route" };
      if (!route.length) return { ok: true, target, visited, blocked };
      const nextHash = route[0];
      const facing = await evaluate(`(async()=>{const g=globalThis.deductriumGame,w=g.hyperGui.world,current=w.currentTile.join(','),target=${JSON.stringify(nextHash)};if(current===target)return{reached:true,current};const r=w.atlasTile.rotors.get(target);if(!r)return{reached:false,current,error:'target is not adjacent'};return{reached:false,current};})()`);
      if (facing.error) throw new Error(`${facing.error}: ${facing.current} -> ${nextHash}`);
      let reached = facing.reached === true;
      let deviated = null;
      if (!reached) {
        for (let push = 0; push < 40; push++) {
          const vector = await evaluate(`(async()=>{const w=globalThis.deductriumGame.hyperGui.world,{Hvec}=await import('/js/hy/algebra.js'),r=w.atlasTile.rotors.get(${JSON.stringify(nextHash)}),p=w.localCamMat.mul(r).apply(new Hvec()),length=Math.hypot(p.x,p.y)||1;return{dx:-p.x/length*90,dy:-p.y/length*90};})()`);
          await cdp("Input.dispatchMouseEvent", { type: "mouseMoved", x: canvas.x, y: canvas.y, button: "none", buttons: 0 });
          await cdp("Input.dispatchMouseEvent", { type: "mousePressed", x: canvas.x, y: canvas.y, button: "left", buttons: 1, clickCount: 1 });
          for (let i = 1; i <= 6; i++) {
            await cdp("Input.dispatchMouseEvent", { type: "mouseMoved", x: canvas.x + vector.dx * i / 6, y: canvas.y + vector.dy * i / 6, button: "left", buttons: 1 });
            await sleep(10);
          }
          await cdp("Input.dispatchMouseEvent", { type: "mouseReleased", x: canvas.x + vector.dx, y: canvas.y + vector.dy, button: "left", buttons: 0, clickCount: 1 });
          await sleep(20);
          const current = await evaluate(`globalThis.deductriumGame.hyperGui.world.currentTile.join(',')`);
          if (current === nextHash) { reached = true; break; }
          if (current !== facing.current) { deviated = current; break; }
        }
      }
      if (deviated) { visited.push(deviated); continue; }
      if (!reached) {
        const state = await evaluate(`(()=>{const g=globalThis.deductriumGame,w=g.hyperGui.world,b=w.getBlock(${JSON.stringify(nextHash)});return{current:w.currentTile.join(','),blocked:${JSON.stringify(nextHash)},name:b?.name??null,text:b?.text??'',type:b?.type??null};})()`);
        blocked.push({ tile: state.blocked, name: state.name, text: state.text, type: state.type });
        if (nextHash === target) return { ok: false, target, visited, blocked, ...state };
        continue;
      }
      visited.push(nextHash);
    }
    return { ok: false, target, visited, blocked, error: "movement step limit exceeded" };
  }
  if (verb === "nearby" || verb === "doors") return evaluate(`(()=>{const g=globalThis.deductriumGame,w=g.hyperGui.world,t=w.currentTile; const a=Array.from({length:w.atlasTile.p},(_,d)=>{const [n]=w.atlasTile.getNeighborAndDir(t,d,true),b=w.getBlock(n.join(',')); return {direction:d,tile:n.join(','),name:b?.name??null,type:b?.type??null,text:b?.text??''};}); return ${verb === "doors" ? "a.filter(x=>x.type===2||x.type===4)" : "a"};})()`);
  if (verb === "fs") return evaluate(`(()=>{const g=globalThis.deductriumGame,c=g.fsGui.cmd;c.gui.actionInput.value=${JSON.stringify(rest.join(" "))}; c.actionInputKeydown({key:'Enter'}); return {buffer:c.cmdBuffer.slice(),hint:g.fsGui.hintText.innerText};})()`);
  if (verb === "ui-fs") return evaluate(`(async()=>{const input=document.getElementById('action-input'),commands=${JSON.stringify(rest.join(' ').split(';').map(x=>x.trim()).filter(Boolean))};for(const command of commands){input.value=command;input.dispatchEvent(new KeyboardEvent('keydown',{key:'Enter',bubbles:true}));await new Promise(r=>setTimeout(r,40));}const g=globalThis.deductriumGame;return {commands,buffer:g.fsGui.cmd.cmdBuffer.slice(),hint:g.fsGui.hintText.innerText,propositions:g.fsGui.formalSystem.propositions.map(p=>g.fsGui.cmd.astparser.stringifyTight(p.value))};})()`);
  if (verb === "ui-deduct") return evaluate(`(async()=>{const rule=${JSON.stringify(rest[0])},indices=${JSON.stringify((rest[1]??'').split(',').map(x=>Number(x.trim())).filter(Number.isInteger))};const button=[...document.querySelectorAll('.cmd-btns button')].find(b=>b.innerText.trim()===rule);const idx=[...document.querySelectorAll('#deduct-list .idx')].find(b=>b.innerText.trim()===rule);const target=button??idx?.nextElementSibling;if(!target)throw new Error('rule button not found: '+rule);target.click();await new Promise(r=>setTimeout(r,30));for(const index of indices){const idxEl=document.querySelector('#prop-list .idx:nth-child('+((index+1)*8-7)+')');const el=idxEl?.nextElementSibling;if(!el)throw new Error('proposition row not found: p'+index);el.click();await new Promise(r=>setTimeout(r,40));}const g=globalThis.deductriumGame;return {rule,indices,buffer:g.fsGui.cmd.cmdBuffer.slice(),hint:g.fsGui.hintText.innerText,propositions:g.fsGui.formalSystem.propositions.map(p=>g.fsGui.cmd.astparser.stringifyTight(p.value))};})()`);
  if (verb === "fs-buffer") return evaluate(`(()=>{const g=globalThis.deductriumGame,c=g.fsGui.cmd;c.cmdBuffer=${JSON.stringify(rest.join(" ").split(",").map(x=>x.trim()).filter(Boolean))}; c.execCmdBuffer(); return {buffer:c.cmdBuffer.slice(),hint:g.fsGui.hintText.innerText,propositions:g.fsGui.formalSystem.propositions.length};})()`);
  if (verb === "fs-hyp") return evaluate(`(()=>{const g=globalThis.deductriumGame,p=g.fsGui.cmd.astparser.parse(${JSON.stringify(rest.join(" "))});g.fsGui.formalSystem.addHypothese(p);g.fsGui.updatePropositionList(true);return {propositions:g.fsGui.formalSystem.propositions.length};})()`);
  if (verb === "fs-macro") return evaluate(`(()=>{const g=globalThis.deductriumGame,name=${JSON.stringify(rest[0])},after=${JSON.stringify(rest[1])};if(!name)throw new Error('fs-macro expects a name');g.fsGui.formalSystem.addMacro(name,'录制*');g.fsGui.addToDeductions(name,after);g.fsGui.onStateChange();const d=g.fsGui.formalSystem.deductions[name];return {name,value:g.fsGui.cmd.astparser.stringifyTight(d?.conclusion??d?.value),from:d?.from,steps:d?.steps?.length??0};})()`);
  if (verb === "fs-assist") return evaluate(`(()=>{const g=globalThis.deductriumGame; const target=${JSON.stringify(rest.shift())}; const commands=${JSON.stringify(rest.join(' ').split(';').map(x=>x.trim()).filter(Boolean))}; const s=g.fsGui.startInferenceProofAssistant(target); if(!s) return {ok:false,error:g.fsGui.hintText.innerText}; const history=[]; for(const command of commands){const r=g.fsGui.applyInferenceProofCommand(command); history.push({command,complete:r?.complete??false,error:document.getElementById('fs-proof-errmsg')?.innerText??''});} const q=g.fsGui.finishInferenceProof(); return {ok:!!q,history,propositions:g.fsGui.formalSystem.propositions.length};})()`);
  if (verb === "fs-auto") return evaluate(`(async()=>{const g=globalThis.deductriumGame;if(!g.fsGui.metarules.includes('cpt'))return {ok:false,error:'完备性元定理 cpt 未解锁，不能使用 tauto'}; const {InferenceProofAssistant}=await import('/js/fs/proof-assistant.js'); const fs=g.fsGui.formalSystem; const target=${JSON.stringify(rest.join(' '))}; const a=new InferenceProofAssistant(fs,target,{ruleNames:g.fsGui.deductions,fastMetaRules:fs.fastmetarules,allowMcpt:true}); a.apply('tauto'); const q=a.qed(); const page=g.fsGui.pageStore.active; page.propositions.push(...q.propositions); fs.propositions=page.propositions; g.fsGui.updatePropositionList(true); g.fsGui.onStateChange(); return {ok:true,target,propositions:fs.propositions.length};})()`);
  if (verb === "fs-auto-all") return evaluate(`(async()=>{const g=globalThis.deductriumGame;if(!g.fsGui.metarules.includes('cpt'))return {ok:false,error:'完备性元定理 cpt 未解锁，不能使用 tauto'}; const {InferenceProofAssistant}=await import('/js/fs/proof-assistant.js'); const {blockMap}=await import('/js/hy/maploader.js'); const fs=g.fsGui.formalSystem,page=g.fsGui.pageStore.active,done=[],failed=[]; for(const [tile,b] of blockMap){if((b.type!==2&&b.type!==4)||!(b.text.endsWith('#p')||b.text.endsWith('#d')))continue; const target=b.text.replace(/#(?:p|d)$/,'').replaceAll('\\n','').trim(); try{const a=new InferenceProofAssistant(fs,target,{ruleNames:g.fsGui.deductions,fastMetaRules:fs.fastmetarules,allowMcpt:true});a.apply('tauto');const q=a.qed();page.propositions.push(...q.propositions);done.push({tile,target});}catch(error){failed.push({tile,target,error:String(error)});} } fs.propositions=page.propositions;g.fsGui.updatePropositionList(true);g.fsGui.onStateChange();return {done:done.length,failed:failed.length,failedSample:failed.slice(0,10),propositions:fs.propositions.length};})()`);
  if (verb === "reset-save") return evaluate(`(()=>{localStorage.removeItem('deductrium-save'); location.reload(); return {ok:true};})()`);
  if (verb === "walk-reachable") return evaluate(`(async()=>{const g=globalThis.deductriumGame,w=g.hyperGui.world,{blockMap}=await import('/js/hy/maploader.js'); const seen=new Set(['']),queue=[[]],blocked=[]; let passed=0; while(queue.length){const t=queue.shift(),h=t.join(','); if(seen.size>5000)break; for(let d=0;d<w.atlasTile.p;d++){const[n]=w.atlasTile.getNeighborAndDir(t,d,true),nh=n.join(','); if(seen.has(nh)||!blockMap.has(nh))continue; const b=w.getBlock(nh); if(!b||b.type===1){seen.add(nh);continue;} const ok=w.hitTest(n); if(!ok){if(b.type===2||b.type===4)blocked.push({tile:nh,name:b.name,text:b.text}); continue;} passed++; seen.add(nh); queue.push(n); w.currentTile=n; w.atlasTile.generateRotors(n); }} return {visited:seen.size,passed,blocked:blocked.slice(0,50),blockedCount:blocked.length,currentTile:w.currentTile,rewards:g.rewards};})()`);
  if (verb === "tt-assist") return evaluate(`(async()=>{const g=globalThis.deductriumGame; const target=${JSON.stringify(rest.shift())}; await g.ttGui.executeTactic(target); return {ok:true,body:document.body.innerText.slice(-500)};})()`);
  if (verb === "fs-sort") return evaluate(`(()=>{const g=globalThis.deductriumGame; g.fsGui.addToDeductions(${JSON.stringify(rest[0])},${JSON.stringify(rest[1])}); return g.fsGui.deductions.slice();})()`);
  if (verb === "tt-new-theorem") return evaluate(`(()=>{document.querySelector('#type-btn')?.click(); document.querySelector('#tt-add-theorem')?.click(); return true;})()`);
  if (verb === "tt-new-folder") return evaluate(`(()=>{const g=globalThis.deductriumGame; g.ttGui.addTheoremFolder(${JSON.stringify(rest.join(' '))}); return true;})()`);
  if (verb === "tt-sort") return evaluate(`(()=>{const g=globalThis.deductriumGame; g.ttGui.moveTheoremItem(${JSON.stringify(rest[0])},${JSON.stringify(rest[1])}); return g.ttGui.theoremItems?.map(x=>({kind:x.kind,id:x.id,value:x.input?.value??x.title?.innerText??''}));})()`);
  if (verb === "fs-list") return evaluate(`(()=>{const g=globalThis.deductriumGame; return {rules:g.fsGui.deductions.slice(),folders:g.fsGui.deductions.filter(x=>x.startsWith('< f >'))};})()`);
  if (verb === "tt-list") return evaluate(`(()=>{const g=globalThis.deductriumGame; return g.ttGui.theoremItems?.map(x=>({kind:x.kind,id:x.id,name:x.input?.value??x.title?.innerText??''}))??[];})()`);
  if (verb === "status") return evaluate(`({title:document.title,loading:document.getElementById('loading')?.className,canvas:!!document.querySelector('canvas'),text:document.body.innerText.slice(0,500),dialogs:${JSON.stringify(dialogs)} })`);
  throw new Error("usage: status | eval <javascript> | click <css> | key <key>");
}
const args = process.argv.slice(2);
try {
  if (args.length) {
    console.log(JSON.stringify(await run(args), null, 2));
  } else {
    console.log("Deductrium headless browser REPL");
    console.log("Commands: status | nearby | doors | move <place> | fs <cmd> | ui-fs <cmd;cmd;...> | ui-deduct <rule> <pN,pM> | hold <key> [ms] | drag <dx> <dy> [ms] | rotate <radians> | fs-buffer <a,b,c> | fs-hyp <ast> | fs-macro <name> [after] | fs-assist <target> <cmds> | fs-auto <target> | fs-auto-all | reset-save | walk-reachable | fs-sort <rule> [after] | tt-assist <target> | tt-new-theorem | tt-new-folder <name> | tt-sort <srcId> <dstId> | eval <javascript> | click <css> | key <key> | quit");
    const rl = readline.createInterface({ input: process.stdin, output: process.stdout, prompt: "browser> " });
    rl.prompt();
    for await (const line of rl) {
      const value = line.trim();
      if (!value) { if (!rl.closed) rl.prompt(); continue; }
      if (value === "quit" || value === "exit") { rl.close(); break; }
      try { console.log(JSON.stringify(await run(value.split(/\s+/), ready ? 0 : 1200), null, 2)); ready = true; }
      catch (error) { console.error(`error: ${error.message}`); }
      if (!rl.closed) rl.prompt();
    }
  }
} finally { socket.close(); child.kill(); }
