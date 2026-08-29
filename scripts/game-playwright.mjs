#!/usr/bin/env node
import readline from "node:readline";
import { mkdir, rename, writeFile } from "node:fs/promises";
import { chromium } from "file:///C:/Users/Hydrogenated233/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright/index.mjs";

const edge = "C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe";
const profile = process.env.GAME_PROFILE || `${process.cwd()}\\work\\playwright-profile`;
const url = process.env.GAME_URL || "http://127.0.0.1:4174/index.html";
const dialogs = [];
const activity = [];
const progressDir = `${process.cwd()}\\game-progress`;
const progressJson = `${progressDir}\\game-progress.json`;
const progressFrameJson = `${progressDir}\\game-progress-frame.json`;
const progressMirrorJson = `${progressDir}\\game-progress-mirror.json`;
const progressSaveJson = `${progressDir}\\game-progress-save.json`;
let progressFrameId = 0;
let progressMirrorId = 0;
let progressFrameCapture = null;
const atomicWriteQueues = new Map();
await mkdir(progressDir, { recursive: true });
const context = await chromium.launchPersistentContext(profile, {
  executablePath: edge,
  headless: true,
  viewport: { width: 1280, height: 900 },
  args: ["--disable-extensions"]
});
const pages = context.pages();
const page = pages.find(candidate => candidate.url().startsWith("http://127.0.0.1:4174")) ?? pages[0] ?? await context.newPage();
page.on("dialog", async dialog => {
  dialogs.push({ type: dialog.type(), message: dialog.message() });
  await dialog.accept();
});
if (!page.url().startsWith("http://127.0.0.1:4174")) await page.goto(url);
await page.waitForFunction(() => globalThis.deductriumGame?.hyperGui?.world);

const print = value => console.log(JSON.stringify(value, null, 2));

async function writeJsonAtomic(path, value) {
  const previous = atomicWriteQueues.get(path) ?? Promise.resolve();
  const current = previous.catch(() => {}).then(async () => {
    const temp = `${path}.${process.pid}.${Date.now()}-${Math.random().toString(36).slice(2)}.tmp`;
    await writeFile(temp, JSON.stringify(value, null, 2), "utf8");
    let lastError;
    for (let attempt = 0; attempt < 12; attempt++) {
      try {
        await rename(temp, path);
        return;
      } catch (error) {
        lastError = error;
        if (error?.code !== "EPERM" && error?.code !== "EBUSY") throw error;
        await new Promise(resolve => setTimeout(resolve, 20 * (attempt + 1)));
      }
    }
    try { await rename(temp, path); } catch { }
    throw lastError;
  });
  atomicWriteQueues.set(path, current);
  try {
    await current;
  } finally {
    if (atomicWriteQueues.get(path) === current) atomicWriteQueues.delete(path);
  }
}
const gameState = () => page.evaluate(() => {
  const game = globalThis.deductriumGame;
  return {
    tile: game.hyperGui.world.currentTile,
    deductriums: game.deductriums,
    rewards: game.rewards,
    propositions: game.fsGui.formalSystem.propositions.length,
    rules: game.fsGui.deductions
  };
});

async function captureProgressFrame() {
  if (progressFrameCapture) return progressFrameCapture;
  progressFrameCapture = (async () => {
    const frameId = ++progressFrameId;
    const slot = frameId % 3;
    const frameName = `game-progress-frame-${slot}.png`;
    await page.screenshot({ path: `${progressDir}\\${frameName}` });
  await writeJsonAtomic(progressFrameJson, { frameId, src: `game-progress/${frameName}` });
    return frameId;
  })().finally(() => {
    progressFrameCapture = null;
  });
  return progressFrameCapture;
}

async function publishMirrorFrame() {
  const mirror = await page.evaluate(() => {
    const game = globalThis.deductriumGame;
    const world = game.hyperGui.world;
    return {
      tile: world.currentTile.slice(),
      currentOrd: Array.isArray(world.currentOrd) ? world.currentOrd.slice() : world.currentOrd,
      camera: {
        r: world.localCamMat.r,
        x: world.localCamMat.x,
        y: world.localCamMat.y,
        z: world.localCamMat.z
      }
    };
  });
  const payload = { frameId: ++progressMirrorId, updatedAt: new Date().toISOString(), ...mirror };
  await writeJsonAtomic(progressMirrorJson, payload);
}

async function publishProgress(action = "started", result = null, error = null) {
  const state = await page.evaluate(() => {
    const game = globalThis.deductriumGame;
    const world = game.hyperGui.world;
    const parser = game.fsGui.cmd.astparser;
    const currentHash = world.currentTile.join(",");
    const current = world.getBlock(currentHash);
    const nearby = Array.from({ length: world.atlasTile.p }, (_, direction) => {
      const [tile] = world.atlasTile.getNeighborAndDir(world.currentTile, direction, true);
      const block = world.getBlock(tile.join(","));
      return {
        direction,
        tile: tile.join(","),
        name: block?.name ?? null,
        type: block?.type ?? null,
        text: block?.text ?? ""
      };
    });
    return {
      mode: game.creative ? "creative" : "survival",
      tile: currentHash,
      current: { name: current?.name ?? null, type: current?.type ?? null, text: current?.text ?? "" },
      nearby,
      deductriums: game.deductriums,
      consumed: game.consumed,
      parcours: game.parcours,
      destructedGates: game.destructedGates,
      rewards: game.rewards,
      propositions: game.fsGui.formalSystem.propositions.map((item, index) => ({
        index,
        value: parser.stringifyTight(item.value),
        rule: item.from?.deductionIdx ?? "hyp"
      })),
      rules: game.fsGui.deductions.filter(name => !name.startsWith("< f >")),
      folders: game.fsGui.deductions.filter(name => name.startsWith("< f >")),
      metarules: game.fsGui.metarules
    };
  });
  activity.push({ time: new Date().toISOString(), action, ok: !error, error, result });
  if (activity.length > 80) activity.splice(0, activity.length - 80);
  try { await captureProgressFrame(); } catch { }
  await publishMirrorFrame();
  const storage = await page.evaluate(() => Object.fromEntries(Object.entries(localStorage)));
  await writeJsonAtomic(progressSaveJson, { updatedAt: new Date().toISOString(), storage });
  const snapshot = { updatedAt: new Date().toISOString(), state, dialogs: dialogs.slice(-10), activity: activity.slice().reverse() };
  await writeJsonAtomic(progressJson, snapshot);
}

async function uiFs(source) {
  const deductButton = page.locator("#deduct-btn");
  if (await deductButton.isVisible()) await deductButton.click();
  const commands = source.split(";").map(value => value.trim()).filter(Boolean);
  const input = page.locator("#action-input");
  for (const command of commands) {
    await input.fill(command);
    await input.press("Enter");
    await page.waitForTimeout(30);
  }
  return page.evaluate(commands => {
    const game = globalThis.deductriumGame;
    return {
      commands,
      buffer: game.fsGui.cmd.cmdBuffer.slice(),
      hint: game.fsGui.hintText.innerText,
      propositions: game.fsGui.formalSystem.propositions.map(item => game.fsGui.cmd.astparser.stringifyTight(item.value))
    };
  }, commands);
}

async function uiDeduct(rule, rawIndices = "") {
  const deductButton = page.locator("#deduct-btn");
  if (await deductButton.isVisible()) await deductButton.click();
  const indices = rawIndices.trim() === "" ? [] : rawIndices.split(",").map(value => {
    const match = /^p?(\d+)$/i.exec(value.trim());
    if (!match) throw new Error(`invalid proposition index: ${value}`);
    return Number(match[1]);
  });
  const commandButton = page.locator(".cmd-btns button").filter({ hasText: new RegExp(`^${rule}$`) }).first();
  if (await commandButton.count()) await commandButton.click();
  else {
    const idx = page.locator("#deduct-list .idx").filter({ hasText: new RegExp(`^${rule}$`) }).first();
    if (!await idx.count()) throw new Error(`rule not found: ${rule}`);
    await idx.locator("xpath=following-sibling::*[1]").click();
  }
  for (const index of indices) {
    const idx = page.locator("#prop-list .idx").nth(index);
    if (!await idx.count()) throw new Error(`proposition not found: p${index}`);
    await idx.locator("xpath=following-sibling::*[1]").click();
    await page.waitForTimeout(30);
  }
  return page.evaluate(({ rule, indices }) => {
    const game = globalThis.deductriumGame;
    return {
      rule,
      indices,
      buffer: game.fsGui.cmd.cmdBuffer.slice(),
      hint: game.fsGui.hintText.innerText,
      propositions: game.fsGui.formalSystem.propositions.map(item => game.fsGui.cmd.astparser.stringifyTight(item.value))
    };
  }, { rule, indices });
}

async function uiAssist(target, script, name = "") {
  const deductButton = page.locator("#deduct-btn");
  if (await deductButton.isVisible()) await deductButton.click();
  await page.locator("#fs-proof-target").fill(target);
  await page.locator("#fs-proof-begin").click();
  const commands = script.split(";").map(value => value.trim()).filter(Boolean);
  for (const command of commands) {
    await page.locator("#fs-proof-input").fill(command);
    await page.locator("#fs-proof-apply").click();
    await page.waitForFunction(() => !globalThis.deductriumGame.fsGui.inferenceProofBusy);
    const error = (await page.locator("#fs-proof-errmsg").innerText()).trim();
    if (error) throw new Error(`${command}: ${error}`);
  }
  if (name) await page.locator("#fs-proof-name").fill(name);
  await page.locator("#fs-proof-qed").click();
  await page.waitForFunction(() => !globalThis.deductriumGame.fsGui.inferenceProofBusy);
  const error = (await page.locator("#fs-proof-errmsg").innerText()).trim();
  if (error) throw new Error(`qed: ${error}`);
  return page.evaluate(({ target, commands, name }) => {
    const game = globalThis.deductriumGame;
    return {
      target,
      commands,
      name: name || null,
      propositions: game.fsGui.formalSystem.propositions.map((item, index) => ({ index, value: game.fsGui.cmd.astparser.stringifyTight(item.value) })),
      rules: game.fsGui.deductions
    };
  }, { target, commands, name });
}

async function resolveTarget(place) {
  return page.evaluate(async place => {
    const { nameMap } = await import("/js/hy/maploader.js");
    const target = nameMap.get(place) ?? place;
    if (!/^(?:|[0-9]+(?:,[0-9]+)*)$/.test(target)) throw new Error(`unknown place: ${place}`);
    return target;
  }, place);
}

async function nextRouteStep(target, blocked) {
  return page.evaluate(async ({ target, blocked }) => {
    const world = globalThis.deductriumGame.hyperGui.world;
    const { blockMap } = await import("/js/hy/maploader.js");
    const start = world.currentTile.join(",");
    if (start === target) return { done: true };
    const excluded = new Set(blocked);
    const queue = [world.currentTile.slice()];
    const previous = new Map([[start, null]]);
    while (queue.length && previous.size < 10000) {
      const tile = queue.shift();
      const hash = tile.join(",");
      if (hash === target) break;
      for (let direction = 0; direction < world.atlasTile.p; direction++) {
        const [next] = world.atlasTile.getNeighborAndDir(tile, direction, true);
        const nextHash = next.join(",");
        const block = blockMap.get(nextHash);
        if (previous.has(nextHash) || !block || block.type === 1 || excluded.has(nextHash)) continue;
        previous.set(nextHash, hash);
        queue.push(next);
      }
    }
    if (!previous.has(target)) return { done: false, error: "no unblocked mapped route" };
    const path = [];
    for (let cursor = target; cursor !== start; cursor = previous.get(cursor)) path.push(cursor);
    return { done: false, next: path.reverse()[0] };
  }, { target, blocked });
}

async function dragToward(nextHash) {
  const canvas = page.locator("canvas");
  const box = await canvas.boundingBox();
  if (!box) throw new Error("canvas is not visible");
  const center = { x: box.x + box.width / 2, y: box.y + box.height / 2 };
  const initial = await page.evaluate(() => globalThis.deductriumGame.hyperGui.world.currentTile.join(","));
  for (let attempt = 0; attempt < 50; attempt++) {
    const vector = await page.evaluate(async target => {
      const world = globalThis.deductriumGame.hyperGui.world;
      const { Hvec } = await import("/js/hy/algebra.js");
      const rotor = world.atlasTile.rotors.get(target);
      if (!rotor) return null;
      const point = world.localCamMat.mul(rotor).apply(new Hvec());
      const length = Math.hypot(point.x, point.y) || 1;
      return { dx: -point.x / length * 80, dy: -point.y / length * 80 };
    }, nextHash);
    if (!vector) throw new Error(`target is not adjacent: ${initial} -> ${nextHash}`);
    await page.mouse.move(center.x, center.y);
    await page.mouse.down();
    for (let dragStep = 1; dragStep <= 5; dragStep++) {
      await page.mouse.move(
        center.x + vector.dx * dragStep / 5,
        center.y + vector.dy * dragStep / 5
      );
      await page.waitForTimeout(16);
      await publishMirrorFrame();
    }
    await page.mouse.up();
    await page.waitForTimeout(20);
    const current = await page.evaluate(() => globalThis.deductriumGame.hyperGui.world.currentTile.join(","));
    if (current === nextHash) return { reached: true, current };
    if (current !== initial) return { reached: false, deviated: current };
  }
  return { reached: false, current: initial };
}

async function moveTo(place) {
  const geometryButton = page.locator("#panel > button").first();
  if (await geometryButton.isVisible()) await geometryButton.click();
  const target = await resolveTarget(place);
  const visited = [], blocked = [];
  for (let step = 0; step < 1000; step++) {
    const route = await nextRouteStep(target, blocked.map(item => item.tile));
    if (route.done) return { ok: true, target, visited, blocked };
    if (route.error) return { ok: false, target, visited, blocked, error: route.error };
    const movement = await dragToward(route.next);
    if (movement.reached) {
      visited.push(route.next);
      continue;
    }
    if (movement.deviated) {
      visited.push(movement.deviated);
      continue;
    }
    const detail = await page.evaluate(tile => {
      const world = globalThis.deductriumGame.hyperGui.world;
      const block = world.getBlock(tile);
      return { tile, name: block?.name ?? null, text: block?.text ?? "", type: block?.type ?? null };
    }, route.next);
    blocked.push(detail);
    if (route.next === target) return { ok: false, target, visited, blocked };
  }
  return { ok: false, target, visited, blocked, error: "movement step limit exceeded" };
}

async function stepTo(place) {
  const geometryButton = page.locator("#panel > button").first();
  if (await geometryButton.isVisible()) await geometryButton.click();
  const target = await resolveTarget(place);
  const current = await page.evaluate(() => globalThis.deductriumGame.hyperGui.world.currentTile.join(","));
  const adjacent = await page.evaluate(({ current, target }) => {
    const world = globalThis.deductriumGame.hyperGui.world;
    for (let direction = 0; direction < world.atlasTile.p; direction++) {
      const [tile] = world.atlasTile.getNeighborAndDir(world.currentTile, direction, true);
      if (tile.join(",") === target) return true;
    }
    return false;
  }, { current, target });
  if (!adjacent) throw new Error(`step target is not adjacent: ${current} -> ${target}`);
  const movement = await dragToward(target);
  const detail = await page.evaluate(tile => {
    const world = globalThis.deductriumGame.hyperGui.world;
    const block = world.getBlock(tile);
    return { tile, name: block?.name ?? null, text: block?.text ?? "", type: block?.type ?? null };
  }, target);
  return { target, movement, detail };
}

async function command(line) {
  const [verb, ...args] = line.trim().split(/\s+/);
  if (verb === "status") return { ...(await gameState()), dialogs };
  if (verb === "nearby" || verb === "doors") {
    const depth = Math.max(1, Math.min(8, Number(args[0]) || 1));
    const query = args.slice(1).join(" ").trim().toLowerCase();
    return page.evaluate(({ doors, depth, query }) => {
    const world = globalThis.deductriumGame.hyperGui.world;
    const start = world.currentTile.join(",");
    const queue = [{ tile: world.currentTile.slice(), distance: 0, path: [] }];
    const seen = new Set([start]);
    const result = [];
    while (queue.length) {
      const current = queue.shift();
      if (current.distance >= depth) continue;
      for (let direction = 0; direction < world.atlasTile.p; direction++) {
        const [tile] = world.atlasTile.getNeighborAndDir(current.tile, direction, true);
        const hash = tile.join(",");
        if (seen.has(hash)) continue;
        seen.add(hash);
        const block = world.getBlock(hash);
        const item = {
          distance: current.distance + 1,
          path: [...current.path, direction],
          tile: hash,
          name: block?.name ?? null,
          type: block?.type ?? null,
          text: block?.text ?? ""
        };
        const haystack = `${item.tile}\n${item.name || ""}\n${item.text}`.toLowerCase();
        if ((!doors || item.type === 2 || item.type === 4) && (!query || haystack.includes(query))) result.push(item);
        if (block && block.type !== 1) queue.push({ tile, distance: item.distance, path: item.path });
      }
    }
    return result;
  }, { doors: verb === "doors", depth, query });
  }
  if (verb === "move") return moveTo(args.join(" "));
  if (verb === "step") return stepTo(args.join(" "));
  if (verb === "ui-fs") return uiFs(args.join(" "));
  if (verb === "ui-deduct") return uiDeduct(args[0], args[1]);
  if (verb === "ui-assist") {
    const [target = "", script = "", name = ""] = args.join(" ").split("::");
    if (!target || !script) throw new Error("ui-assist expects target::command;command[::name]");
    return uiAssist(target, script, name);
  }
  if (verb === "eval") return page.evaluate(expression => (0, eval)(expression), args.join(" "));
  if (verb === "wait") { await page.waitForTimeout(Number(args[0]) || 1000); return true; }
  throw new Error("commands: status | nearby [depth] [filter] | doors [depth] [filter] | move <place> | step <adjacent-place> | ui-fs <cmd;...> | ui-deduct <rule> [pN,pM] | ui-assist <target>::<commands>[::name] | eval <js> | wait <ms> | quit");
}

console.log("Deductrium Playwright game console");
await publishProgress();
const rl = readline.createInterface({ input: process.stdin, output: process.stdout, prompt: "game> " });
rl.prompt();
try {
  for await (const line of rl) {
    const value = line.trim();
    if (!value) { if (!rl.closed) rl.prompt(); continue; }
    if (value === "quit" || value === "exit") break;
    try {
      const result = await command(value);
      await publishProgress(value, result);
      print(result);
    } catch (error) {
      await publishProgress(value, null, error.message);
      console.error(`error: ${error.message}`);
    }
    if (!rl.closed) rl.prompt();
  }
} finally {
  await page.waitForTimeout(100);
  await context.close();
}
