#!/usr/bin/env node
import readline from "node:readline";
import { Polygon } from "../js/hy/tiling.js";
import { blockMap, duplicateNames, initMap, nameMap, TileBlockType } from "../js/hy/maploader.js";
import { initFormalSystem } from "../js/fs/initial.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";

const polygon = new Polygon(6, 4);
initMap(polygon);

const TYPE_NAMES = ["road", "wall", "gate", "reward", "ordinal"];
const state = { tile: [] };

function hashOf(tile) { return tile.join(","); }
function parseTile(value) {
  if (value === undefined || value === "" || value === "here") return state.tile.slice();
  const named = nameMap.get(value);
  const raw = named ?? value;
  if (!/^-?\d+(,-?\d+)*$/.test(raw)) throw new Error(`invalid tile or unknown name: ${value}`);
  return raw.split(",").map(Number);
}
function blockAt(tile) { return blockMap.get(hashOf(tile)); }
function describe(tile) {
  const block = blockAt(tile);
  return {
    tile: hashOf(tile),
    name: block?.name ?? null,
    type: block ? TYPE_NAMES[block.type] : "unmapped",
    text: block?.text ?? ""
  };
}
function print(value) { console.log(typeof value === "string" ? value : JSON.stringify(value, null, 2)); }
function neighbors(tile) {
  return Array.from({ length: polygon.p }, (_, dir) => {
    const [next] = polygon.getNeighborAndDir(tile, dir, true);
    return { direction: dir, tile: hashOf(next), ...describe(next) };
  });
}
function scan() {
  const malformed = [];
  for (const [tile, block] of blockMap) {
    if (!Number.isInteger(block.type) || !TYPE_NAMES[block.type]) malformed.push({ tile, block });
    if (block.name && nameMap.get(block.name) !== tile) malformed.push({ tile, issue: "nameMap mismatch", name: block.name });
  }
  return { blocks: blockMap.size, names: nameMap.size, duplicateNames: duplicateNames.slice(), malformed };
}
function moveTo(value) {
  const target = parseTile(value), targetHash = hashOf(target), startHash = hashOf(state.tile);
  const queue = [state.tile.slice()], previous = new Map([[startHash, null]]), via = new Map();
  while (queue.length) {
    const current = queue.shift(), currentHash = hashOf(current);
    if (currentHash === targetHash) break;
    for (let direction = 0; direction < polygon.p; direction++) {
      const [next] = polygon.getNeighborAndDir(current, direction, true), nextHash = hashOf(next);
      if (previous.has(nextHash)) continue;
      const block = blockAt(next);
      if (!block || block.type === TileBlockType.Wall || block.type === TileBlockType.Gate) continue;
      previous.set(nextHash, currentHash); via.set(nextHash, direction); queue.push(next);
    }
  }
  if (!previous.has(targetHash)) throw new Error(`no passable route from ${startHash || "origin"} to ${targetHash}`);
  const directions = [];
  for (let cursor = targetHash; cursor !== startHash; cursor = previous.get(cursor)) directions.push(via.get(cursor));
  directions.reverse();
  const steps = [];
  for (const direction of directions) { const [next] = polygon.getNeighborAndDir(state.tile, direction, true); state.tile = next; steps.push({ direction, tile: hashOf(next), block: describe(next) }); }
  print({ from: startHash, to: targetHash, steps });
}
function help() {
  console.log(`Commands:
  status                         show current tile and block
  go <0-5> [count]               move until a wall, gate, or requested count
  go <0-5> [count] --through-gates  ignore gate locks for topology exploration
  move <tile|name>               find and follow a passable route to a place
  neighbors [tile|name]         inspect all adjacent tiles
  inspect [tile|name]            inspect one tile (default: current)
  find <text>                    search block names and descriptions
  scan                           check map/name consistency
  proof <target> <cmds>          run proof commands separated by ';'
  proof ... --entr               qed, then expand the resulting proposition
  reset                          return to the origin
  help                           show this help
  quit                           exit`);
}
function proof(args) {
  const entr = args.includes("--entr");
  const nameIndex = args.indexOf("--name");
  const qedName = nameIndex >= 0 ? args[nameIndex + 1] : undefined;
  const filtered = args.filter((arg, index) => arg !== "--entr" && index !== nameIndex && index !== nameIndex + 1);
  const target = filtered.shift();
  const commands = filtered.join(" ").split(";").map(command => command.trim()).filter(Boolean);
  if (!target || !commands.length) throw new Error("proof expects a target and semicolon-separated commands");
  const fs = initFormalSystem(true).fs;
  const assistant = new InferenceProofAssistant(fs, target);
  for (const commandText of commands) assistant.apply(commandText);
  const result = assistant.qed(qedName);
  const output = { target, commands, qed: { committed: result.committed, deferred: result.deferred }, propositions: fs.propositions.length };
  if (entr && fs.propositions.length) {
    fs.expandMacroWithProp(fs.propositions.length - 1);
    output.entr = { ok: true, propositions: fs.propositions.length };
  } else if (entr) {
    output.entr = { ok: false, error: "qed produced no proposition (named qed clears the active page)" };
  }
  print(output);
}
function command(line) {
  const [verb, ...args] = line.trim().split(/\s+/);
  if (!verb) return true;
  if (verb === "help" || verb === "?") { help(); return true; }
  if (verb === "quit" || verb === "exit") return false;
  if (verb === "status") { print(describe(state.tile)); return true; }
  if (verb === "reset") { state.tile = []; print(describe(state.tile)); return true; }
  if (verb === "inspect") { print(describe(parseTile(args[0]))); return true; }
  if (verb === "neighbors") { print(neighbors(parseTile(args[0]))); return true; }
  if (verb === "go") {
    const dir = Number(args[0]);
    const throughGates = args.includes("--through-gates");
    const countArg = args.find(arg => arg !== "--through-gates");
    const count = countArg === undefined ? 1 : Number(countArg);
    if (!Number.isInteger(dir) || dir < 0 || dir >= polygon.p || !Number.isInteger(count) || count < 1) throw new Error("go expects direction 0-5 and a positive count");
    const steps = [];
    for (let i = 0; i < count; i++) {
      const [next] = polygon.getNeighborAndDir(state.tile, dir, true);
      const block = blockAt(next);
      steps.push({ from: hashOf(state.tile), direction: dir, to: hashOf(next), passable: block?.type !== TileBlockType.Wall, block: describe(next) });
      if (block?.type === TileBlockType.Wall || !block || (block?.type === TileBlockType.Gate && !throughGates)) break;
      state.tile = next;
    }
    print(steps); return true;
  }
  if (verb === "move") { if (!args[0]) throw new Error("move expects a tile or name"); moveTo(args[0]); return true; }
  if (verb === "find") {
    const needle = args.join(" ").toLocaleLowerCase();
    if (!needle) throw new Error("find expects text");
    const matches = [];
    for (const [tile, block] of blockMap) {
      if (`${block.name ?? ""} ${block.text}`.toLocaleLowerCase().includes(needle)) matches.push({ tile, ...describe(tile.split(",").map(Number)) });
    }
    print(matches); return true;
  }
  if (verb === "scan") { print(scan()); return true; }
  if (verb === "proof") { proof(args); return true; }
  throw new Error(`unknown command: ${verb}`);
}

if (process.argv.length > 2) {
  try { process.exitCode = command(process.argv.slice(2).join(" ")) ? 0 : 0; }
  catch (error) { console.error(`error: ${error.message}`); process.exitCode = 1; }
} else {
  console.log("Deductrium game CLI (map-level harness)");
  help();
  const rl = readline.createInterface({ input: process.stdin, output: process.stdout, prompt: "game> " });
  rl.prompt();
  rl.on("line", line => {
    try { if (!command(line)) rl.close(); }
    catch (error) { console.error(`error: ${error.message}`); }
    if (!rl.closed) rl.prompt();
  });
}
