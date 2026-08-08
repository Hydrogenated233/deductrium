import assert from "node:assert/strict";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const engine = new TTCoreEngine();
engine.configure({
  unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
  inferDisplayMode: "_",
  timeout: 30_000,
  language: "zh"
});

const log = console.log;
try {
  console.log = () => {};
  const unlifted = engine.check("Πa:U0,Πb:U0,((a ≃ b) ≃ (a = b))");
  assert.equal(unlifted.ok, false, "equivalences at different universe levels must not be accepted");

  const lifted = engine.check("Πa:U0,Πb:U0,((LiftU (a ≃ b)) ≃ (a = b))");
  assert.equal(lifted.ok, true, "LiftU should make the universe levels agree");
} finally {
  console.log = log;
}

console.log("universe-level equivalence regression passed");
