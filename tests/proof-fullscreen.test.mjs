import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { installProofFullscreen } from "../js/proof-fullscreen.js";

class Element extends EventTarget {
    attributes = new Map();
    style = { overflow: "auto" };
    scrollTop = 31;
    scrollLeft = 7;
    children = [{ value: "intro h", open: false }];
    classes = new Set();
    classList = {
        add: name => this.classes.add(name),
        remove: name => this.classes.delete(name)
    };
    setAttribute(name, value) { this.attributes.set(name, value); }
    focus(options) { this.focusOptions = options; }
}
function setup(native = false) {
    const doc = Object.assign(new EventTarget(), {
        body: new Element(), fullscreenEnabled: native, fullscreenElement: null
    });
    const host = Object.assign(new Element(), { ownerDocument: doc });
    const button = new Element();
    doc.exitFullscreen = async () => {
        doc.fullscreenElement = null;
        doc.dispatchEvent(new Event("fullscreenchange"));
    };
    host.requestFullscreen = async () => {
        doc.fullscreenElement = host;
        doc.dispatchEvent(new Event("fullscreenchange"));
    };
    installProofFullscreen(host, button);
    installProofFullscreen(host, button);
    return { host, button, doc };
}
const click = button => button.dispatchEvent(new Event("click"));
const settle = async () => { await Promise.resolve(); await Promise.resolve(); };
const escape = doc => {
    const event = Object.assign(new Event("keydown", { cancelable: true }), { key: "Escape" });
    doc.dispatchEvent(event);
    assert.equal(event.defaultPrevented, true);
};

for (const native of [false, true]) {
    const { host, button, doc } = setup(native);
    const proof = host.children[0];
    click(button);
    await settle();
    assert.equal(button.attributes.get("aria-pressed"), "true");
    assert.equal(host.classes.has("proof-assistant-fullscreen"), true);
    assert.equal(doc.body.style.overflow, "hidden");
    assert.equal(doc.fullscreenElement, native ? host : null);
    host.scrollTop = 200;
    escape(doc);
    await settle();
    assert.equal(host.classes.has("proof-assistant-fullscreen"), false);
    assert.equal(button.attributes.get("aria-pressed"), "false");
    assert.equal(doc.body.style.overflow, "auto");
    assert.equal(host.scrollTop, 31);
    assert.equal(host.scrollLeft, 7);
    assert.equal(host.children[0], proof);
    assert.equal(proof.value, "intro h");
    assert.equal(proof.open, false);
    assert.deepEqual(button.focusOptions, { preventScroll: true });
    click(button);
    await settle();
    click(button);
    await settle();
    assert.equal(button.attributes.get("aria-pressed"), "false");
}

{
    const { host, button, doc } = setup(true);
    host.requestFullscreen = async () => { throw new Error("not allowed"); };
    click(button);
    await settle();
    assert.equal(host.classes.has("proof-assistant-fullscreen"), true, "native denial keeps viewport fallback");
    escape(doc);
    await settle();
    assert.equal(host.classes.has("proof-assistant-fullscreen"), false);
}
{
    const { host, button, doc } = setup(true);
    click(button);
    await settle();
    await doc.exitFullscreen();
    assert.equal(button.attributes.get("aria-pressed"), "false", "browser-native Escape synchronizes state");
    assert.equal(host.classes.has("proof-assistant-fullscreen"), false);
}
{
    const { host, button, doc } = setup(true);
    let finish;
    let requests = 0;
    host.requestFullscreen = () => {
        requests++;
        return new Promise(resolve => { finish = () => {
            doc.fullscreenElement = host;
            doc.dispatchEvent(new Event("fullscreenchange"));
            resolve();
        }; });
    };
    click(button);
    click(button);
    escape(doc);
    finish();
    await settle();
    await settle();
    assert.equal(requests, 1, "repeated clicks serialize requests");
    assert.equal(doc.fullscreenElement, null, "Escape during entry exits after the request settles");
}

const html = readFileSync(new URL("../index.html", import.meta.url), "utf8");
for (const [layer, host, button] of [
    ["tt", "tactic-div", "tactic-fullscreen"],
    ["fs", "fs-proof-assistant", "fs-proof-fullscreen"]
]) {
    assert.match(html, new RegExp(`id="${button}"[^>]*type="button"`));
    const gui = readFileSync(new URL(`../src/${layer}/gui.ts`, import.meta.url), "utf8");
    assert.ok(gui.includes(`installProofFullscreen(document.getElementById("${host}"), document.getElementById("${button}"))`));
}
console.log("shared proof fullscreen native, fallback, Escape and state retention regression passed");
