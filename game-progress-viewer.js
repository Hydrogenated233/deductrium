const byId = id => document.getElementById(id);
const connection = byId("connection");
const gameFrame = byId("game-frame");
const mirror = byId("game-mirror");
const fallback = byId("game-fallback");
const frameLayers = [byId("game-shot-a"), byId("game-shot-b")];
const mirrorOrigin = "http://localhost:4174";
const observerSessionId = crypto.randomUUID ? crypto.randomUUID() : `${Date.now()}-${Math.random()}`;
let activeFrameLayer = 0;
let displayedFrameId = -1;
let displayedMirrorFrameId = -1;
let frameRequestPending = false;
let mirrorRequestPending = false;
let stateRequestPending = false;
let saveRequestPending = false;
let mirrorReady = false;
let mirrorRendering = false;
let latestState = null;
let latestMirrorFrame = null;
let latestStorage = null;

function fitMirror() {
  const scale = Math.min(gameFrame.clientWidth / 1280, gameFrame.clientHeight / 900);
  mirror.style.transform = `translate(-50%, -50%) scale(${scale})`;
}

new ResizeObserver(fitMirror).observe(gameFrame);
fitMirror();

function replaceChildren(element, children) {
  element.replaceChildren(...children);
}

function makeElement(tag, className, text) {
  const element = document.createElement(tag);
  if (className) element.className = className;
  if (text !== undefined) element.textContent = String(text);
  return element;
}

function renderMetrics(state) {
  const values = [
    ["模式", state.mode],
    ["推理素", `${state.deductriums}µg`],
    ["移动步数", state.parcours],
    ["已拆门", state.destructedGates],
    ["定理", state.propositions.length],
    ["规则", state.rules.length]
  ];
  replaceChildren(byId("metrics"), values.map(([label, value]) => {
    const item = makeElement("div", "metric");
    item.append(makeElement("span", "metric-label", label), makeElement("strong", "metric-value", value));
    return item;
  }));
}

function renderNearby(state) {
  replaceChildren(byId("nearby"), state.nearby.map(item => {
    const className = item.type === 2 ? "nearby-item gate" : item.type === 3 ? "nearby-item reward" : "nearby-item";
    const row = makeElement("div", className);
    row.append(
      makeElement("strong", "", `${item.direction}: ${item.name || item.tile}`),
      makeElement("span", "", item.text || item.tile)
    );
    return row;
  }));
}

function renderRewards(state) {
  const rewards = state.rewards.slice(-18).reverse();
  replaceChildren(byId("rewards"), rewards.map(value => makeElement("span", "tag", value)));
}

function renderPropositions(state) {
  replaceChildren(byId("propositions"), state.propositions.map(item => {
    const row = document.createElement("tr");
    row.append(makeElement("td", "", `p${item.index}`), makeElement("td", "", item.value), makeElement("td", "", item.rule));
    return row;
  }));
  byId("prop-count").textContent = `${state.propositions.length} 条`;
}

function renderActivity(activity) {
  replaceChildren(byId("activity"), activity.map(item => {
    const row = document.createElement("tr");
    const time = new Date(item.time).toLocaleTimeString("zh-CN", { hour12: false });
    row.append(
      makeElement("td", "", time),
      makeElement("td", "", item.action),
      makeElement("td", item.ok ? "ok" : "fail", item.ok ? "完成" : item.error || "失败")
    );
    return row;
  }));
  byId("action-count").textContent = `${activity.length} 条`;
}

function renderSnapshot(snapshot) {
  const { state } = snapshot;
  renderMetrics(state);
  renderNearby(state);
  renderRewards(state);
  renderPropositions(state);
  renderActivity(snapshot.activity);
  byId("location").textContent = state.tile;
  byId("current").textContent = [
    `tile: ${state.tile}`,
    `name: ${state.current.name || "-"}`,
    `type: ${state.current.type ?? "-"}`,
    state.current.text || ""
  ].join("\n");
  byId("updated").textContent = `更新于 ${new Date(snapshot.updatedAt).toLocaleString("zh-CN", { hour12: false })}`;
  connection.textContent = "实时";
  connection.className = "connection online";
}

function postMirror(message) {
  if (!mirror.contentWindow) return;
  mirror.contentWindow.postMessage(message, mirrorOrigin);
}

function bootstrapMirror() {
  if (!mirrorReady || !latestState || !latestMirrorFrame || !latestStorage) return;
  postMirror({
    type: "deductrium-observer-bootstrap",
    sessionId: observerSessionId,
    storage: latestStorage,
    state: latestState,
    frame: latestMirrorFrame
  });
}

addEventListener("message", event => {
  if (event.origin !== mirrorOrigin || event.source !== mirror.contentWindow) return;
  if (event.data?.type === "deductrium-observer-ready") {
    mirrorReady = true;
    mirrorRendering = false;
    bootstrapMirror();
    return;
  }
  if (event.data?.type === "deductrium-observer-rendering") {
    mirrorRendering = true;
    fallback.classList.add("hidden");
  }
});

async function refreshState() {
  if (stateRequestPending) return;
  stateRequestPending = true;
  try {
    const response = await fetch(`game-progress/game-progress.json?t=${Date.now()}`, { cache: "no-store" });
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const snapshot = await response.json();
    latestState = snapshot.state;
    renderSnapshot(snapshot);
    if (mirrorRendering) postMirror({ type: "deductrium-observer-state", state: latestState });
    else bootstrapMirror();
  } catch {
    connection.textContent = "等待连接";
    connection.className = "connection error";
  } finally {
    stateRequestPending = false;
  }
}

async function refreshSave() {
  if (saveRequestPending) return;
  saveRequestPending = true;
  try {
    const response = await fetch(`game-progress/game-progress-save.json?t=${Date.now()}`, { cache: "no-store" });
    if (!response.ok) return;
    latestStorage = (await response.json()).storage;
    bootstrapMirror();
  } catch {
    // The screenshot fallback remains available until the mirror save is published.
  } finally {
    saveRequestPending = false;
  }
}

async function refreshMirror() {
  if (mirrorRequestPending) return;
  mirrorRequestPending = true;
  try {
    const response = await fetch(`game-progress/game-progress-mirror.json?t=${Date.now()}`, { cache: "no-store" });
    if (!response.ok) return;
    const frame = await response.json();
    if (frame.frameId <= displayedMirrorFrameId) return;
    latestMirrorFrame = frame;
    displayedMirrorFrameId = frame.frameId;
    if (mirrorRendering) postMirror({ type: "deductrium-observer-frame", frame });
    else bootstrapMirror();
  } catch {
    // The last rendered game frame stays visible.
  } finally {
    mirrorRequestPending = false;
  }
}

function loadImage(image, src) {
  return new Promise((resolve, reject) => {
    image.onload = () => resolve();
    image.onerror = reject;
    image.src = src;
  });
}

async function refreshFrame() {
  if (frameRequestPending) return;
  frameRequestPending = true;
  try {
    const response = await fetch(`game-progress/game-progress-frame.json?t=${Date.now()}`, { cache: "no-store" });
    if (!response.ok) return;
    const frame = await response.json();
    if (frame.frameId <= displayedFrameId) return;
    const nextLayer = 1 - activeFrameLayer;
    const nextImage = frameLayers[nextLayer];
    await loadImage(nextImage, `${frame.src}?frame=${frame.frameId}`);
    frameLayers[activeFrameLayer].classList.remove("active");
    nextImage.classList.add("active");
    activeFrameLayer = nextLayer;
    displayedFrameId = frame.frameId;
  } catch {
    // State polling reports connection failures; keep the last valid frame visible.
  } finally {
    frameRequestPending = false;
  }
}

await Promise.all([refreshState(), refreshSave(), refreshMirror(), refreshFrame()]);
setInterval(refreshState, 750);
setInterval(refreshSave, 2000);
setInterval(refreshMirror, 50);
setInterval(refreshFrame, 300);
