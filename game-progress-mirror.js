(() => {
  const observerMode = new URLSearchParams(location.search).get("game-progress-observer") === "1";
  if (!observerMode) return;

  const allowedParents = new Set(["http://127.0.0.1:4174", "http://localhost:4174"]);
  let readyTimer = null;

  function send(type, detail = {}) {
    window.parent.postMessage({ type, ...detail }, "*");
  }

  async function waitForGame() {
    const startedAt = Date.now();
    while (!globalThis.deductriumGame?.hyperGui?.world) {
      if (Date.now() - startedAt > 30000) throw new Error("mirror game did not initialize");
      await new Promise(resolve => setTimeout(resolve, 50));
    }
    return globalThis.deductriumGame;
  }

  function applyState(game, state) {
    game.deductriums = state.deductriums;
    game.consumed = state.consumed;
    game.parcours = state.parcours;
    game.destructedGates = state.destructedGates;
    if (Array.isArray(game.rewards)) game.rewards.splice(0, game.rewards.length, ...state.rewards);
  }

  function applyFrame(game, frame) {
    const world = game.hyperGui.world;
    world.currentTile.splice(0, world.currentTile.length, ...frame.tile);
    if (Array.isArray(world.currentOrd) && Array.isArray(frame.currentOrd)) {
      world.currentOrd.splice(0, world.currentOrd.length, ...frame.currentOrd);
    }
    Object.assign(world.localCamMat, frame.camera);
  }

  window.addEventListener("message", async event => {
    if (!allowedParents.has(event.origin)) return;
    const message = event.data;
    if (!message || typeof message !== "object") return;

    if (message.type === "deductrium-observer-bootstrap") {
      const marker = "deductrium-observer-session";
      if (sessionStorage.getItem(marker) !== message.sessionId) {
        for (const [key, value] of Object.entries(message.storage || {})) localStorage.setItem(key, value);
        sessionStorage.setItem(marker, message.sessionId);
        location.reload();
        return;
      }
      try {
        const game = await waitForGame();
        if (message.state) applyState(game, message.state);
        if (message.frame) applyFrame(game, message.frame);
        if (readyTimer) clearInterval(readyTimer);
        send("deductrium-observer-rendering");
      } catch (error) {
        send("deductrium-observer-error", { error: error.message });
      }
      return;
    }

    if (message.type === "deductrium-observer-state") {
      try { applyState(await waitForGame(), message.state); } catch { }
      return;
    }

    if (message.type === "deductrium-observer-frame") {
      try {
        applyFrame(await waitForGame(), message.frame);
        send("deductrium-observer-rendering");
      } catch { }
    }
  });

  addEventListener("DOMContentLoaded", () => {
    document.documentElement.style.overflow = "hidden";
    document.body.style.overflow = "hidden";
  });
  send("deductrium-observer-ready");
  readyTimer = setInterval(() => send("deductrium-observer-ready"), 500);
})();
