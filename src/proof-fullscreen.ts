const installed = new WeakSet<HTMLElement>();

/** Resize the existing editor without remounting its proof or input nodes. */
export function installProofFullscreen(host: HTMLElement | null, button: HTMLElement | null): void {
    if (!host || !button || installed.has(host)) return;
    installed.add(host);
    const doc = host.ownerDocument;
    let active = false;
    let pending = false;
    let native = false;
    let exitAfterPending = false;
    let scrollTop = 0;
    let scrollLeft = 0;
    let previousOverflow = "";

    const paint = () => {
        button.setAttribute("aria-pressed", String(active));
        button.setAttribute("aria-label", active ? "\u9000\u51fa\u5168\u5c4f" : "\u5168\u5c4f\u8bc1\u660e\u52a9\u624b");
        button.setAttribute("title", active ? "\u9000\u51fa\u5168\u5c4f (Esc)" : "\u5168\u5c4f\u8bc1\u660e\u52a9\u624b");
        button.textContent = active ? "\u2199" : "\u26f6";
    };
    const leave = () => {
        if (!active) return;
        active = false;
        native = false;
        host.classList.remove("proof-assistant-fullscreen");
        doc.body.style.overflow = previousOverflow;
        host.scrollTop = scrollTop;
        host.scrollLeft = scrollLeft;
        paint();
        button.focus({ preventScroll: true });
    };
    const exit = async () => {
        if (pending) return;
        pending = true;
        try {
            if (doc.fullscreenElement === host) await doc.exitFullscreen();
            leave();
        } catch {
            // Keep the exit control usable if the browser refuses this request.
            if (doc.fullscreenElement !== host) leave();
        } finally {
            pending = false;
            if (exitAfterPending) {
                exitAfterPending = false;
                void exit();
            }
        }
    };
    button.addEventListener("click", async () => {
        if (pending) return;
        if (active) return void exit();
        active = true;
        pending = true;
        scrollTop = host.scrollTop;
        scrollLeft = host.scrollLeft;
        previousOverflow = doc.body.style.overflow;
        doc.body.style.overflow = "hidden";
        host.classList.add("proof-assistant-fullscreen");
        paint();
        try {
            if (doc.fullscreenEnabled && host.requestFullscreen) {
                await host.requestFullscreen();
                native = doc.fullscreenElement === host;
            }
        } catch {
            // Embedded browsers may deny native fullscreen; the viewport layout remains usable.
        } finally {
            pending = false;
            if (exitAfterPending) {
                exitAfterPending = false;
                void exit();
            }
        }
    });
    doc.addEventListener("fullscreenchange", () => {
        if (doc.fullscreenElement === host) native = true;
        else if (native) leave();
    });
    doc.addEventListener("keydown", event => {
        if (!active || event.key !== "Escape") return;
        event.preventDefault();
        event.stopImmediatePropagation();
        if (pending) {
            exitAfterPending = true;
            return;
        }
        void exit();
    }, true);
    paint();
}
