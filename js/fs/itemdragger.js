export class ListDragger {
    list;
    constructor(list) {
        this.list = list;
    }
    cols = 8;
    srcName = null;
    dstName = null;
    dragging = false;
    moved = false;
    onExecute = () => { };
    queryAllowDrag = () => true;
    startY = 0;
    mouseMoveListener = (event) => this.onMove(event);
    mouseUpListener = () => this.onUp();
    touchMoveListener = (event) => this.onTouchMove(event);
    touchEndListener = () => this.onTouchEnd();
    attachIdxListener(dom) {
        const cb = (idx) => {
            idx.onmousedown = null;
            idx.onmousedown = (ev) => {
                ev.preventDefault();
                this.startDrag(idx, ev);
            };
            idx.ontouchstart = (te) => {
                const touch = te.touches[0];
                const startX = touch.clientX;
                const startY = touch.clientY;
                let longPressTimer = null;
                let moved = false;
                longPressTimer = window.setTimeout(() => {
                    if (!moved) {
                        this.startDrag(idx, { clientX: startX, clientY: startY });
                    }
                }, 300);
                const cancel = () => {
                    if (longPressTimer) {
                        clearTimeout(longPressTimer);
                        longPressTimer = null;
                    }
                    document.removeEventListener("touchmove", moveCheck);
                    document.removeEventListener("touchend", cancel);
                    document.removeEventListener("touchcancel", cancel);
                };
                const moveCheck = (ev) => {
                    const t = ev.touches[0];
                    const dx = t.clientX - startX;
                    const dy = t.clientY - startY;
                    if (Math.abs(dx) > 5 || Math.abs(dy) > 5) {
                        moved = true;
                        cancel();
                    }
                };
                document.addEventListener("touchmove", moveCheck);
                document.addEventListener("touchend", cancel);
                document.addEventListener("touchcancel", cancel);
            };
        };
        if (!dom) {
            this.list.querySelectorAll('.idx').forEach(cb);
        }
        else {
            cb(dom);
        }
    }
    update() {
        this.attachIdxListener();
    }
    getRowElement(element) {
        return element.closest("[data-drag-row]") ?? element;
    }
    getRowName(element) {
        return element.dataset.dragId ?? element.innerText;
    }
    startDrag(idxEl, ev) {
        this.moved = false;
        if (this.queryAllowDrag && !this.queryAllowDrag())
            return;
        idxEl = this.getRowElement(idxEl);
        const allChildren = Array.from(this.list.children);
        const childIndex = allChildren.indexOf(idxEl);
        if (childIndex === -1)
            return;
        const rowStart = Math.floor(childIndex / this.cols) * this.cols;
        for (let i = 0; i < this.cols; i++) {
            const el = allChildren[rowStart + i];
            if (!el)
                continue;
            el.classList.add("dragging");
        }
        this.dragging = true;
        this.startY = ev.clientY;
        this.srcName = this.getRowName(idxEl);
        document.addEventListener('mousemove', this.mouseMoveListener);
        document.addEventListener('mouseup', this.mouseUpListener);
        document.addEventListener('touchmove', this.touchMoveListener, { passive: false });
        document.addEventListener('touchend', this.touchEndListener);
    }
    onTouchMove(e) {
        if (!this.dragging)
            return;
        e.preventDefault();
        const t = e.touches[0];
        this.onMove({ clientX: t.clientX, clientY: t.clientY });
    }
    onTouchEnd() {
        this.onUp();
    }
    onMove(e) {
        if (!this.dragging)
            return;
        this.moved = true;
        const children = Array.from(this.list.children).filter(element => !element.hasAttribute("data-drag-row") || !element.classList.contains("hide"));
        const rowCount = Math.ceil(children.length / this.cols);
        let inserted = false;
        this.list.querySelectorAll(".dragging-bottom, .dragging-top, .dragging-inside").forEach(e => {
            e.classList.remove("dragging-bottom");
            e.classList.remove("dragging-top");
            e.classList.remove("dragging-inside");
        });
        for (let r = 0; r < rowCount; r++) {
            const firstIndex = r * this.cols;
            const firstChild = children[firstIndex];
            if (!firstChild)
                continue;
            const rect = firstChild.getBoundingClientRect();
            const midY = rect.top + rect.height / 2;
            if (e.clientY < midY) {
                this.dstName = this.getRowName(firstChild);
                firstChild.classList.add("dragging-top");
                inserted = true;
                break;
            }
            if (firstChild.dataset.dragFolder === "true"
                && firstChild.dataset.dragFolderOpen === "true"
                && e.clientY <= rect.bottom) {
                this.dstName = "inside:" + this.getRowName(firstChild);
                firstChild.classList.add("dragging-inside");
                inserted = true;
                break;
            }
        }
        if (!inserted) {
            this.dstName = " ";
            children[(rowCount - 1) * this.cols]?.classList.add("dragging-bottom");
        }
    }
    onUp() {
        if (!this.dragging)
            return;
        this.dragging = false;
        this.list.querySelectorAll(".dragging, .dragging-bottom, .dragging-top, .dragging-inside").forEach(e => {
            e.classList.remove("dragging-bottom");
            e.classList.remove("dragging-top");
            e.classList.remove("dragging-inside");
            e.classList.remove("dragging");
        });
        if (this.moved)
            this.onExecute(this.srcName, this.dstName);
        this.moved = false;
        this.srcName = null;
        this.dstName = null;
        document.removeEventListener('mousemove', this.mouseMoveListener);
        document.removeEventListener('mouseup', this.mouseUpListener);
        document.removeEventListener('touchmove', this.touchMoveListener);
        document.removeEventListener('touchend', this.touchEndListener);
    }
}
//# sourceMappingURL=itemdragger.js.map