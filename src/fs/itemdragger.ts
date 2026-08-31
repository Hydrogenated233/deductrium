export function filterDragCandidates<T>(
    candidates: readonly T[],
    getName: (candidate: T) => string,
    excludedNames: ReadonlySet<string>
) {
    if (!excludedNames?.size) return [...candidates];
    return candidates.filter(candidate => !excludedNames.has(getName(candidate)));
}

export function isWithinDragBlock(
    bounds: readonly Pick<DOMRect, "top" | "bottom">[],
    clientY: number
) {
    if (!bounds.length) return false;
    const top = Math.min(...bounds.map(bound => bound.top));
    const bottom = Math.max(...bounds.map(bound => bound.bottom));
    return clientY >= top && clientY <= bottom;
}

export type DragHitRow = {
    name: string;
    top: number;
    bottom: number;
    folder?: boolean;
    folderOpen?: boolean;
    /** Depth in the flattened workspace tree. */
    depth?: number;
};

export type DragHitResult = {
    destination: string;
    kind: "noop" | "top" | "after" | "inside" | "bottom";
};

/**
 * Resolve a pointer position to the same destination grammar used by the
 * workspace.  A row has a small "before" band and an "after" band.  Folder
 * rows deliberately do not produce `inside:` destinations: dropping on a
 * folder must not silently append to its tail.  Dropping below a child row
 * still uses `after:` and therefore preserves that child's folder scope.
 */
export function resolveDragDestination(
    rows: readonly DragHitRow[],
    clientY: number
): DragHitResult {
    if (!rows.length) return { destination: " ", kind: "bottom" };

    const isFirstVisibleChild = (index: number) => {
        const row = rows[index];
        const previous = rows[index - 1];
        if (!previous?.folder || previous.folderOpen === false) return false;
        if (row.depth === undefined && previous.depth === undefined) return true;
        return row.depth !== undefined
            && previous.depth !== undefined
            && row.depth === previous.depth + 1;
    };
    const before = (index: number): DragHitResult => {
        if (index > 0 && isFirstVisibleChild(index)) {
            return { destination: `after:${rows[index - 1].name}`, kind: "after" };
        }
        return { destination: rows[index].name, kind: "top" };
    };
    const after = (row: DragHitRow): DragHitResult => ({
        destination: row.folder && !row.folderOpen
            ? `after-subtree:${row.name}`
            : `after:${row.name}`,
        kind: "after"
    });

    // A malformed/stale layout can briefly leave overlapping rectangles. Use
    // the deepest (then smallest/closest) row instead of allowing an outer
    // folder to capture a pointer that is visibly over an inner row.
    const containing = rows
        .map((row, index) => ({ row, index }))
        .filter(({ row, index }) => clientY >= row.top
            && (clientY < row.bottom || (index === rows.length - 1 && clientY <= row.bottom)));
    if (containing.length) {
        containing.sort((a, b) => {
            const depthA = Number.isFinite(a.row.depth) ? a.row.depth! : -1;
            const depthB = Number.isFinite(b.row.depth) ? b.row.depth! : -1;
            if (depthA !== depthB) return depthB - depthA;
            const heightA = a.row.bottom - a.row.top;
            const heightB = b.row.bottom - b.row.top;
            if (heightA !== heightB) return heightA - heightB;
            const centerA = Math.abs(clientY - (a.row.top + a.row.bottom) / 2);
            const centerB = Math.abs(clientY - (b.row.top + b.row.bottom) / 2);
            return centerA - centerB;
        });
        const { row, index } = containing[0];
        if (row.folder) return after(row);
        const height = Math.max(1, row.bottom - row.top);
        const topBand = Math.max(3, Math.min(8, height * 0.25));
        return clientY < row.top + topBand ? before(index) : after(row);
    }

    const nextIndex = rows.findIndex(row => clientY < row.top);
    if (nextIndex >= 0) return before(nextIndex);
    return after(rows[rows.length - 1]);
}

export class ListDragger {
    list: HTMLElement;
    constructor(list: HTMLElement) {
        this.list = list;
    }
    cols = 8;
    srcName: string = null;
    dstName: string = null;
    dragging = false;
    moved = false;
    onExecute: (src: string, dst: string) => void = () => { };
    queryAllowDrag: () => boolean = () => true;
    /** Rows that move together with the selected row, such as a folder subtree. */
    queryDraggedNames: ((src: string) => Iterable<string>) | null = null;
    startY = 0;
    private draggedNames = new Set<string>();
    private readonly mouseMoveListener = (event: MouseEvent) => this.onMove(event);
    private readonly mouseUpListener = () => this.onUp();
    private readonly touchMoveListener = (event: TouchEvent) => this.onTouchMove(event);
    private readonly touchEndListener = () => this.onTouchEnd();
    attachIdxListener(dom?: HTMLElement) {
        const cb = (idx: HTMLElement) => {
            idx.onmousedown = null;
            idx.onmousedown = (ev) => {
                ev.preventDefault();
                this.startDrag(idx, ev as MouseEvent);
            };
            idx.ontouchstart = (te) => {
                const touch = te.touches[0];
                const startX = touch.clientX;
                const startY = touch.clientY;
                let longPressTimer: number | null = null;
                let moved = false;
                longPressTimer = window.setTimeout(() => {
                    if (!moved) {
                        this.startDrag(idx, { clientX: startX, clientY: startY } as MouseEvent);
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

                const moveCheck = (ev: TouchEvent) => {
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
            this.list.querySelectorAll<HTMLElement>('.idx').forEach(cb);
        } else {
            cb(dom);
        }
    }
    update() {
        this.attachIdxListener();
    }

    private getRowElement(element: HTMLElement) {
        return element.closest<HTMLElement>("[data-drag-row]") ?? element;
    }

    private getRowName(element: HTMLElement) {
        return element.dataset.dragId ?? element.innerText;
    }

    startDrag(idxEl: HTMLElement, ev: MouseEvent) {
        this.moved = false;
        if (this.queryAllowDrag && !this.queryAllowDrag()) return;
        idxEl = this.getRowElement(idxEl);
        const allChildren = Array.from(this.list.children) as HTMLElement[];
        const childIndex = allChildren.indexOf(idxEl);
        if (childIndex === -1) return;

        const rowStart = Math.floor(childIndex / this.cols) * this.cols;
        for (let i = 0; i < this.cols; i++) {
            const el = allChildren[rowStart + i] as HTMLElement | undefined;
            if (!el) continue;
            el.classList.add("dragging");
        }
        this.dragging = true;
        this.startY = ev.clientY;
        this.srcName = this.getRowName(idxEl);
        this.draggedNames = new Set(this.queryDraggedNames?.(this.srcName) ?? []);

        document.addEventListener('mousemove', this.mouseMoveListener);
        document.addEventListener('mouseup', this.mouseUpListener);
        document.addEventListener('touchmove', this.touchMoveListener, { passive: false });
        document.addEventListener('touchend', this.touchEndListener);
    }

    onTouchMove(e: TouchEvent) {
        if (!this.dragging) return;
        e.preventDefault();
        const t = e.touches[0];
        this.onMove({ clientX: t.clientX, clientY: t.clientY } as unknown as MouseEvent);
    }
    onTouchEnd() {
        this.onUp();
    }

    onMove(e: MouseEvent) {
        if (!this.dragging) return;
        this.moved = true;
        const visibleChildren = (Array.from(this.list.children) as HTMLElement[]).filter(
            element => !element.hasAttribute("data-drag-row") || !element.classList.contains("hide")
        );
        const draggedRows = visibleChildren.filter(element => this.draggedNames.has(this.getRowName(element)));
        const candidateChildren = this.queryDraggedNames === null
            ? visibleChildren
            : visibleChildren.filter(element => element.dataset.dragRow === "true");
        const children = filterDragCandidates(
            candidateChildren,
            element => this.getRowName(element),
            this.draggedNames
        );
        const rowCount = Math.ceil(children.length / this.cols);

        this.list.querySelectorAll(".dragging-bottom, .dragging-top, .dragging-inside").forEach(e => {
            e.classList.remove("dragging-bottom");
            e.classList.remove("dragging-top");
            e.classList.remove("dragging-inside");
        });

        // The inference-layer lists still use the historical multi-column
        // drag behavior.  Only theorem/sandbox workspaces opt into the
        // subtree-aware before/after destinations below.
        if (this.queryDraggedNames === null) {
            let inserted = false;
            for (let r = 0; r < rowCount; r++) {
                const firstChild = children[r * this.cols];
                if (!firstChild) continue;
                const rect = firstChild.getBoundingClientRect();
                const midY = rect.top + rect.height / 2;
                if (e.clientY < midY) {
                    this.dstName = this.getRowName(firstChild);
                    firstChild.classList.add("dragging-top");
                    inserted = true;
                    break;
                }
                if (
                    firstChild.dataset.dragFolder === "true"
                    && firstChild.dataset.dragFolderOpen === "true"
                    && e.clientY <= rect.bottom
                ) {
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
            return;
        }

        const candidates = [] as DragHitRow[];
        const elementsByName = new Map<string, HTMLElement>();
        for (let r = 0; r < rowCount; r++) {
            const firstChild = children[r * this.cols];
            if (!firstChild) continue;
            const rect = firstChild.getBoundingClientRect();
            const name = this.getRowName(firstChild);
            const depth = Number.parseInt(firstChild.dataset.dragDepth ?? "", 10);
            candidates.push({
                name,
                top: rect.top,
                bottom: rect.bottom,
                folder: firstChild.dataset.dragFolder === "true",
                folderOpen: firstChild.dataset.dragFolderOpen === "true",
                depth: Number.isFinite(depth) ? depth : undefined
            });
            elementsByName.set(name, firstChild);
        }
        const result = this.srcName && isWithinDragBlock(
            draggedRows.map(row => row.getBoundingClientRect()),
            e.clientY
        )
            ? { destination: this.srcName, kind: "noop" as const }
            : resolveDragDestination(candidates, e.clientY);
        this.dstName = result.destination;
        if (result.kind === "top") {
            elementsByName.get(result.destination)?.classList.add("dragging-top");
        } else if (result.kind === "after") {
            const targetName = result.destination.startsWith("after-subtree:")
                ? result.destination.slice("after-subtree:".length)
                : result.destination.slice("after:".length);
            elementsByName.get(targetName)?.classList.add("dragging-bottom");
        } else if (result.kind === "inside") {
            // Kept for callers that provide a legacy destination, but the
            // pointer resolver above no longer generates this state.
            elementsByName.get(result.destination.slice("inside:".length))?.classList.add("dragging-inside");
        } else if (result.kind === "bottom") {
            children[(rowCount - 1) * this.cols]?.classList.add("dragging-bottom");
        }
    }

    onUp() {
        if (!this.dragging) return;
        this.dragging = false;
        this.list.querySelectorAll(".dragging, .dragging-bottom, .dragging-top, .dragging-inside").forEach(e => {
            e.classList.remove("dragging-bottom");
            e.classList.remove("dragging-top");
            e.classList.remove("dragging-inside");
            e.classList.remove("dragging");
        });
        if (this.moved) this.onExecute(this.srcName, this.dstName);
        this.moved = false;
        this.srcName = null;
        this.dstName = null;
        this.draggedNames.clear();
        document.removeEventListener('mousemove', this.mouseMoveListener);
        document.removeEventListener('mouseup', this.mouseUpListener);
        document.removeEventListener('touchmove', this.touchMoveListener);
        document.removeEventListener('touchend', this.touchEndListener);

    }
}
