import { ListDragger } from "../fs/itemdragger.js";
import { TheoremWorkspaceLayoutItem } from "./theorem-workspace.js";

/**
 * DOM adapter shared by the theorem list and the type-theory sandbox.
 *
 * The workspace model owns ordering and folder semantics; this module only
 * translates that state into the small set of row attributes and layout
 * styles consumed by ListDragger and the existing CSS.
 */

export type WorkspaceRowOptions = {
    folder?: boolean;
    folderOpen?: boolean;
};

export function setWorkspaceRowData(
    row: HTMLElement,
    id: string,
    options: WorkspaceRowOptions = {}
) {
    row.dataset.dragRow = "true";
    row.dataset.dragId = id;
    if (options.folder === undefined) delete row.dataset.dragFolder;
    else row.dataset.dragFolder = String(options.folder);
    if (options.folderOpen === undefined) delete row.dataset.dragFolderOpen;
    else row.dataset.dragFolderOpen = String(options.folderOpen);
    return row;
}

export function workspaceRowId(row: HTMLElement) {
    return row.dataset.dragId ?? "";
}

export type WorkspaceDragHandleOptions = {
    dragger: ListDragger;
    title?: string;
    label?: string;
    rowOptions?: WorkspaceRowOptions;
};

/** Create and attach the canonical drag handle used by workspace rows. */
export function createWorkspaceDragHandle(
    row: HTMLElement,
    id: string,
    options: WorkspaceDragHandleOptions
) {
    setWorkspaceRowData(row, id, options.rowOptions);
    const handle = document.createElement("button");
    handle.type = "button";
    handle.className = "inhabitat-modify";
    handle.classList.add("tt-drag-handle", "idx");
    handle.innerText = options.label ?? "↕";
    handle.title = options.title ?? "拖动排序";
    row.appendChild(handle);
    options.dragger.attachIdxListener(handle);
    return handle;
}

/**
 * Put rows in model order while keeping an optional trailing control (usually
 * the add button) at the end of the container.
 */
export function syncWorkspaceDomOrder(
    container: HTMLElement,
    rows: readonly HTMLElement[],
    trailing: Node | null = null
) {
    let nextSibling: Node | null = trailing;
    for (let index = rows.length - 1; index >= 0; index--) {
        const row = rows[index];
        if (row.parentElement !== container || row.nextSibling !== nextSibling) {
            container.insertBefore(row, nextSibling);
        }
        nextSibling = row;
    }
}

export type WorkspaceLayoutRowHandler = (
    row: HTMLElement,
    state: TheoremWorkspaceLayoutItem
) => void;

/** Apply visibility, disabled state, and folder indentation to workspace rows. */
export function applyWorkspaceLayout(
    rows: Iterable<HTMLElement>,
    layout: readonly TheoremWorkspaceLayoutItem[],
    onRow?: WorkspaceLayoutRowHandler
) {
    const states = new Map(layout.map(item => [item.id, item] as const));
    for (const row of rows) {
        const id = workspaceRowId(row);
        if (!id) continue;
        const state = states.get(id);
        if (!state) continue;
        row.classList.toggle("hide", state.hidden);
        row.classList.toggle("tt-folder-disabled", state.disabled);
        row.dataset.dragDepth = String(state.depth);
        row.style.setProperty("--tt-folder-depth", String(state.depth));
        onRow?.(row, state);
    }
}
