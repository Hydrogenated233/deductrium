export function setWorkspaceRowData(row, id, options = {}) {
    row.dataset.dragRow = "true";
    row.dataset.dragId = id;
    if (options.folder === undefined)
        delete row.dataset.dragFolder;
    else
        row.dataset.dragFolder = String(options.folder);
    if (options.folderOpen === undefined)
        delete row.dataset.dragFolderOpen;
    else
        row.dataset.dragFolderOpen = String(options.folderOpen);
    return row;
}
export function workspaceRowId(row) {
    return row.dataset.dragId ?? "";
}
/** Create and attach the canonical drag handle used by workspace rows. */
export function createWorkspaceDragHandle(row, id, options) {
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
export function syncWorkspaceDomOrder(container, rows, trailing = null) {
    let nextSibling = trailing;
    for (let index = rows.length - 1; index >= 0; index--) {
        const row = rows[index];
        if (row.parentElement !== container || row.nextSibling !== nextSibling) {
            container.insertBefore(row, nextSibling);
        }
        nextSibling = row;
    }
}
/** Apply visibility, disabled state, and folder indentation to workspace rows. */
export function applyWorkspaceLayout(rows, layout, onRow) {
    const states = new Map(layout.map(item => [item.id, item]));
    for (const row of rows) {
        const id = workspaceRowId(row);
        if (!id)
            continue;
        const state = states.get(id);
        if (!state)
            continue;
        row.classList.toggle("hide", state.hidden);
        row.classList.toggle("tt-folder-disabled", state.disabled);
        row.dataset.dragDepth = String(state.depth);
        row.style.setProperty("--tt-folder-depth", String(state.depth));
        onRow?.(row, state);
    }
}
//# sourceMappingURL=theorem-workspace-view.js.map