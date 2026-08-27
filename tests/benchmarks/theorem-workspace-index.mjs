import { performance } from "node:perf_hooks";

import { TheoremWorkspace } from "../../js/tt/theorem-workspace.js";

const theoremCount = Math.max(1, Number(process.env.TT_WORKSPACE_BENCHMARK_THEOREMS) || 20000);
const folderCount = Math.max(1, Number(process.env.TT_WORKSPACE_BENCHMARK_FOLDERS) || 40);
const telescopeDepth = Math.max(1, Number(process.env.TT_WORKSPACE_BENCHMARK_DEPTH) || 1200);
const perFolder = Math.ceil(theoremCount / folderCount);
const flatItems = [];

for (let folderIndex = 0; folderIndex < folderCount; folderIndex++) {
    const start = folderIndex * perFolder;
    const end = Math.min(theoremCount, start + perFolder);
    flatItems.push({
        kind: "folder",
        id: `folder-${folderIndex}`,
        name: `Folder ${folderIndex}`,
        length: end - start,
        open: true,
        disabled: false
    });
    for (let theoremIndex = start; theoremIndex < end; theoremIndex++) {
        flatItems.push({
            kind: "theorem",
            id: `theorem-${theoremIndex}`,
            value: `theorem_${theoremIndex}`,
            local: true
        });
    }
}

const start = performance.now();
const workspace = new TheoremWorkspace(flatItems);
const derivedAt = performance.now();
let visible = 0;
for (let theoremIndex = 0; theoremIndex < workspace.theoremCount; theoremIndex++) {
    const folderId = `folder-${Math.min(folderCount - 1, Math.floor(theoremIndex / perFolder))}`;
    if (workspace.isTheoremInScope(theoremIndex, folderId)) visible++;
}
const queriedAt = performance.now();
const move = workspace.move("folder-0", "inside:folder-1");
const movedAt = performance.now();

const telescopeItems = Array.from({ length: telescopeDepth }, (_, index) => ({
    kind: "folder",
    id: `scope-${index}`,
    name: `Scope ${index}`,
    length: telescopeDepth - index,
    open: true,
    disabled: false
}));
telescopeItems.push({ kind: "theorem", id: "scope-leaf", value: "scope_leaf", local: true });
const telescopeStart = performance.now();
const telescope = new TheoremWorkspace(telescopeItems);
const scopeDepth = telescope.folderScopesForItem("scope-leaf").length;
const telescopeAt = performance.now();

console.log(JSON.stringify({
    theorems: workspace.theoremCount,
    folders: folderCount,
    visible,
    move: {
        changed: move.changed,
        revalidateFrom: move.revalidateFrom,
        revalidateTo: move.revalidateTo
    },
    telescopeDepth: scopeDepth,
    timingsMs: {
        derive: Number((derivedAt - start).toFixed(2)),
        indexedScopeQueries: Number((queriedAt - derivedAt).toFixed(2)),
        contiguousFolderMove: Number((movedAt - queriedAt).toFixed(2)),
        telescopeIndexAndScope: Number((telescopeAt - telescopeStart).toFixed(2))
    }
}));
