/**
 * DOM-free ordered theorem workspace.
 *
 * The workspace owns ordering and folder rules. Rendering, theorem caches,
 * and validation execution are adapters around this module.
 */

export type TheoremWorkspaceSaveItem =
    | { kind: "theorem", value: string, local?: boolean }
    | { kind: "folder", id: string, name: string, length: number, open: boolean, disabled: boolean };

export type TheoremWorkspaceTheorem = {
    kind: "theorem";
    id: string;
    value: string;
    local: boolean;
};

export type TheoremWorkspaceFolder = {
    kind: "folder";
    id: string;
    name: string;
    length: number;
    open: boolean;
    disabled: boolean;
};

export type TheoremWorkspaceItem = TheoremWorkspaceTheorem | TheoremWorkspaceFolder;

export type TheoremWorkspaceRange = {
    startIndex: number;
    endIndex: number;
    startTheoremIndex: number;
    endTheoremIndex: number;
};

export type TheoremWorkspaceMutation = {
    changed: boolean;
    structureChanged: boolean;
    definitionsChanged: boolean;
    revalidateFrom: number | null;
    /**
     * The directly moved/changed theorem interval. Consumers that need a
     * complete definition rebuild must still start at revalidateFrom.
     */
    revalidateTo: number | null;
    snapshot: TheoremWorkspaceItem[];
};

export type TheoremWorkspaceLayoutItem = {
    id: string;
    depth: number;
    hidden: boolean;
    disabled: boolean;
    canBeLocal: boolean;
};

type FolderEntry = {
    id: string;
    /** Inclusive item index of the folder's final descendant. */
    endItemIndex: number;
    descendantsHidden: boolean;
    descendantsDisabled: boolean;
};

type WorkspaceItemIndex = {
    itemIndex: number;
    parentFolderId: string | null;
    /** Folder owning the item's scope; a folder owns its own scope. */
    scopeFolderId: string | null;
    hidden: boolean;
    disabled: boolean;
};

type WorkspaceFolderIndex = {
    itemIndex: number;
    /** Exclusive item index after the folder subtree. */
    endIndex: number;
    parentFolderId: string | null;
};

/**
 * Rebuilt once for each structural revision. The index deliberately stores
 * parent links instead of copying every ancestor stack into every row: a
 * telescope of folders remains O(n) in both time and memory.
 */
type TheoremWorkspaceDerived = {
    revision: number;
    itemIndexById: Map<string, number>;
    itemInfoById: Map<string, WorkspaceItemIndex>;
    folderInfoById: Map<string, WorkspaceFolderIndex>;
    theoremItemIndices: number[];
    theoremPrefixCounts: number[];
    /** Immediate folder owner of the insertion boundary before each item. */
    insertionParentFolderIds: (string | null)[];
    layout: TheoremWorkspaceLayoutItem[];
};

function cloneItem(item: TheoremWorkspaceItem): TheoremWorkspaceItem {
    return item.kind === "theorem"
        ? { kind: "theorem", id: item.id, value: item.value, local: item.local }
        : {
            kind: "folder",
            id: item.id,
            name: item.name,
            length: item.length,
            open: item.open,
            disabled: item.disabled
        };
}

type TheoremWorkspaceInput = TheoremWorkspaceSaveItem | TheoremWorkspaceItem;

function itemFromSave(item: TheoremWorkspaceInput, fallbackId: string): TheoremWorkspaceItem {
    if (item.kind === "folder") {
        return {
            kind: "folder",
            id: item.id,
            name: item.name,
            length: Number(item.length) || 0,
            open: item.open !== false,
            disabled: !!item.disabled
        };
    }
    return {
        kind: "theorem",
        id: "id" in item && item.id ? item.id : fallbackId,
        value: String(item.value ?? ""),
        local: !!item.local
    };
}

export class TheoremWorkspace {
    private items: TheoremWorkspaceItem[] = [];
    private derived: TheoremWorkspaceDerived | null = null;
    private revision = 0;

    constructor(items: readonly TheoremWorkspaceInput[] = []) {
        this.replace(items);
    }

    replace(items: readonly TheoremWorkspaceInput[]) {
        this.items = items.map((item, index) => itemFromSave(item, `theorem-${index + 1}`));
        this.normalizeFolderLengths();
        return this.snapshot();
    }

    snapshot(): TheoremWorkspaceItem[] {
        return this.items.map(cloneItem);
    }

    serialize(): TheoremWorkspaceSaveItem[] {
        return this.items.map(item => item.kind === "theorem"
            ? { kind: "theorem", value: item.value, local: item.local }
            : {
                kind: "folder",
                id: item.id,
                name: item.name,
                length: item.length,
                open: item.open,
                disabled: item.disabled
            });
    }

    get itemCount() {
        return this.items.length;
    }

    get theoremCount() {
        return this.getDerived().theoremItemIndices.length;
    }

    findItemIndex(id: string | null | undefined) {
        return id ? this.getDerived().itemIndexById.get(id) ?? -1 : -1;
    }

    theoremIndexBeforeItem(itemIndex: number) {
        const end = Math.max(0, Math.min(Math.floor(itemIndex), this.items.length));
        return this.getDerived().theoremPrefixCounts[end] ?? 0;
    }

    itemIndexForTheorem(theoremIndex: number) {
        const target = Math.max(0, Math.floor(theoremIndex));
        return this.getDerived().theoremItemIndices[target] ?? this.items.length;
    }

    folderRange(folderId: string | null | undefined): TheoremWorkspaceRange | null {
        if (!folderId) return null;
        const derived = this.getDerived();
        const folder = derived.folderInfoById.get(folderId);
        if (!folder) return null;
        return {
            startIndex: folder.itemIndex,
            endIndex: folder.endIndex,
            startTheoremIndex: derived.theoremPrefixCounts[folder.itemIndex] ?? 0,
            endTheoremIndex: derived.theoremPrefixCounts[folder.endIndex] ?? 0
        };
    }

    folderScopesForItems(ids: readonly (string | null | undefined)[]) {
        const derived = this.getDerived();
        const result = new Map<string, TheoremWorkspaceFolder[]>();
        for (const id of new Set(ids)) {
            if (!id || !derived.itemInfoById.has(id)) continue;
            result.set(id, this.cloneFolderScope(this.itemScopeFolderIds(id, derived), derived));
        }
        return result;
    }

    folderScopesForItem(id: string | null | undefined) {
        return this.folderScopesForItems([id]).get(id ?? "") ?? [];
    }

    folderPath(folderId: string | null | undefined) {
        if (!folderId) return "";
        const derived = this.getDerived();
        return this.folderScopeIds(folderId, derived)
            .map(id => this.folderItem(id, derived)?.name ?? "")
            .filter(Boolean)
            .join(" / ");
    }

    folderAppendIndex(folderId: string | null | undefined) {
        return this.folderRange(folderId)?.endIndex ?? -1;
    }

    layout(): TheoremWorkspaceLayoutItem[] {
        return this.getDerived().layout.map(item => ({ ...item }));
    }

    isTheoremDisabled(theoremIndex: number) {
        const itemIndex = this.itemIndexForTheorem(theoremIndex);
        if (itemIndex >= this.items.length) return false;
        const id = this.items[itemIndex]?.id;
        return !!id && (this.getDerived().itemInfoById.get(id)?.disabled ?? false);
    }

    isTheoremInScope(theoremIndex: number, selectedFolderId: string | null = null) {
        const itemIndex = this.itemIndexForTheorem(theoremIndex);
        const item = this.items[itemIndex];
        if (!item || item.kind !== "theorem") return false;
        const derived = this.getDerived();
        const info = derived.itemInfoById.get(item.id);
        if (!info || info.disabled) return false;
        if (!item.local) return true;
        return !!selectedFolderId
            && !!info.parentFolderId
            && this.folderContains(info.parentFolderId, selectedFolderId, derived);
    }

    isTheoremVisible(
        theoremIndex: number,
        targetTheoremIndex: number,
        selectedFolderId: string | null = null,
        hasDefinition = true
    ) {
        return hasDefinition
            && theoremIndex < targetTheoremIndex
            && this.isTheoremInScope(theoremIndex, selectedFolderId);
    }

    updateTheorem(id: string, patch: Partial<Pick<TheoremWorkspaceTheorem, "value" | "local">>) {
        const derived = this.getDerived();
        const info = derived.itemInfoById.get(id);
        const item = info ? this.items[info.itemIndex] : null;
        if (!item || item.kind !== "theorem") return this.result(false, false, false, null);
        const valueChanged = patch.value !== undefined && item.value !== patch.value;
        const localChanged = patch.local !== undefined && item.local !== !!patch.local;
        if (valueChanged) item.value = String(patch.value);
        if (localChanged) item.local = !!patch.local;
        const changed = valueChanged || localChanged;
        const theoremIndex = derived.theoremPrefixCounts[info.itemIndex] ?? 0;
        return this.result(changed, false, changed, theoremIndex, changed ? theoremIndex + 1 : null);
    }

    setFolderOpen(id: string, open: boolean) {
        const folder = this.folderItem(id);
        if (!folder || folder.open === !!open) return this.result(false, false, false, null);
        folder.open = !!open;
        this.invalidateDerived();
        return this.result(true, true, false, null);
    }

    setFolderDisabled(id: string, disabled: boolean) {
        const range = this.folderRange(id);
        const folder = this.folderItem(id);
        if (!folder || folder.disabled === !!disabled) return this.result(false, false, false, null);
        folder.disabled = !!disabled;
        this.invalidateDerived();
        const changed = !!range && range.endTheoremIndex > range.startTheoremIndex;
        return this.result(
            true,
            true,
            changed,
            changed ? range!.startTheoremIndex : null,
            changed ? range!.endTheoremIndex : null
        );
    }

    renameFolder(id: string, name: string) {
        const folder = this.folderItem(id);
        if (!folder || !name || folder.name === name) return this.result(false, false, false, null);
        folder.name = name;
        return this.result(true, true, false, null);
    }

    insertTheorem(
        item: TheoremWorkspaceTheorem,
        itemIndex = this.items.length,
        parentFolderId?: string | null
    ) {
        const index = this.clampItemIndex(itemIndex);
        const derived = this.getDerived();
        if (derived.itemIndexById.has(item.id)) return this.result(false, false, false, null);
        const theoremIndex = derived.theoremPrefixCounts[index] ?? 0;
        this.applyFolderLengthDelta(
            this.folderScopeIds(this.insertionParentFolderId(index, parentFolderId, derived), derived),
            1,
            derived
        );
        this.items.splice(index, 0, cloneItem(item));
        this.normalizeFolderLengths();
        return this.result(true, true, true, theoremIndex, theoremIndex + 1);
    }

    insertFolder(
        item: TheoremWorkspaceFolder,
        itemIndex = this.items.length,
        parentFolderId?: string | null
    ) {
        const index = this.clampItemIndex(itemIndex);
        const derived = this.getDerived();
        if (derived.itemIndexById.has(item.id)) return this.result(false, false, false, null);
        this.applyFolderLengthDelta(
            this.folderScopeIds(this.insertionParentFolderId(index, parentFolderId, derived), derived),
            1,
            derived
        );
        this.items.splice(index, 0, cloneItem(item));
        this.normalizeFolderLengths();
        return this.result(true, true, false, null);
    }

    removeTheorem(id: string) {
        const derived = this.getDerived();
        const info = derived.itemInfoById.get(id);
        const item = info ? this.items[info.itemIndex] : null;
        if (!item || item.kind !== "theorem") return this.result(false, false, false, null);
        const theoremIndex = derived.theoremPrefixCounts[info.itemIndex] ?? 0;
        this.applyFolderLengthDelta(this.itemScopeFolderIds(id, derived), -1, derived);
        this.items.splice(info.itemIndex, 1);
        this.normalizeFolderLengths();
        return this.result(true, true, true, theoremIndex, theoremIndex + 1);
    }

    removeFolder(id: string) {
        const derived = this.getDerived();
        const info = derived.folderInfoById.get(id);
        if (!info) return this.result(false, false, false, null);
        const theoremIndex = derived.theoremPrefixCounts[info.itemIndex] ?? 0;
        const endTheoremIndex = derived.theoremPrefixCounts[info.endIndex] ?? theoremIndex;
        this.applyFolderLengthDelta(
            this.itemScopeFolderIds(id, derived).filter(folderId => folderId !== id),
            -1,
            derived
        );
        this.items.splice(info.itemIndex, 1);
        this.normalizeFolderLengths();
        return this.result(true, true, true, theoremIndex, endTheoremIndex);
    }

    move(srcId: string, destination: string) {
        const derived = this.getDerived();
        const sourceInfo = derived.itemInfoById.get(srcId);
        const source = sourceInfo ? this.items[sourceInfo.itemIndex] : null;
        if (!source || sourceInfo.hidden) return this.result(false, false, false, null);

        const srcIndex = sourceInfo.itemIndex;
        const sourceFolder = source.kind === "folder" ? derived.folderInfoById.get(srcId) : null;
        const movedItemCount = sourceFolder ? sourceFolder.endIndex - srcIndex : 1;
        const oldTheoremStart = derived.theoremPrefixCounts[srcIndex] ?? 0;
        const movedTheoremCount = (derived.theoremPrefixCounts[srcIndex + movedItemCount] ?? oldTheoremStart)
            - oldTheoremStart;

        const insideFolderId = destination.startsWith("inside:") ? destination.slice("inside:".length) : null;
        let destinationBoundary: number;
        let destinationParentFolderId: string | null;

        if (insideFolderId) {
            const folderInfo = derived.folderInfoById.get(insideFolderId);
            const folder = folderInfo ? this.items[folderInfo.itemIndex] : null;
            const folderItemInfo = derived.itemInfoById.get(insideFolderId);
            if (!folderInfo || !folder || folder.kind !== "folder" || !folderItemInfo
                || !folder.open || folderItemInfo.hidden) {
                return this.result(false, false, false, null);
            }
            if (folderInfo.itemIndex >= srcIndex && folderInfo.itemIndex < srcIndex + movedItemCount) {
                return this.result(false, false, false, null);
            }
            destinationBoundary = folderInfo.endIndex;
            destinationParentFolderId = insideFolderId;
        } else if (destination === " ") {
            destinationBoundary = this.items.length;
            destinationParentFolderId = derived.insertionParentFolderIds[destinationBoundary] ?? null;
        } else {
            const destinationInfo = derived.itemInfoById.get(destination);
            if (!destinationInfo || destinationInfo.hidden) return this.result(false, false, false, null);
            if (destinationInfo.itemIndex >= srcIndex && destinationInfo.itemIndex < srcIndex + movedItemCount) {
                return this.result(false, false, false, null);
            }
            destinationBoundary = destinationInfo.itemIndex;
            destinationParentFolderId = derived.insertionParentFolderIds[destinationBoundary] ?? null;
        }

        // The boundary is calculated against the pre-removal revision.
        const insertIndex = destinationBoundary - (srcIndex < destinationBoundary ? movedItemCount : 0);
        // A drop at the current item index can still change folder ownership:
        // appending the first row after a folder into that folder is one such
        // case. It is a true no-op only when its immediate parent is unchanged.
        if (insertIndex === srcIndex && sourceInfo.parentFolderId === destinationParentFolderId) {
            return this.result(false, false, false, null);
        }

        const folderLengthDeltas = new Map<string, number>();
        const addDelta = (folderIds: readonly string[], delta: number) => {
            for (const folderId of folderIds) {
                folderLengthDeltas.set(folderId, (folderLengthDeltas.get(folderId) ?? 0) + delta);
            }
        };
        addDelta(
            this.itemScopeFolderIds(srcId, derived).filter(folderId => folderId !== srcId),
            -movedItemCount
        );
        addDelta(this.folderScopeIds(destinationParentFolderId, derived), movedItemCount);

        this.applyFolderLengthDeltas(folderLengthDeltas, derived);
        const moving = this.items.splice(srcIndex, movedItemCount);
        this.items.splice(insertIndex, 0, ...moving);
        this.normalizeFolderLengths();

        const destinationTheoremIndex = derived.theoremPrefixCounts[destinationBoundary] ?? 0;
        const newTheoremStart = destinationTheoremIndex
            - (srcIndex < destinationBoundary ? movedTheoremCount : 0);
        const revalidateFrom = movedTheoremCount > 0
            ? Math.min(oldTheoremStart, newTheoremStart)
            : null;
        const revalidateTo = movedTheoremCount > 0
            ? Math.max(oldTheoremStart + movedTheoremCount, newTheoremStart + movedTheoremCount)
            : null;
        return this.result(true, true, movedTheoremCount > 0, revalidateFrom, revalidateTo);
    }

    private clampItemIndex(itemIndex: number) {
        return Math.max(0, Math.min(Math.floor(itemIndex), this.items.length));
    }

    private insertionParentFolderId(
        itemIndex: number,
        parentFolderId: string | null | undefined,
        derived: TheoremWorkspaceDerived
    ) {
        if (parentFolderId === null) return null;
        if (parentFolderId) return derived.folderInfoById.has(parentFolderId) ? parentFolderId : null;
        return derived.insertionParentFolderIds[itemIndex] ?? null;
    }

    private folderItem(id: string, derived = this.getDerived()) {
        const folderInfo = derived.folderInfoById.get(id);
        const item = folderInfo ? this.items[folderInfo.itemIndex] : null;
        return item?.kind === "folder" ? item : null;
    }

    private itemScopeFolderIds(id: string, derived: TheoremWorkspaceDerived) {
        return this.folderScopeIds(derived.itemInfoById.get(id)?.scopeFolderId ?? null, derived);
    }

    private folderScopeIds(folderId: string | null, derived: TheoremWorkspaceDerived) {
        const result: string[] = [];
        let cursor = folderId;
        while (cursor) {
            const folder = derived.folderInfoById.get(cursor);
            if (!folder) break;
            result.push(cursor);
            cursor = folder.parentFolderId;
        }
        result.reverse();
        return result;
    }

    private cloneFolderScope(ids: readonly string[], derived: TheoremWorkspaceDerived) {
        const result: TheoremWorkspaceFolder[] = [];
        for (const id of ids) {
            const folder = this.folderItem(id, derived);
            if (folder) result.push(cloneItem(folder) as TheoremWorkspaceFolder);
        }
        return result;
    }

    private folderContains(ancestorId: string, childId: string, derived: TheoremWorkspaceDerived) {
        const ancestor = derived.folderInfoById.get(ancestorId);
        const child = derived.folderInfoById.get(childId);
        return !!ancestor && !!child
            && ancestor.itemIndex <= child.itemIndex
            && child.itemIndex < ancestor.endIndex;
    }

    private applyFolderLengthDelta(folderIds: readonly string[], delta: number, derived: TheoremWorkspaceDerived) {
        const deltas = new Map<string, number>();
        for (const folderId of folderIds) deltas.set(folderId, delta);
        this.applyFolderLengthDeltas(deltas, derived);
    }

    private applyFolderLengthDeltas(deltas: ReadonlyMap<string, number>, derived: TheoremWorkspaceDerived) {
        for (const [id, delta] of deltas) {
            if (!delta) continue;
            const folder = this.folderItem(id, derived);
            if (folder) folder.length = Math.max(0, folder.length + delta);
        }
    }

    private normalizeFolderLengths() {
        this.invalidateDerived();
        for (let index = 0; index < this.items.length; index++) {
            const item = this.items[index];
            if (item.kind === "folder") {
                item.length = Math.max(0, Math.min(item.length, this.items.length - index - 1));
            }
        }
    }

    private invalidateDerived() {
        this.derived = null;
        this.revision++;
    }

    private getDerived(): TheoremWorkspaceDerived {
        if (this.derived?.revision === this.revision) return this.derived;
        const itemIndexById = new Map<string, number>();
        const itemInfoById = new Map<string, WorkspaceItemIndex>();
        const folderInfoById = new Map<string, WorkspaceFolderIndex>();
        const theoremItemIndices: number[] = [];
        const theoremPrefixCounts: number[] = [0];
        const insertionParentFolderIds: (string | null)[] = [];
        const layout: TheoremWorkspaceLayoutItem[] = [];
        const stack: FolderEntry[] = [];
        let theoremCount = 0;

        for (let index = 0; index <= this.items.length; index++) {
            while (stack.length && stack[stack.length - 1].endItemIndex < index) stack.pop();
            insertionParentFolderIds[index] = stack[stack.length - 1]?.id ?? null;
            if (index === this.items.length) break;

            const item = this.items[index];
            const parent = stack[stack.length - 1];
            const parentFolderId = parent?.id ?? null;
            const hidden = parent?.descendantsHidden ?? false;
            const inheritedDisabled = parent?.descendantsDisabled ?? false;
            const disabled = inheritedDisabled || (item.kind === "folder" && item.disabled);

            if (!itemIndexById.has(item.id)) itemIndexById.set(item.id, index);
            if (item.kind === "folder") {
                const endIndex = Math.min(this.items.length, index + Math.max(0, item.length) + 1);
                itemInfoById.set(item.id, {
                    itemIndex: index,
                    parentFolderId,
                    scopeFolderId: item.id,
                    hidden,
                    disabled
                });
                folderInfoById.set(item.id, { itemIndex: index, endIndex, parentFolderId });
                layout.push({
                    id: item.id,
                    depth: stack.length,
                    hidden,
                    disabled,
                    canBeLocal: false
                });
                stack.push({
                    id: item.id,
                    endItemIndex: endIndex - 1,
                    descendantsHidden: hidden || !item.open,
                    descendantsDisabled: inheritedDisabled || item.disabled
                });
            } else {
                itemInfoById.set(item.id, {
                    itemIndex: index,
                    parentFolderId,
                    scopeFolderId: parentFolderId,
                    hidden,
                    disabled
                });
                layout.push({
                    id: item.id,
                    depth: stack.length,
                    hidden,
                    disabled,
                    canBeLocal: stack.length > 0
                });
                theoremItemIndices.push(index);
                theoremCount++;
            }
            theoremPrefixCounts[index + 1] = theoremCount;
        }
        this.derived = {
            revision: this.revision,
            itemIndexById,
            itemInfoById,
            folderInfoById,
            theoremItemIndices,
            theoremPrefixCounts,
            insertionParentFolderIds,
            layout
        };
        return this.derived;
    }

    private result(
        changed: boolean,
        structureChanged: boolean,
        definitionsChanged: boolean,
        revalidateFrom: number | null,
        revalidateTo: number | null = null
    ): TheoremWorkspaceMutation {
        return {
            changed,
            structureChanged,
            definitionsChanged,
            revalidateFrom,
            revalidateTo,
            snapshot: this.snapshot()
        };
    }
}
