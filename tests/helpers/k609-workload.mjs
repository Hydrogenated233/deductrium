import { GameSaveLoad } from "../../js/saveload.js";

export const K609_FINAL_THEOREM = "permEqvV87K_pg10:=ind_nat (Ln:nat,((Fin n)~=(Fin n))~=(Fin(factorial n))) permBaseEqvK_pg10 (Ln:nat,Le:((Fin n)~=(Fin n))~=(Fin(factorial n)),permStepEqvV87K_pg10 n e)";

export function decodeK609Theorems(encoded) {
    const saveLoader = Object.create(GameSaveLoad.prototype);
    saveLoader.storageKey = "deductrium-save";
    const parts = saveLoader.deserializeStr(encoded.trim()).split("-(=)-");
    if (parts.length !== 4) throw new Error(`expected 4 save sections, received ${parts.length}`);

    const saved = JSON.parse(parts[3]);
    const items = Array.isArray(saved)
        ? saved.map(value => ({ kind: "theorem", value }))
        : saved?.items;
    if (!Array.isArray(items)) throw new Error("type-theory save section has no theorem items");

    return items
        .filter(item => item.kind === "theorem")
        .map(item => String(item.value ?? ""));
}

export function createK609BenchmarkTheorems(encoded) {
    return [...decodeK609Theorems(encoded), K609_FINAL_THEOREM];
}
