import { TTGui, TTTheoremSaveItem } from "./gui.js";

export class SavesParser {

    serialize(gui: TTGui) {
        return JSON.stringify({ version: 2, items: gui.serializeTheoremItems() });
    }
    deserialize(gui: TTGui, s: string) {
        const saved = JSON.parse(s);
        const items: TTTheoremSaveItem[] = Array.isArray(saved)
            ? saved.map(value => ({ kind: "theorem", value }))
            : saved?.items;
        gui.restoreTheoremItems(Array.isArray(items) ? items : []);
        // gui.updateAfterUnlock();
        // gui.getInhabitatArray()[0]?.onblur({} as any);
    }
}
