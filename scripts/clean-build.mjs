import { rm } from "node:fs/promises";

await rm(new URL("../js", import.meta.url), { recursive: true, force: true });
