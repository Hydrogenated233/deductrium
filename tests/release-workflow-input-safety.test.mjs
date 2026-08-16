import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const workflowUrl = new URL("../.github/workflows/release.yml", import.meta.url);
const workflow = await readFile(workflowUrl, "utf8");
const stepStart = workflow.indexOf("      - name: Resolve release metadata");
const stepEnd = workflow.indexOf("      - name: Build release archive", stepStart);
assert.ok(stepStart >= 0 && stepEnd > stepStart, "release metadata step was not found");

const step = workflow.slice(stepStart, stepEnd);
assert.match(step, /RELEASE_INPUT_TAG:\s*\$\{\{ inputs\.tag \}\}/);
assert.match(step, /RELEASE_REF_NAME:\s*\$\{\{ github\.ref_name \}\}/);
assert.match(step, /RELEASE_REF_TYPE:\s*\$\{\{ github\.ref_type \}\}/);

const runStart = step.indexOf("        run: |");
assert.ok(runStart >= 0, "release metadata PowerShell body was not found");
const script = step.slice(runStart);
assert.doesNotMatch(script, /\$\{\{\s*(?:inputs\.tag|github\.ref_name|github\.ref_type)\s*\}\}/,
    "untrusted workflow values were interpolated directly into PowerShell source");
assert.match(script, /\$env:RELEASE_INPUT_TAG/);
assert.match(script, /\$env:RELEASE_REF_NAME/);
assert.match(script, /\$env:RELEASE_REF_TYPE/);
assert.match(script, /hott-v\(\?<date>\\d\{4\}\\\.\\d\{2\}\\\.\\d\{2\}\)/,
    "a date-like explicit tag no longer controls the archive date");

console.log("release workflow input isolation regression passed");
