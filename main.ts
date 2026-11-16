// Driver for the markdown-render-speed-02 entry. The harness runs
// `node /bot/main.ts` on Node 22: it reads every case from /input/cases.json
// (or $MAKEFUN_INPUT_DIR), renders each markdown with parse() from
// ./parse.js, and writes the HTML strings, one per case and in the cases'
// order, to /output/html.json (or $MAKEFUN_OUTPUT_DIR). Written for this
// entry; the driver itself does no Markdown work.
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const cases = JSON.parse(readFileSync(join(inputDir, 'cases.json'), 'utf8'));
const html = new Array(cases.length);
for (let i = 0; i < cases.length; i++) {
  html[i] = parse(cases[i].markdown);
}
mkdirSync(outputDir, { recursive: true });
writeFileSync(join(outputDir, 'html.json'), JSON.stringify(html));
