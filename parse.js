// parse.js — a fast Markdown renderer returning exactly the HTML that
// marked 18.1.3 produces with its defaults (GFM on, breaks off, pedantic
// off, async off). Written from scratch for the markdown-render-speed-02
// bounty.
//
// Design: one pass over the input. The block phase walks the source with
// marked's own block grammar (the same regular expressions, adapted from
// marked's MIT-licensed rules) and records compact block entries — it never
// builds a token tree. The render phase turns those entries straight into
// HTML strings. Inline rendering is also single-pass: a first-character
// dispatch tries only the tokenizers that can start with that character,
// and plain prose is copied in bulk after a cheap trigger check. No
// dependency, no built-in module; only the language itself.

export function parse(markdown) {
  const src = String(markdown).replace(/\r\n|\r/g, '\n');
  // Per-parse mutable state, shared by the block and inline phases.
  const st = {
    links: Object.create(null), // link reference definitions, by label
    inLink: false, // inside an <a> (or an image alt): no nested links
    inRawBlock: false, // inside <pre>/<code>/<kbd>/<script>: text is raw
    linkEmitted: false, // a link was rendered while parsing a label
    linkParenPossible: true, // the text may hold a "(...)" inline link
    top: true, // parsing at the document's top level
    hintStack: [], // one closer-scan per open inline span
  };
  const blocks = lexBlocks(src, st, true);
  const out = [];
  renderBlocks(blocks, st, out);
  return out.join('');
}

// ---------------------------------------------------------------------------
// Small shared patterns and string helpers.
// ---------------------------------------------------------------------------

const RE_CODE_INDENT = /^(?: {0,3}\t| {1,4})/gm;
const RE_LINK_BRACKET_ESC = /\\([\[\]])/g;
const RE_FENCE_INDENT = /^(\s+)(?:```)/;
const RE_LEAD_WS = /^\s+/;
const RE_HASH_END = /#$/;
const RE_LEAD_SPACE = /^ /;
const RE_TRAIL_SPACE = / $/;
const RE_TRAIL_WS = /[ \t]$/;
const RE_NON_SPACE = /[^ ]/;
const RE_NL = /\n/g;
const RE_TAB = /\t/g;
const RE_LEAD_WS_TAB = /^[ \t]+/;
const RE_WS_RUN = /\s+/g;
const RE_BLANK = /^[ \t]*$/;
const RE_DOUBLE_BLANK = /\n[ \t]*\n[ \t]*$/;
const RE_BQ_START = /^ {0,3}>/;
const RE_BQ_SETEXT = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const RE_BQ_MARKER = /^ {0,3}>[ \t]?/gm;
const RE_BQ_MARKER_WS = /^( {0,3}>)([ \t]+)/gm;
const RE_TASK = /^\[[ xX]\][ \t]+\S/;
const RE_TASK_STRIP = /^\[[ xX]\][ \t]+/;
const RE_TASK_BOX = /\[[ xX]\]/;
const RE_ANY_LINE = /\n.*\n/;
const RE_ANGLE_HREF = /^<(.*)>$/;
const RE_TABLE_SEP = /[:|]/;
const RE_TABLE_EDGE = /^\||\| *$/g;
const RE_TABLE_TRAIL_BLANK = /\n[ \t]*$/;
const RE_ALIGN_RIGHT = /^ *-+: *$/;
const RE_ALIGN_CENTER = /^ *:-+: *$/;
const RE_ALIGN_LEFT = /^ *:-+ *$/;
const RE_A_OPEN = /^<a /i;
const RE_A_CLOSE = /^<\/a>/i;
const RE_PRE_OPEN = /^<(pre|code|kbd|script)(\s|>)/i;
const RE_PRE_CLOSE = /^<\/(pre|code|kbd|script)(\s|>)/i;
const RE_ANGLE_OPEN = /^</;
const RE_ANGLE_CLOSE = />$/;
const RE_ALNUM = /[\p{L}\p{N}]/u;
const RE_NUM_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const RE_NUM_REF_OR_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
const RE_ESC_TEST = /[&<>"']/;
const RE_ESC_REPLACE = /[&<>"']/g;
const RE_ESC_TEST_NOENC = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const RE_ESC_REPLACE_NOENC = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
const RE_PCT25 = /%25/g;
const RE_PIPE = /\|/g;
const RE_PIPE_SPLIT = / \|/;
const RE_PIPE_ESC = /\\\|/g;
const RE_CR = /\r\n|\r/g;
// Characters that can start another inline construct; the plain-text fast
// path stops at the first of these.
const RE_TEXT_STOP = /[\\<!\[`*~_]/;

// A plain span needs the full text regex only when it might hold a
// URL/email autolink, a mailto:/xmpp: head, or a hard break.
function spanHasTrigger(span) {
  return span.includes('://') || span.includes('www.')
    || span.includes('@') || span.includes('mailto:')
    || span.includes('xmpp:') || span.includes('  \n');
}
const RE_NOT_SPACE_START = /^\S*/;
const RE_NL_END = /\n$/;

const ESC = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

function escapeHtml(html, encode) {
  if (encode) {
    if (RE_ESC_TEST.test(html)) return html.replace(RE_ESC_REPLACE, (ch) => ESC[ch]);
  } else if (RE_ESC_TEST_NOENC.test(html)) {
    return html.replace(RE_ESC_REPLACE_NOENC, (ch) => ESC[ch]);
  }
  return html;
}

// Numeric character references are decoded; a decoded character must not
// join its neighbours into a new reference, so every `&` that is not
// already one is escaped here. Zero, out-of-range and surrogate values
// become the replacement character. Named entities are NOT decoded —
// marked 18 keeps them as written.
function decodeNumericRefs(text) {
  if (!RE_NUM_REF.test(text)) return text;
  return text.replace(RE_NUM_REF_OR_AMP, (ref, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '�';
    return code === 38 ? '&amp;' : String.fromCodePoint(code);
  });
}

function cleanUrl(href) {
  try {
    href = encodeURI(href).replace(RE_PCT25, '%');
  } catch {
    return null;
  }
  return href;
}

// Split a table row on unescaped pipes, honouring the column count.
function splitCells(rowText, count) {
  const row = rowText.replace(RE_PIPE, (match, offset, str) => {
    let escaped = false;
    let curr = offset;
    while (--curr >= 0 && str[curr] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = row.split(RE_PIPE_SPLIT);
  let i = 0;
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells.at(-1)?.trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (; i < cells.length; i++) cells[i] = cells[i].trim().replace(RE_PIPE_ESC, '|');
  return cells;
}

// Remove trailing `c`s (str.replace(/c*$/, '') without the REDOS risk).
function rtrim(str, c, invert) {
  const l = str.length;
  if (l === 0) return '';
  let suffLen = 0;
  while (suffLen < l) {
    const ch = str.charAt(l - suffLen - 1);
    if (ch === c && !invert) suffLen++;
    else if (ch !== c && invert) suffLen++;
    else break;
  }
  return str.slice(0, l - suffLen);
}

function trimTrailingBlankLines(str) {
  const lines = str.split('\n');
  let end = lines.length - 1;
  while (end >= 0 && RE_BLANK.test(lines[end])) end--;
  if (lines.length - end <= 2) return str;
  return lines.slice(0, end + 1).join('\n');
}

// Normalizes a link label so definitions and references match: trim,
// collapse inner whitespace to one space, case-fold through upper case
// (as commonmark.js does, so ß meets SS).
function normalizeLabel(label) {
  return label.trim().replace(RE_WS_RUN, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Index of the closing bracket that takes the level below zero; -2 when
// more open than closed, -1 when balanced or absent.
function findClosingBracket(str, b) {
  if (str.indexOf(b[0]) === -1 && str.indexOf(b[1]) === -1) return -1;
  let level = 0;
  for (let i = 0; i < str.length; i++) {
    if (str[i] === '\\') i++;
    else if (str[i] === b[0]) level++;
    else if (str[i] === b[1]) {
      level--;
      if (level < 0) return i;
    }
  }
  return level > 0 ? -2 : -1;
}

// Index of the first character that is not a space.
function firstNonSpace(s) {
  for (let i = 0; i < s.length; i++) if (s[i] !== ' ') return i;
  return -1;
}

// Expand tabs to spaces, tracking the column from `indent`.
function expandTabs(line, indent = 0) {
  let col = indent;
  let expanded = '';
  for (const ch of line) {
    if (ch === '\t') {
      const added = 4 - (col % 4);
      expanded += ' '.repeat(added);
      col += added;
    } else {
      expanded += ch;
      col++;
    }
  }
  return expanded;
}

// One scan of a masked source for the last `*` / `_` run that can close
// emphasis or strong and the last `~` run that can close strikethrough. A
// run can close only when it is not preceded by ASCII whitespace or the
// start of the string.
function scanClosers(src) {
  let star = -1, under = -1, tilde = -1;
  const len = src.length;
  for (let i = 0; i < len; i++) {
    const ch = src[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = i === 0 ? '\n' : src[i - 1];
    let j = i + 1;
    while (j < len && src[j] === ch) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (ch === '~') tilde = i;
      else if (ch === '*') star = i;
      else under = i;
    }
    i = j - 1;
  }
  return { src, star, under, tilde };
}

// ---------------------------------------------------------------------------
// Block grammar: marked's GFM block rules (its rules module, MIT). Only the
// GFM set is needed — the defaults are gfm on, breaks off, pedantic off,
// so the pedantic and normal grammars are never used. The three begin
// patterns below are built per indent (0–3) and cached, because the block
// lexer asks for them with the current indent on every list item line.
// ---------------------------------------------------------------------------

const TAG_LIST = 'address|article|aside|base|basefont|blockquote|body|caption'
  + '|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption'
  + '|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe'
  + '|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option'
  + '|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title'
  + '|tr|track|ul';

function indentCached(make) {
  const cache = [];
  return (indent) => {
    const idx = Math.max(0, Math.min(3, indent - 1));
    let re = cache[idx];
    if (!re) { re = make(idx); cache[idx] = re; }
    return re;
  };
}
const itemStartRe = (bull) => new RegExp(`^( {0,3}${bull})((?:[\t ][^\\n]*)?(?:\\n|$))`);
const nextBulletRe = indentCached((i) => new RegExp(`^ {0,${i}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\\n]*)?(?:\\n|$))`));
const hrAtRe = indentCached((i) => new RegExp(`^ {0,${i}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\\n+|$)`));
const fenceAtRe = indentCached((i) => new RegExp(`^ {0,${i}}(?:\`\`\`|~~~)`));
const atxAtRe = indentCached((i) => new RegExp(`^ {0,${i}}#{1,6}(?:\\s|$)`));
const htmlAtRe = indentCached((i) => new RegExp(`^ {0,${i}}(?:</?(?:${TAG_LIST})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i'));
const bqAtRe = indentCached((i) => new RegExp(`^ {0,${i}}>`));

const BLK_BLOCKQUOTE = /^( {0,3}> ?(?:(?![ \t]*(?:\n|$))(([^\n]+(?:\n(?! {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}#{1,6}(?:\s|$)| {0,3}>| {0,3}(?:`{3,}(?=[^`\n]*(?:\n|$))|~~~)[^\n]*(?:\n|$)| {0,3}(?:[*+-]|\d{1,9}[.)])(?:[ \t]|\n|$)| {0,3}(?:<\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\n|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)|[ \t]+\n)[^\n]+)*))|[^\n]*)(?:\n|$))+/;
const BLK_CODE = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
const BLK_DEF = /^ {0,3}\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\]: *(?:\n[ \t]*)?([^<\s][^\s]*|<.*?>)(?:(?: +(?:\n[ \t]*)?| *\n[ \t]*)((?:"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))))? *(?:\n+|$)/;
const BLK_FENCES = /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/;
const BLK_HEADING = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;
const BLK_HR = /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/;
const BLK_HTML = /^ {0,3}(?:<(script|pre|style|textarea)[\s>][\s\S]*?(?:<\/\1>[^\n]*\n*|$)|<!--(?:-?>|[\s\S]*?(?:-->|$))[^\n]*(\n+|$)|<\?[\s\S]*?(?:\?>[^\n]*\n*|$)|<![A-Z][\s\S]*?(?:>[^\n]*\n*|$)|<!\[CDATA\[[\s\S]*?(?:\]\]>[^\n]*\n*|$)|<\/?(address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?:[ \t]+|\n|\/?>|$)[\s\S]*?(?:(?:\n[ \t]*)+\n|$)|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?: +[a-zA-Z:_][\w.:-]*(?: *= *"[^"\n]*"| *= *'[^'\n]*'| *= *[^\s"'=<>`]+)?)*? *\/?>(?=[ \t]*(?:\n|$))[\s\S]*?(?:(?:\n[ \t]*)+\n|$)|<\/[a-z][a-z0-9-]*\s*>(?=[ \t]*(?:\n|$))[\s\S]*?(?:(?:\n[ \t]*)+\n|$))/i;
const BLK_LHEADING = /^(?! {0,3}(?:[*+-]|\d{1,9}[.)]) |(?: {4}| {0,3}\t)| {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\s|$)| {0,3}<[^\n>]+>\n| {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n)((?:.|\n(?!\s*?\n| {0,3}(?:[*+-]|\d{1,9}[.)]) | {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\s|$)| {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}<[^\n>]+>\n| {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n))+?)\n {0,3}(=+|-+)[ \t]*(?:\n+|$)/;
const BLK_LIST = /^( {0,3}(?:[*+-]|\d{1,9}[.)]))([ \t][^\n]*?)?(?:\n|$)/;
const BLK_NEWLINE = /^(?:[ \t]*(?:\n|$))+/;
const BLK_PARAGRAPH = /^([^\n]+(?:\n(?! {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}#{1,6}(?:\s|$)| {0,3}>| {0,3}(?:`{3,}(?=[^`\n]*(?:\n|$))|~~~)[^\n]*(?:\n|$)| {0,3}(?:[*+-]|1[.)])[ \t]+[^ \t\n]| {0,3}(?:<\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\n|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)| *([^\n ].*)\n {0,3}((?:\| *)?:?-+:? *(?:\| *:?-+:? *)*(?:\| *)?)(?:\n((?:(?! *\n| {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}#{1,6}(?:\s|$)| {0,3}>|(?: {4}| {0,3}	)[^\n]| {0,3}(?:`{3,}(?=[^`\n]*(?:\n|$))|~~~)[^\n]*(?:\n|$)| {0,3}(?:[*+-]|1[.)])[ \t]| {0,3}(?:<\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\n|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)).*(?:\n|$))*)\n*|$)|[ \t]+\n)[^\n]+)*)/;
const BLK_TABLE = /^ *([^\n ].*)\n {0,3}((?:\| *)?:?-+:? *(?:\| *:?-+:? *)*(?:\| *)?)(?:\n((?:(?! *\n| {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}#{1,6}(?:\s|$)| {0,3}>|(?: {4}| {0,3}	)[^\n]| {0,3}(?:`{3,}(?=[^`\n]*(?:\n|$))|~~~)[^\n]*(?:\n|$)| {0,3}(?:[*+-]|1[.)])[ \t]| {0,3}(?:<\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\n|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)).*(?:\n|$))*)\n*|$)/;
const BLK_TEXT = /^[^\n]+/;

// ---------------------------------------------------------------------------
// Inline grammar: marked's GFM inline rules (its rules module, MIT).
// ---------------------------------------------------------------------------

const INL_BACKPEDAL = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;
const INL_ANY_PUNCT = /\\([\p{P}\p{S}])/gu;
const INL_ANY_PUNCT_OUTSIDE_CODE = /(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\([\p{P}\p{S}])/gu;
const INL_AUTOLINK = /^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/;
const INL_BLOCK_SKIP = /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)|(?<!`)()(?<b>`+)[^`]+\k<b>(?!`)|<(?! )[^<>]*?>/g;
const INL_BR = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;
const INL_CODE = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const INL_DEL = /^(~~?)(?=[^\s~])((?:\\[\s\S]|[^\\])*?(?:\\[\s\S]|[^\s~\\]))\1(?=[^~]|$)/;
const INL_DEL_L = /^~~?(?:((?!~)[\p{P}\p{S}])|[^\s~])/u;
const INL_DEL_R = /^[^~]+(?=[^~])|(?!~)[\p{P}\p{S}](~~?)(?=[\s]|$)|[^\s\p{P}\p{S}](~~?)(?!~)(?=[\s\p{P}\p{S}]|$)|(?!~)[\s\p{P}\p{S}](~~?)(?=[^\s\p{P}\p{S}])|[\s](~~?)(?!~)(?=[\p{P}\p{S}])|(?!~)[\p{P}\p{S}](~~?)(?!~)(?=[\p{P}\p{S}])|[^\s\p{P}\p{S}](~~?)(?=[^\s\p{P}\p{S}])/gu;
const INL_EM_L = /^(?:\*+(?:((?!\*)(?!~)[\p{P}\p{S}])|([^\s*]))?)|^_+(?:((?!_)(?!~)[\p{P}\p{S}])|([^\s_]))?/u;
const INL_EM_R_AST = /^[^_*]*?__[^_*]*?\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\*)(?!~)[\p{P}\p{S}](\*+)(?=[\s]|$)|(?:[^\s\p{P}\p{S}]|~)(\*+)(?!\*)(?=(?!~)[\s\p{P}\p{S}]|$)|(?!\*)(?!~)[\s\p{P}\p{S}](\*+)(?=(?:[^\s\p{P}\p{S}]|~))|[\s](\*+)(?!\*)(?=(?!~)[\p{P}\p{S}])|(?!\*)(?!~)[\p{P}\p{S}](\*+)(?!\*)(?=(?!~)[\p{P}\p{S}])|(?:[^\s\p{P}\p{S}]|~)(\*+)(?=(?:[^\s\p{P}\p{S}]|~))/gu;
const INL_EM_R_UND = /^[^_*]*?\*\*[^_*]*?_[^_*]*?(?=\*\*)|[^_]+(?=[^_])|(?!_)[\p{P}\p{S}](_+)(?=[\s]|$)|[^\s\p{P}\p{S}](_+)(?!_)(?=[\s\p{P}\p{S}]|$)|(?!_)[\s\p{P}\p{S}](_+)(?=[^\s\p{P}\p{S}])|[\s](_+)(?!_)(?=[\p{P}\p{S}])|(?!_)[\p{P}\p{S}](_+)(?!_)(?=[\p{P}\p{S}])/gu;
const INL_ESCAPE = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const INL_LINK = /^!?\[((?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?)\]\([ \t\n]*(<(?:\\.|[^\n<>\\])+>|[^ \t\n\x00-\x1f]+|(?=\)))(?:(?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)("(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\((?:\\[\s\S]|[^)\\])*\)))?[ \t\n]*\)/;
const INL_NOLINK = /^!?\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\](?:\[\])?/;
const INL_PUNCT = /^((?![*_])[\s\p{P}\p{S}])/u;
const INL_REFLINK = /^!?\[((?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?)\]\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\]/;
const INL_REFLINK_SEARCH = /!?\[((?:[^\[\]\\`]*(?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\]))){0,999}?[^\[\]\\`]*?)\]\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999})\]|!?\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999})\](?:\[\])?(?!\()/g;
const INL_TAG = /^<!--(?:-?>|[\s\S]*?-->)|^<\/[a-zA-Z][a-zA-Z0-9-]*\s*>|^<[a-zA-Z][a-zA-Z0-9-]*(?:\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?)*?\s*\/?>|^<\?[\s\S]*?\?>|^<![a-zA-Z]+\s[\s\S]*?>|^<!\[CDATA\[[\s\S]*?\]\]>/;
const INL_TEXT = /^(?:[^a-zA-Z0-9](?=(?:mailto|xmpp):)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\n)|(?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@)|[\s\S]*?(?:(?=[\\<!\[`*~_]|\b_|[hH][tT][tT][pP][sS]?|[fF][tT][pP]:\/\/|(?<![^\s*_~(])www\.|$)|[^ ](?= {2,}\n)|[^a-zA-Z0-9](?=(?:mailto|xmpp):)|[^a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-](?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@))))/;
const INL_URL = /^(?:mailto:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])|xmpp:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])(?:\/[A-Za-z0-9@.]+)?)|^((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|^[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/;

// ---------------------------------------------------------------------------
// Block lexing: turns source into a list of block records, collecting link
// reference definitions into st.links. Mirrors marked's Lexer.blockTokens
// (same order, same merging rules). A record is {t, raw, ...} with t the
// block type; records hold the raw text the render phase turns into HTML,
// so no token objects are built for inline.
// ---------------------------------------------------------------------------

// A fenced code block's text is indented by the fence's own indent.
function fenceIndentCompensation(raw, text) {
  const m = raw.match(RE_FENCE_INDENT);
  if (m === null) return text;
  const indentToCode = m[1];
  return text.split('\n').map((node) => {
    const mn = node.match(RE_LEAD_WS);
    if (mn === null) return node;
    return node.slice(Math.min(mn[0].length, indentToCode.length));
  }).join('\n');
}

function lexBlocks(src, st, top, lastParagraphClipped = false, blocks = []) {
  let srcLength = Infinity;
  while (src) {
    if (src.length < srcLength) srcLength = src.length;
    else throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));

    let rec;
    // blank lines / spaces
    if ((rec = tokSpace(src))) {
      src = src.substring(rec.raw.length);
      const last = blocks.at(-1);
      if (rec.raw.length === 1 && last !== undefined) last.raw += '\n';
      else blocks.push(rec);
      continue;
    }
    // indented code
    if ((rec = tokCode(src))) {
      src = src.substring(rec.raw.length);
      const last = blocks.at(-1);
      if (last?.t === 'paragraph' || last?.t === 'text') {
        last.raw += (last.raw.endsWith('\n') ? '' : '\n') + rec.raw;
        last.text += '\n' + rec.text;
      } else blocks.push(rec);
      continue;
    }
    // fenced code
    if ((rec = tokFences(src))) {
      src = src.substring(rec.raw.length);
      blocks.push(rec);
      continue;
    }
    // ATX heading
    if ((rec = tokHeading(src, st))) {
      src = src.substring(rec.raw.length);
      blocks.push(rec);
      continue;
    }
    // thematic break
    if ((rec = tokHr(src))) {
      src = src.substring(rec.raw.length);
      blocks.push(rec);
      continue;
    }
    // blockquote
    if ((rec = tokBlockquote(src, st))) {
      src = src.substring(rec.raw.length);
      blocks.push(rec);
      continue;
    }
    // list
    if ((rec = tokList(src, st))) {
      src = src.substring(rec.raw.length);
      blocks.push(rec);
      continue;
    }
    // html block
    if ((rec = tokHtml(src))) {
      src = src.substring(rec.raw.length);
      blocks.push(rec);
      continue;
    }
    // link reference definition
    if ((rec = tokDef(src))) {
      src = src.substring(rec.raw.length);
      const last = blocks.at(-1);
      if (last?.t === 'paragraph' || last?.t === 'text') {
        last.raw += (last.raw.endsWith('\n') ? '' : '\n') + rec.raw;
        last.text += '\n' + rec.raw;
      } else {
        if (!st.links[rec.tag]) st.links[rec.tag] = { href: rec.href, title: rec.title };
        blocks.push(rec);
      }
      continue;
    }
    // table (gfm)
    if ((rec = tokTable(src, st))) {
      src = src.substring(rec.raw.length);
      blocks.push(rec);
      continue;
    }
    // setext heading
    if ((rec = tokLheading(src, st))) {
      src = src.substring(rec.raw.length);
      blocks.push(rec);
      continue;
    }
    // paragraph (top level only)
    if (top && (rec = tokParagraph(src, st))) {
      const last = blocks.at(-1);
      if (lastParagraphClipped && last?.t === 'paragraph') {
        last.raw += (last.raw.endsWith('\n') ? '' : '\n') + rec.raw;
        last.text += '\n' + rec.text;
      } else {
        blocks.push(rec);
      }
      lastParagraphClipped = false;
      src = src.substring(rec.raw.length);
      continue;
    }
    // plain text
    if ((rec = tokText(src, st))) {
      src = src.substring(rec.raw.length);
      const last = blocks.at(-1);
      if (last?.t === 'text') {
        last.raw += (last.raw.endsWith('\n') ? '' : '\n') + rec.raw;
        last.text += '\n' + rec.text;
      } else blocks.push(rec);
      continue;
    }
    if (src) throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
  }
  st.top = true;
  return blocks;
}

function tokSpace(src) {
  const cap = BLK_NEWLINE.exec(src);
  if (cap && cap[0].length > 0) return { t: 'space', raw: cap[0] };
  return null;
}

function tokCode(src) {
  const cap = BLK_CODE.exec(src);
  if (!cap) return null;
  const raw = trimTrailingBlankLines(cap[0]);
  return { t: 'code', raw, text: raw.replace(RE_CODE_INDENT, '') };
}

function tokFences(src) {
  const cap = BLK_FENCES.exec(src);
  if (!cap) return null;
  return {
    t: 'code', raw: cap[0],
    lang: cap[2] ? cap[2].trim().replace(INL_ANY_PUNCT, '$1') : cap[2],
    text: fenceIndentCompensation(cap[0], cap[3] || ''),
  };
}

function tokHeading(src, st) {
  const cap = BLK_HEADING.exec(src);
  if (!cap) return null;
  let text = cap[2].trim();
  if (RE_HASH_END.test(text)) {
    const trimmed = rtrim(text, '#');
    if (!trimmed || RE_TRAIL_WS.test(trimmed)) text = trimmed.trim();
  }
  return { t: 'heading', raw: rtrim(cap[0], '\n'), depth: cap[1].length, text };
}

function tokHr(src) {
  const cap = BLK_HR.exec(src);
  if (!cap) return null;
  return { t: 'hr', raw: rtrim(cap[0], '\n') };
}

function tokHtml(src) {
  const cap = BLK_HTML.exec(src);
  if (!cap) return null;
  const raw = trimTrailingBlankLines(cap[0]);
  return { t: 'html', raw, pre: cap[1] === 'pre' || cap[1] === 'script' || cap[1] === 'style', text: raw };
}

function tokDef(src) {
  const cap = BLK_DEF.exec(src);
  if (!cap) return null;
  if (!RE_ANGLE_OPEN.test(cap[2]) && findClosingBracket(cap[2], '()') !== -1) return null;
  const tag = normalizeLabel(cap[1]);
  const href = cap[2] ? cap[2].replace(RE_ANGLE_HREF, '$1').replace(INL_ANY_PUNCT, '$1') : '';
  const title = cap[3] ? cap[3].substring(1, cap[3].length - 1).replace(INL_ANY_PUNCT, '$1') : cap[3];
  return { t: 'def', tag, raw: rtrim(cap[0], '\n'), href, title };
}

function tokTable(src, st) {
  const cap = BLK_TABLE.exec(src);
  if (!cap) return null;
  if (!RE_TABLE_SEP.test(cap[2])) return null;
  const headers = splitCells(cap[1]);
  const aligns = cap[2].replace(RE_TABLE_EDGE, '').split('|');
  const rows = cap[3]?.trim() ? cap[3].replace(RE_TABLE_TRAIL_BLANK, '').split('\n') : [];
  if (headers.length !== aligns.length) return null;
  const align = [];
  for (const a of aligns) {
    if (RE_ALIGN_RIGHT.test(a)) align.push('right');
    else if (RE_ALIGN_CENTER.test(a)) align.push('center');
    else if (RE_ALIGN_LEFT.test(a)) align.push('left');
    else align.push(null);
  }
  const rowCells = [];
  for (const row of rows) rowCells.push(splitCells(row, headers.length));
  return { t: 'table', raw: rtrim(cap[0], '\n'), header: headers, align, rows: rowCells };
}

function tokLheading(src, st) {
  const cap = BLK_LHEADING.exec(src);
  if (!cap) return null;
  return { t: 'heading', raw: rtrim(cap[0], '\n'), depth: cap[2].charAt(0) === '=' ? 1 : 2, text: cap[1].trim() };
}

function tokParagraph(src, st) {
  const cap = BLK_PARAGRAPH.exec(src);
  if (!cap) return null;
  const text = cap[1].charAt(cap[1].length - 1) === '\n' ? cap[1].slice(0, -1) : cap[1];
  return { t: 'paragraph', raw: cap[0], text };
}

function tokText(src, st) {
  const cap = BLK_TEXT.exec(src);
  if (!cap) return null;
  return { t: 'text', raw: cap[0], text: cap[0] };
}

function tokBlockquote(src, st) {
  const cap = BLK_BLOCKQUOTE.exec(src);
  if (!cap) return null;
  let lines = rtrim(cap[0], '\n').split('\n');
  let raw = '';
  let text = '';
  const tokens = [];

  while (lines.length > 0) {
    let inBlockquote = false;
    const currentLines = [];
    let i;
    for (i = 0; i < lines.length; i++) {
      if (RE_BQ_START.test(lines[i])) {
        currentLines.push(lines[i]);
        inBlockquote = true;
      } else if (!inBlockquote) {
        currentLines.push(lines[i]);
      } else {
        break;
      }
    }
    lines = lines.slice(i);

    const currentRaw = currentLines.join('\n');
    const currentText = currentRaw
      .replace(RE_BQ_MARKER_WS, (_, marker, whitespace) => marker + expandTabs(whitespace, marker.length))
      .replace(RE_BQ_SETEXT, '\n    $1')
      .replace(RE_BQ_MARKER, '');
    raw = raw ? `${raw}\n${currentRaw}` : currentRaw;
    text = text ? `${text}\n${currentText}` : currentText;

    lexBlocks(currentText, st, true, true, tokens);

    if (lines.length === 0) break;

    const lastToken = tokens.at(-1);
    if (lastToken?.t === 'code' || lastToken?.t === 'heading' || lastToken?.t === 'hr' || lastToken?.t === 'html' || lastToken?.t === 'table') {
      break;
    } else if (lastToken?.t === 'blockquote') {
      const oldToken = lastToken;
      const continuation = lines.join('\n');
      const newText = oldToken.raw + '\n' + continuation.replace(RE_BQ_MARKER, '');
      const newToken = tokBlockquote(newText, st);
      tokens[tokens.length - 1] = newToken;
      const leftover = newText.substring(newToken.raw.length).replace(/^\n/, '');
      const leftoverCount = leftover ? leftover.split('\n').length : 0;
      const consumed = leftoverCount ? lines.slice(0, -leftoverCount) : lines;
      if (consumed.length > 0) raw = `${raw}\n${consumed.join('\n')}`;
      text = text.substring(0, text.length - oldToken.text.length) + newToken.text;
      lines = lines.slice(consumed.length);
      if (lines.length > 0 && RE_BQ_START.test(lines[0])) continue;
      break;
    } else if (lastToken?.t === 'list') {
      const oldToken = lastToken;
      const newText = oldToken.raw + '\n' + lines.join('\n');
      const newToken = tokList(newText, st);
      tokens[tokens.length - 1] = newToken;
      const consumedCount = newToken.raw.length > oldToken.raw.length
        ? newText.slice(oldToken.raw.length + 1, newToken.raw.length).split('\n').length
        : 0;
      if (consumedCount > 0) {
        const consumed = lines.slice(0, consumedCount).join('\n');
        raw = `${raw}\n${consumed}`;
        text = `${text}\n${consumed}`;
      }
      lines = lines.slice(consumedCount);
      continue;
    }
  }

  return { t: 'blockquote', raw, tokens, text };
}

function tokList(src, st) {
  let cap = BLK_LIST.exec(src);
  if (!cap) return null;
  const listSrc = src;
  const taken = () => listSrc.length - src.length;
  let bull = cap[1].trim();
  const isordered = bull.length > 1;

  const list = {
    t: 'list', raw: '', ordered: isordered,
    start: isordered ? +bull.slice(0, -1) : '', loose: false, items: [],
  };

  bull = isordered ? `\\d{1,9}\\${bull.slice(-1)}` : `\\${bull}`;

  const itemRegex = itemStartRe(bull);
  let endsWithBlankLine = false;
  while (src) {
    let endEarly = false;
    let itemContents = '';
    if (!(cap = itemRegex.exec(src))) break;
    if (BLK_HR.test(src)) break;

    const itemStart = taken();
    src = src.substring(cap[0].length);

    const firstLine = cap[2].split('\n', 1)[0];
    const bulletIndent = cap[1].length;
    let line = firstLine.replace(RE_LEAD_WS_TAB, (w) => expandTabs(w, bulletIndent));
    let nextLine = src.split('\n', 1)[0];
    let blankLine = !line.trim();

    let indent = 0;
    if (blankLine) {
      indent = bulletIndent + 1;
    } else {
      indent = line.search(RE_NON_SPACE);
      indent = indent > 4 ? 1 : indent;
      itemContents = line.slice(indent);
      indent += bulletIndent;
    }

    if (blankLine && RE_BLANK.test(nextLine)) {
      src = src.substring(nextLine.length + 1);
      endEarly = true;
    }

    if (!endEarly) {
      const nextBullet = nextBulletRe(indent);
      const hrRe = hrAtRe(indent);
      const fencesRe = fenceAtRe(indent);
      const headingRe = atxAtRe(indent);
      const htmlRe = htmlAtRe(indent);
      const bqRe = bqAtRe(indent);
      const ci = Math.max(0, Math.min(3, indent - 1));
      // Content lines are collected and joined once, instead of growing
      // the item string line by line.
      const parts = [itemContents];
      itemContents = '';

      while (src) {
        const nl = src.indexOf('\n');
        const rawLine = nl === -1 ? src : src.slice(0, nl);
        nextLine = rawLine;
        const nextLineWithoutTabs = (nextLine[0] === ' ' || nextLine[0] === '\t')
          ? nextLine.replace(RE_LEAD_WS_TAB, (w) => expandTabs(w)) : nextLine;

        if (fencesRe.test(nextLine)) break;
        if (headingRe.test(nextLine)) break;
        if (bqRe.test(nextLine)) break;
        if (nextBullet.test(nextLine)) break;
        if (hrRe.test(nextLine)) break;
        // The html test carries the long tag alternation; it can only
        // match a line whose first non-space character (within the
        // indent) is '<'.
        const fns = firstNonSpace(nextLine);
        if (fns !== -1 && fns <= ci && nextLine[fns] === '<' && htmlRe.test(nextLine)) break;

        const nextBlank = !nextLine.trim();
        if (firstNonSpace(nextLineWithoutTabs) >= indent || nextBlank) {
          parts.push(nextLineWithoutTabs.slice(indent));
        } else {
          if (blankLine) break;
          if (firstNonSpace(line.includes('\t') ? line.replace(RE_TAB, '    ') : line) >= 4) break;
          if (fencesRe.test(line)) break;
          if (headingRe.test(line)) break;
          if (hrRe.test(line)) break;
          const lfns = firstNonSpace(line);
          if (lfns !== -1 && lfns <= ci && line[lfns] === '<' && htmlRe.test(line)) break;

          const setextContinuation = /^ {0,3}(?:=+|-+) *$/.test(nextLine)
            && BLK_LHEADING.test(`${line}\n${nextLine}`);
          const continuation = setextContinuation
            ? `    ${nextLineWithoutTabs.replace(/^ {0,3}/, '')}`
            : nextLine;
          parts.push(continuation);
        }

        blankLine = nextBlank;
        src = nl === -1 ? '' : src.substring(nl + 1);
        line = nextLineWithoutTabs.slice(indent);
      }
      itemContents = parts.join('\n');
    }

    const raw = listSrc.slice(itemStart, taken());

    if (!list.loose) {
      if (endsWithBlankLine) list.loose = true;
      else if (RE_DOUBLE_BLANK.test(raw)) endsWithBlankLine = true;
    }

    list.items.push({
      t: 'list_item', raw, task: RE_TASK.test(itemContents),
      loose: false, text: itemContents, tokens: [],
    });
  }

  const lastItem = list.items.at(-1);
  if (lastItem) {
    lastItem.raw = lastItem.raw.trimEnd();
    lastItem.text = lastItem.text.trimEnd();
  } else {
    return null;
  }
  list.raw = listSrc.slice(0, taken()).trimEnd();

  // First pass: tokenize items and decide list.loose from spacers.
  for (const item of list.items) {
    item.tokens = lexBlocks(item.text, st, false);
    if (!list.loose) {
      const spacers = item.tokens.filter((t) => t.t === 'space');
      const hasMultipleLineBreaks = spacers.length > 0 && spacers.some((t) => RE_ANY_LINE.test(t.raw));
      list.loose = hasMultipleLineBreaks;
    }
  }

  // Second pass: place task checkboxes using the final list.loose.
  for (const item of list.items) {
    const itemToken = item.tokens[0];
    if (item.task && (itemToken?.t === 'text' || itemToken?.t === 'paragraph')) {
      item.text = item.text.replace(RE_TASK_STRIP, '');
      itemToken.raw = itemToken.raw.replace(RE_TASK_STRIP, '');
      itemToken.text = itemToken.text.replace(RE_TASK_STRIP, '');

      const taskRaw = RE_TASK_BOX.exec(item.raw);
      if (taskRaw) {
        const checkbox = { t: 'checkbox', raw: taskRaw[0] + ' ', checked: taskRaw[0] !== '[ ]' };
        item.checked = checkbox.checked;
        if (list.loose) {
          if (item.tokens[0] && ['paragraph', 'text'].includes(item.tokens[0].t)) {
            // The checkbox becomes the paragraph's first inline element;
            // the paragraph's own text is left alone (marked prefixes its
            // text field with the checkbox raw, but renders from the
            // tokens, so prefixing here would print "[ ] " twice).
            item.tokens[0].checkbox = checkbox;
          } else {
            item.tokens.unshift({ t: 'paragraph', raw: checkbox.raw, text: '', checkbox });
          }
        } else {
          item.tokens.unshift(checkbox);
        }
      }
    } else if (item.task) {
      item.task = false;
    }
  }

  if (list.loose) {
    for (const item of list.items) {
      item.loose = true;
      for (const token of item.tokens) {
        if (token.t === 'text') token.t = 'paragraph';
      }
    }
  }

  return list;
}

// ---------------------------------------------------------------------------
// Inline rendering: turns inline source into HTML (mode 'html') or plain
// text (mode 'text', for image alt attributes), mirroring marked's
// Lexer.inlineTokens + Parser.parseInline. Renders straight to the output
// array instead of building token objects. `mode` propagates into nested
// spans, so an image inside a link still renders as <img>, and a link
// inside an image's alt still renders as plain text.
// ---------------------------------------------------------------------------

// Is the end of this link label inside an inline tag/autolink that runs
// past the label? Then the label is not a link at all.
function isLabelEndInsideToken(src, label, labelStart) {
  if (!label.includes('<')) return false;
  for (let i = 0; i < label.length; i++) {
    if (label[i] === '\\') { i++; continue; }
    if (label[i] === '`') {
      const code = INL_CODE.exec(label.slice(i));
      if (code) { i += code[0].length - 1; continue; }
    }
    if (label[i] !== '<') continue;
    const tokenSrc = src.slice(labelStart + i);
    const token = INL_TAG.exec(tokenSrc) || INL_AUTOLINK.exec(tokenSrc);
    if (!token) continue;
    if (token[0].length > label.length - i) return true;
    i += token[0].length - 1;
  }
  return false;
}

// Does this link text hold a link already? An image does not count: an
// image may hold a link, a link may not.
function linkInText(text, st) {
  if (!text.includes('[')) return false;
  for (const match of text.matchAll(INL_BLOCK_SKIP)) {
    if (INL_LINK.test(match[0]) && text.charAt(match.index - 1) !== '!') return true;
  }
  for (const match of text.matchAll(INL_REFLINK_SEARCH)) {
    const match0 = match[0];
    const refStart = match0.lastIndexOf('[');
    if (match0.charAt(0) === '!' || !Object.hasOwn(st.links, normalizeLabel(match0.slice(refStart + 1, -1)))) continue;
    if (refStart > 1 && linkInText(match0.slice(1, refStart - 1), st)) continue;
    return true;
  }
  return false;
}

// Mask links, code, html and escapes so emStrong and del do not see their
// delimiters inside them. Every mask keeps the length it replaces, because
// emStrong and del line maskedSrc up with src by slicing from the end.
function maskSrc(src, st) {
  let maskedSrc = src;
  if (st.links && src.includes('[')) {
    const maskReflink = (match0) => {
      const refStart = match0.lastIndexOf('[');
      if (!Object.hasOwn(st.links, normalizeLabel(match0.slice(refStart + 1, -1)))) return match0;
      if (refStart > 1 && match0.charAt(0) !== '!') {
        const text = match0.slice(1, refStart - 1);
        if (linkInText(text, st)) {
          return '[' + text.replace(INL_REFLINK_SEARCH, maskReflink)
            + '][' + 'a'.repeat(match0.length - refStart - 2) + ']';
        }
      }
      return '[' + 'a'.repeat(match0.length - 2) + ']';
    };
    maskedSrc = maskedSrc.replace(INL_REFLINK_SEARCH, maskReflink);
  }
  maskedSrc = maskedSrc.replace(INL_ANY_PUNCT_OUTSIDE_CODE, (match0, code, punct) => {
    if (punct) return '+'.repeat(match0.length);
    if (code) return code + match0.slice(code.length, -code.length).replace(/`/g, '+') + code;
    return match0;
  });
  maskedSrc = maskedSrc.replace(INL_BLOCK_SKIP, (match0, _link, context) => {
    const offset = context ? context.length : 0;
    return match0.slice(0, offset) + '[' + 'a'.repeat(match0.length - offset - 2) + ']';
  });
  return maskedSrc;
}

// Render inline source to HTML ('html') or plain text ('text'), appending
// to `out`. Returns nothing; `out` is an array of string fragments.
function renderInline(src, st, out, mode) {
  const prevLinkParenPossible = st.linkParenPossible;
  st.linkParenPossible = prevLinkParenPossible && src.includes(')');
  try {
    renderInlineInner(src, st, out, mode);
  } finally {
    st.linkParenPossible = prevLinkParenPossible;
  }
}

function renderInlineInner(src, st, out, mode) {
  const maskedSrc = (src.includes('*') || src.includes('_') || src.includes('~'))
    ? maskSrc(src, st) : src;
  st.hintStack.push(scanClosers(maskedSrc));
  try {
    renderInlineLoop(src, maskedSrc, st, out, mode);
  } finally {
    st.hintStack.pop();
  }
}

function renderInlineLoop(src, maskedSrc, st, out, mode) {
  let keepPrevChar = false;
  let prevChar = '';
  let srcLength = Infinity;
  while (src) {
    if (src.length < srcLength) srcLength = src.length;
    else throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));

    if (!keepPrevChar) prevChar = '';
    keepPrevChar = false;

    // Dispatch on the first character: only the tokenizers that can start
    // with it are tried. A URL/email autolink can only start with a letter,
    // digit, '.', '+', '-' or '_' (INL_URL's scheme/www/email heads), so
    // the structural tokenizers are skipped for plain prose entirely.
    const c = src.charCodeAt(0);
    let n = 0;
    if (c === 92) { // backslash: escape, then a hard break (backslash + newline)
      n = tokEscape(src, st, out, mode) || tokBr(src, st, out, mode);
    } else if (c === 60) { // <: tag, autolink
      n = tokTag(src, st, out, mode) || tokAutolink(src, st, out, mode);
    } else if (c === 91) { // [: link, reflink
      n = tokLink(src, st, out, mode) || tokReflink(src, st, out, mode);
    } else if (c === 33) { // !: link/image, reflink (only as ![)
      n = src.charCodeAt(1) === 91
        ? (tokLink(src, st, out, mode) || tokReflink(src, st, out, mode)) : 0;
    } else if (c === 42) { // *: emphasis
      n = tokEmStrong(src, maskedSrc, st, out, mode, prevChar);
    } else if (c === 95) { // _: emphasis, then a possible email autolink
      n = tokEmStrong(src, maskedSrc, st, out, mode, prevChar)
        || (!st.inLink ? tokUrl(src, st, out, mode) : 0);
    } else if (c === 96) { // backtick: code span
      n = tokCodespan(src, st, out, mode);
    } else if (c === 126) { // ~: strikethrough
      n = tokDel(src, maskedSrc, st, out, mode, prevChar);
    } else if (c === 32) { // space: hard break (two spaces + newline)
      n = tokBr(src, st, out, mode);
    } else if (!st.inLink && isUrlStart(c)) {
      // letter, digit, '.', '+', '-': a scheme, www. or email autolink
      n = tokUrl(src, st, out, mode);
    }
    if (n) {
      // A reflink fallback consumes exactly 1 char and yields a text
      // token, so it updates prevChar like a text token does.
      if (n === 1 && (c === 91 || c === 33) && src[0] !== '_') { prevChar = src[0]; keepPrevChar = true; }
      src = src.substring(n);
      continue;
    }
    // plain text (also the fallback when the dispatched tokenizer failed)
    if ((n = tokInlineText(src, st, out, mode))) {
      if (src[n - 1] !== '_') { prevChar = src[n - 1]; keepPrevChar = true; }
      src = src.substring(n);
      continue;
    }
    if (src) throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
  }
}

// First character of a scheme (letter), www., or email local part.
function isUrlStart(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122)
    || c === 46 || c === 43 || c === 45;
}

// Renders inline source to a single string (used for the inner text of
// emphasis, strong, strikethrough and links).
function inlineStr(src, st, mode) {
  const out = [];
  renderInline(src, st, out, mode);
  return out.join('');
}

function tokEscape(src, st, out, mode) {
  const cap = INL_ESCAPE.exec(src);
  if (!cap) return 0;
  out.push(mode === 'text' ? cap[1] : escapeHtml(cap[1]));
  return cap[0].length;
}

function tokTag(src, st, out, mode) {
  const cap = INL_TAG.exec(src);
  if (!cap) return 0;
  if (!st.inLink && RE_A_OPEN.test(cap[0])) st.inLink = true;
  else if (st.inLink && RE_A_CLOSE.test(cap[0])) st.inLink = false;
  if (!st.inRawBlock && RE_PRE_OPEN.test(cap[0])) st.inRawBlock = true;
  else if (st.inRawBlock && RE_PRE_CLOSE.test(cap[0])) st.inRawBlock = false;
  out.push(cap[0]);
  return cap[0].length;
}

function tokLink(src, st, out, mode) {
  if (st.linkParenPossible === false) return 0;
  const cap = INL_LINK.exec(src);
  if (!cap) return 0;
  const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(src, cap[1], labelStart)) return 0;
  const trimmedUrl = cap[2].trim();
  if (RE_ANGLE_OPEN.test(trimmedUrl)) {
    // commonmark requires matching angle brackets
    if (!RE_ANGLE_CLOSE.test(trimmedUrl)) return 0;
    // ending angle bracket cannot be escaped
    const rtrimSlash = rtrim(trimmedUrl.slice(0, -1), '\\');
    if ((trimmedUrl.length - rtrimSlash.length) % 2 === 0) return 0;
  } else {
    const lastParenIndex = findClosingBracket(cap[2], '()');
    if (lastParenIndex === -2) return 0;
    if (lastParenIndex > -1) {
      const start = cap[0].indexOf('!') === 0 ? 5 : 4;
      const linkLen = start + cap[1].length + lastParenIndex;
      cap[2] = cap[2].substring(0, lastParenIndex);
      cap[0] = cap[0].substring(0, linkLen).trim();
      cap[3] = '';
    }
  }
  const unescaped = rtrim(cap[0].slice(0, -1), '\\');
  if ((cap[0].length - unescaped.length) % 2 === 0) return 0;
  let href = cap[2];
  const title = cap[3] ? cap[3].slice(1, -1) : '';
  href = href.trim();
  if (RE_ANGLE_OPEN.test(href)) href = href.slice(1, -1);
  return outputLink(cap,
    { href: href ? href.replace(INL_ANY_PUNCT, '$1') : href,
      title: title ? title.replace(INL_ANY_PUNCT, '$1') : title },
    cap[0], st, out, mode);
}

function tokReflink(src, st, out, mode) {
  let cap = INL_REFLINK.exec(src) || INL_NOLINK.exec(src);
  if (!cap) return 0;
  const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(src, cap[1], labelStart)) return 0;
  const link = st.links[normalizeLabel(cap[2] || cap[1])];
  if (!link) {
    const ch = cap[0].charAt(0);
    out.push(mode === 'text' ? ch : escapeHtml(ch));
    return 1;
  }
  return outputLink(cap, link, cap[0], st, out, mode);
}

// Builds a link or image from a matched label: tokenizes the label text
// (HTML for a link, plain text for an image's alt), refuses a link whose
// text already holds one, and renders the <a> or <img>.
function outputLink(cap, link, raw, st, out, mode) {
  const href = link.href;
  const title = link.title || null;
  const text = cap[1].replace(RE_LINK_BRACKET_ESC, '$1');
  const isImage = cap[0].charAt(0) === '!';

  const outerInLink = st.inLink;
  const outerLinkEmitted = st.linkEmitted;
  const outerInRawBlock = st.inRawBlock;
  st.inLink = true;
  st.linkEmitted = false;
  // An image's label renders as plain text (its alt); a label rendered in
  // text mode renders as plain text too.
  const inner = inlineStr(text, st, (isImage || mode === 'text') ? 'text' : 'html');
  const textHasLink = st.linkEmitted;
  st.linkEmitted = outerLinkEmitted;
  st.inLink = outerInLink;

  if (!isImage) {
    if (textHasLink) {
      st.inRawBlock = outerInRawBlock;
      return 0;
    }
    st.linkEmitted = true;
  }

  // In text mode (image alt text) a link or image is just its plain text.
  if (mode === 'text') {
    out.push(inner);
    return raw.length;
  }

  if (isImage) {
    const cleanHref = cleanUrl(href);
    if (cleanHref === null) {
      out.push(escapeHtml(inner));
      return raw.length;
    }
    let s = `<img src="${escapeHtml(cleanHref)}" alt="${escapeHtml(inner)}"`;
    if (title) s += ` title="${escapeHtml(title)}"`;
    out.push(s + '>');
    return raw.length;
  }

  const cleanHref = cleanUrl(href);
  if (cleanHref === null) {
    out.push(inner);
    return raw.length;
  }
  let s = '<a href="' + escapeHtml(cleanHref) + '"';
  if (title) s += ' title="' + escapeHtml(title) + '"';
  out.push(s + '>' + inner + '</a>');
  return raw.length;
}

function tokEmStrong(src, maskedSrc, st, out, mode, prevChar) {
  let match = INL_EM_L.exec(src);
  if (!match) return 0;
  if (!match[1] && !match[2] && !match[3] && !match[4]) return 0;
  const delimChar = match[0][0];
  const midRun = prevChar === delimChar;
  const srcStart = maskedSrc.length - src.length;
  let runStart = srcStart;
  while (runStart > 0 && maskedSrc[runStart - 1] === delimChar) runStart--;
  const runPrevChar = [...maskedSrc.slice(Math.max(0, runStart - 2), runStart)].at(-1) ?? '';
  const runPrevPunct = runPrevChar === '*' || runPrevChar === '_' || !!INL_PUNCT.exec(runPrevChar);
  if (runStart < srcStart) prevChar = runPrevChar;
  const prevPunct = runStart < srcStart ? runPrevPunct : !!INL_PUNCT.exec(prevChar);
  if (match[4] && prevChar.match(RE_ALNUM)) return 0;
  const nextChar = match[1] || match[3] || '';
  if (!nextChar || !prevChar || prevPunct) {
    const lLength = [...match[0]].length - 1;
    let rDelim, rLength, delimTotal = lLength, midDelimTotal = 0;
    const runLength = srcStart - runStart + lLength;
    const openerCanClose = !!runPrevChar.trim() && (!!nextChar || (delimChar === '*' && !runPrevPunct));
    if (delimChar !== '*' && delimChar !== '_') return 0;
    const endReg = delimChar === '*' ? INL_EM_R_AST : INL_EM_R_UND;
    const hint = st.hintStack.at(-1);
    const lastPossible = hint ? (delimChar === '*' ? hint.star : hint.under) : -1;
    const windowStart = maskedSrc.length - src.length + lLength;
    if (lastPossible < windowStart) return 0;
    maskedSrc = maskedSrc.slice(-1 * src.length + lLength);
    const lastInWindow = lastPossible - windowStart;
    endReg.lastIndex = 0;
    while ((match = endReg.exec(maskedSrc)) !== null) {
      if (match.index > lastInWindow) break;
      rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!rDelim) continue;
      rLength = [...rDelim].length;
      if (match[3] || match[4]) {
        delimTotal += rLength;
        continue;
      } else if (match[5] || match[6] || openerCanClose) {
        if (midRun && (match[5] || match[6])) break;
        if (runLength % 3 && !((runLength + rLength) % 3)) {
          midDelimTotal += rLength;
          continue;
        }
      }
      delimTotal -= rLength;
      if (delimTotal > 0) continue;
      rLength = Math.min(rLength, rLength + delimTotal + midDelimTotal);
      const lastCharLength = [...match[0]][0].length;
      const raw = src.slice(0, lLength + match.index + lastCharLength + rLength);
      if (Math.min(lLength, rLength) % 2) {
        const text = raw.slice(1, -1);
        if (mode === 'text') out.push(inlineStr(text, st, 'text'));
        else out.push('<em>' + inlineStr(text, st, 'html') + '</em>');
        return raw.length;
      }
      const text = raw.slice(2, -2);
      if (mode === 'text') out.push(inlineStr(text, st, 'text'));
      else out.push('<strong>' + inlineStr(text, st, 'html') + '</strong>');
      return raw.length;
    }
  }
  return 0;
}

function tokCodespan(src, st, out, mode) {
  const cap = INL_CODE.exec(src);
  if (!cap) return 0;
  let text = cap[2].replace(RE_NL, ' ');
  const hasNonSpaceChars = RE_NON_SPACE.test(text);
  const hasSpaceCharsOnBothEnds = RE_LEAD_SPACE.test(text) && RE_TRAIL_SPACE.test(text);
  if (hasNonSpaceChars && hasSpaceCharsOnBothEnds) text = text.substring(1, text.length - 1);
  if (mode === 'text') out.push(text);
  else out.push(`<code>${escapeHtml(text, true)}</code>`);
  return cap[0].length;
}

function tokBr(src, st, out, mode) {
  const cap = INL_BR.exec(src);
  if (!cap) return 0;
  if (mode === 'text') out.push('');
  else out.push('<br>');
  return cap[0].length;
}

function tokDel(src, maskedSrc, st, out, mode, prevChar) {
  let match = INL_DEL_L.exec(src);
  if (!match) return 0;
  const nextChar = match[1] || '';
  if (!nextChar || !prevChar || INL_PUNCT.exec(prevChar)) {
    const lLength = [...match[0]].length - 1;
    let rDelim, rLength, delimTotal = lLength;
    const endReg = INL_DEL_R;
    const hint = st.hintStack.at(-1);
    const lastPossible = hint ? hint.tilde : -1;
    const windowStart = maskedSrc.length - src.length + lLength;
    if (lastPossible < windowStart) return 0;
    maskedSrc = maskedSrc.slice(-1 * src.length + lLength);
    const lastInWindow = lastPossible - windowStart;
    endReg.lastIndex = 0;
    while ((match = endReg.exec(maskedSrc)) !== null) {
      if (match.index > lastInWindow) break;
      rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!rDelim) continue;
      rLength = [...rDelim].length;
      if (rLength !== lLength) continue;
      if (match[3] || match[4]) {
        delimTotal += rLength;
        continue;
      }
      delimTotal -= rLength;
      if (delimTotal > 0) continue;
      rLength = Math.min(rLength, rLength + delimTotal);
      const lastCharLength = [...match[0]][0].length;
      const raw = src.slice(0, lLength + match.index + lastCharLength + rLength);
      const text = raw.slice(lLength, -lLength);
      if (mode === 'text') out.push(inlineStr(text, st, 'text'));
      else out.push('<del>' + inlineStr(text, st, 'html') + '</del>');
      return raw.length;
    }
  }
  return 0;
}

function tokAutolink(src, st, out, mode) {
  const cap = INL_AUTOLINK.exec(src);
  if (!cap) return 0;
  let text, href;
  if (cap[2] === '@') {
    text = cap[1];
    href = 'mailto:' + text;
  } else {
    text = cap[1];
    href = text;
  }
  if (mode === 'text') {
    out.push(text);
  } else {
    const cleanHref = cleanUrl(href);
    if (cleanHref === null) {
      out.push(escapeHtml(text, true));
    } else {
      out.push('<a href="' + escapeHtml(cleanHref, true) + '">' + escapeHtml(text, true) + '</a>');
    }
  }
  return cap[0].length;
}

function tokUrl(src, st, out, mode) {
  const cap = INL_URL.exec(src);
  if (!cap) return 0;
  let text, href;
  if (cap[2] === '@') {
    text = cap[0];
    href = 'mailto:' + text;
  } else {
    let prevCapZero;
    do {
      prevCapZero = cap[0];
      cap[0] = INL_BACKPEDAL.exec(cap[0])?.[0] ?? '';
    } while (prevCapZero !== cap[0]);
    text = cap[0];
    href = cap[1] === 'www.' ? 'http://' + cap[0] : cap[0];
  }
  if (mode === 'text') {
    out.push(text);
  } else {
    const cleanHref = cleanUrl(href);
    if (cleanHref === null) {
      out.push(escapeHtml(text, true));
    } else {
      out.push('<a href="' + escapeHtml(cleanHref, true) + '">' + escapeHtml(text, true) + '</a>');
    }
  }
  return cap[0].length;
}

function tokInlineText(src, st, out, mode) {
  // Fast path: the next character that can start another inline construct.
  // If the plain span before it holds no URL/email trigger and no hard
  // break, it is all text — no need to run the full text regex over it.
  const stop = RE_TEXT_STOP.exec(src);
  const end = stop ? stop.index : src.length;
  if (end > 0) {
    const span = src.slice(0, end);
    if (!spanHasTrigger(span)) {
      const escaped = st.inRawBlock;
      const text = escaped ? span : decodeNumericRefs(span);
      if (mode === 'text') out.push(text);
      else out.push(escaped ? text : escapeHtml(text));
      return end;
    }
  }
  const cap = INL_TEXT.exec(src);
  if (!cap) return 0;
  const escaped = st.inRawBlock;
  const text = escaped ? cap[0] : decodeNumericRefs(cap[0]);
  if (mode === 'text') out.push(text);
  else out.push(escaped ? text : escapeHtml(text));
  return cap[0].length;
}

// ---------------------------------------------------------------------------
// Block rendering: turns the block records into the final HTML string,
// mirroring marked's Renderer exactly.
// ---------------------------------------------------------------------------

function renderBlocks(blocks, st, out) {
  for (const block of blocks) {
    switch (block.t) {
      case 'space':
        break;
      case 'hr':
        out.push('<hr>\n');
        break;
      case 'heading': {
        const inner = [];
        renderInline(block.text, st, inner, 'html');
        out.push(`<h${block.depth}>${inner.join('')}</h${block.depth}>\n`);
        break;
      }
      case 'code': {
        // Marked's renderer: the language is the first non-space run; an
        // empty block gains no newline, a non-empty one gains exactly one
        // (its trailing newline is stripped first). Code text is always
        // escaped here (no tokenizer ever sets `escaped`).
        const langString = (block.lang || '').match(RE_NOT_SPACE_START)?.[0];
        const code = block.text ? block.text.replace(RE_NL_END, '') + '\n' : '';
        const codeHtml = escapeHtml(code, true);
        if (!langString) out.push(`<pre><code>${codeHtml}</code></pre>\n`);
        else out.push(`<pre><code class="language-${escapeHtml(langString)}">${codeHtml}</code></pre>\n`);
        break;
      }
      case 'blockquote': {
        const inner = [];
        renderBlocks(block.tokens, st, inner);
        out.push(`<blockquote>\n${inner.join('')}</blockquote>\n`);
        break;
      }
      case 'list': {
        const type = block.ordered ? 'ol' : 'ul';
        const start = block.ordered && block.start !== 1 ? ` start="${block.start}"` : '';
        const inner = [];
        for (const item of block.items) renderListItem(item, st, inner);
        out.push(`<${type}${start}>\n${inner.join('')}</${type}>\n`);
        break;
      }
      case 'html':
        out.push(block.text);
        break;
      case 'def':
        break;
      case 'paragraph': {
        const inner = [];
        renderInline(block.text, st, inner, 'html');
        if (block.checkbox) inner.unshift(checkboxHtml(block.checkbox));
        out.push(`<p>${inner.join('')}</p>\n`);
        break;
      }
      case 'text': {
        const inner = [];
        renderInline(block.text, st, inner, 'html');
        if (block.checkbox) inner.unshift(checkboxHtml(block.checkbox));
        out.push(inner.join(''));
        break;
      }
      case 'checkbox':
        out.push(checkboxHtml(block));
        break;
      case 'table': {
        let s = '<table>\n<thead>\n<tr>\n';
        for (let i = 0; i < block.header.length; i++) {
          const align = block.align[i] ? ` align="${block.align[i]}"` : '';
          const inner = [];
          renderInline(block.header[i], st, inner, 'html');
          s += `<th${align}>${inner.join('')}</th>\n`;
        }
        s += '</tr>\n</thead>\n';
        let body = '';
        for (const row of block.rows) {
          let cells = '';
          for (let j = 0; j < row.length; j++) {
            const align = block.align[j] ? ` align="${block.align[j]}"` : '';
            const inner = [];
            renderInline(row[j], st, inner, 'html');
            cells += `<td${align}>${inner.join('')}</td>\n`;
          }
          body += `<tr>\n${cells}</tr>\n`;
        }
        if (body) s += `<tbody>${body}</tbody>`;
        s += '</table>\n';
        out.push(s);
        break;
      }
    }
  }
}

function checkboxHtml(checkbox) {
  return checkbox.checked
    ? '<input checked="" disabled="" type="checkbox"> '
    : '<input disabled="" type="checkbox"> ';
}

function renderListItem(item, st, out) {
  const inner = [];
  renderBlocks(item.tokens, st, inner);
  out.push(`<li>${inner.join('')}</li>\n`);
}
