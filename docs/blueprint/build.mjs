import {execFileSync} from 'node:child_process';
import {readFileSync, writeFileSync} from 'node:fs';
import {fileURLToPath} from 'node:url';
import {parseHTML} from 'linkedom';
import {mathjax} from 'mathjax-full/js/mathjax.js';
import {TeX} from 'mathjax-full/js/input/tex.js';
import {SVG} from 'mathjax-full/js/output/svg.js';
import {liteAdaptor} from 'mathjax-full/js/adaptors/liteAdaptor.js';
import {RegisterHTMLHandler} from 'mathjax-full/js/handlers/html.js';
import {AssistiveMmlHandler} from 'mathjax-full/js/a11y/assistive-mml.js';
import 'mathjax-full/js/input/tex/ams/AmsConfiguration.js';

const local = name => new URL(name, import.meta.url);
const html = execFileSync('pandoc', [
  '-f', 'markdown', '-t', 'html5', '--mathjax', '--section-divs', '--no-highlight',
  '--wrap=none', fileURLToPath(local('../BLUEPRINT.md')),
], {encoding: 'utf8'});

// Render once for both the hosted page and the offline copy. All formulas share
// a set of vector glyphs. Assistive MathML supplies their semantic structure.
const adaptor = liteAdaptor();
AssistiveMmlHandler(RegisterHTMLHandler(adaptor));
const mathDoc = mathjax.document(html, {
  InputJax: new TeX({packages: ['base', 'ams']}),
  OutputJax: new SVG({fontCache: 'global'}),
});
mathDoc.render();
const {document: content} = parseHTML(adaptor.outerHTML(adaptor.root(mathDoc.document)));
if (content.querySelector('merror') || content.querySelectorAll('span.math').length !==
    content.querySelectorAll('span.math mjx-container').length) {
  throw new Error('A mathematical expression did not typeset correctly.');
}

const {document: page} = parseHTML(readFileSync(local('layout.html'), 'utf8'));
for (const style of content.querySelectorAll('head style')) page.head.append(style);
const fonts = local('node_modules/@fontsource-variable/open-sans/');
const styles = ['normal', 'italic'].map(style => {
  const file = new URL('files/open-sans-latin-wght-' + style + '.woff2', fonts);
  return "@font-face{font-family:'Open Sans';font-style:" + style + ';font-weight:300 800;src:url(data:font/woff2;base64,' +
    readFileSync(file).toString('base64') + ') format("woff2")}';
});
page.head.querySelector('#reader-css').textContent = [
  readFileSync(local('plastex.css'), 'utf8'), '/*' + readFileSync(new URL('LICENSE', fonts), 'utf8') + '*/',
  '/* MathJax SVG output, MathJax Consortium.\n' + readFileSync(local('node_modules/mathjax-full/LICENSE'), 'utf8') + '*/',
  ...styles, readFileSync(local('reader.css'), 'utf8'),
].join('\n');
const main = page.querySelector('main');
while (content.body.firstChild) main.append(content.body.firstChild);
const article = main.querySelector('.level1');
// The Markdown view links here for readers who opened the former entry point.
const webLink = article.querySelector('p > a[href="https://vc2015.github.io/generic-chaining/"]');
webLink?.parentElement.remove();
article.querySelector('h1 + p').className = 'byline';
article.querySelector('h1 + p').textContent = 'GPT-Sol 6.2, prompted by Victor Chernozhukov';

const results = [...article.querySelectorAll('section.level2')].filter(s => /^(lemma|theorem)-\d+$/.test(s.id));
for (const section of results) {
  const heading = section.querySelector('h2');
  const number = heading.textContent;
  const title = heading.nextElementSibling.querySelector('strong');
  const name = title.textContent.replace(/\.$/, '');
  heading.innerHTML = '<span></span> <strong></strong>';
  heading.firstElementChild.textContent = number;
  heading.lastElementChild.textContent = name;
  title.remove();
  section.classList.add('result');
  section.querySelectorAll('details').forEach(d => d.classList.add('disclosure'));
}

const index = article.querySelector('#theorem-index');
const table = index.querySelector('table');
table.querySelector('colgroup')?.remove();
const graph = index.querySelector('details');
graph.id = 'proof-dependencies';
graph.classList.add('graph', 'disclosure');
const graphCode = graph.querySelector('.mermaid');
const graphLines = graphCode.textContent.split('\n').map(line => line.trim()).filter(Boolean).slice(1);
const branchProofs = ['bounding-the-width', 'constructing-nets'];
const proofParts = article.querySelector('#theorem-2 details').querySelectorAll('p > strong:first-child');
if (proofParts.length !== 2) throw new Error('Expected the two directions of Theorem 2.');
proofParts.forEach((part, index) => { part.parentElement.id = branchProofs[index]; });

// The GitHub Mermaid diagram and the clickable offline figure share one edge list.
const dots = graphLines.map(line => {
  const node = /^(\w+)\["(.+)"\]$/.exec(line);
  if (node) {
    const [, key, label] = node;
    const match = /^(Lemma|Theorem) (\d+) · (.*)$/.exec(label);
    const id = match ? match[1].toLowerCase() + '-' + match[2] :
      {upper: branchProofs[0], lower: branchProofs[1]}[key];
    if (!id) throw new Error('Unmapped graph node: ' + key);
    const text = match ? match[1] + ' ' + match[2] + '\n' + match[3] : label;
    return key + ' [label=' + JSON.stringify(text) + ', URL="#' + id + '", tooltip=' +
      JSON.stringify(label) + ', fillcolor="' + (key.startsWith('t') ? '#cfe3fe' : '#f0f6ff') + '"]';
  }
  const edge = /^(\w+) --> (\w+)$/.exec(line);
  if (!edge) throw new Error('Unrecognized dependency: ' + line);
  return edge[1] + ' -> ' + edge[2];
});
const dot = 'digraph blueprint { graph [rankdir=TB, bgcolor="transparent", nodesep=.23, ranksep=.38, pad=.10];' +
  'node [shape=ellipse, style="filled", fontname="DejaVu Sans", fontsize=10, margin=".13,.09", color="#5786bc", fontcolor="#17385e"];' +
  'edge [color="#7690ab" arrowsize=.62];\n' + dots.join(';\n') + ';}';
const graphSvg = execFileSync('dot', ['-Tsvg'], {input: dot, encoding: 'utf8'}).split('<svg')[1];
const plot = page.createElement('div');
plot.className = 'graph-plot';
plot.innerHTML = '<svg' + graphSvg;
plot.querySelector('svg').setAttribute('aria-label', 'Proof dependencies of the mixed-tail and Gaussian theorems');
for (const a of plot.querySelectorAll('a')) {
  a.setAttribute('href', a.getAttribute('xlink:href'));
  a.setAttribute('aria-label', a.getAttribute('xlink:title'));
}
graphCode.replaceWith(plot);

// Reproduce the chapter sequence in the PDF. Source anchors remain stable in
// the single-file reader, including links from the old standalone blueprint.
const chapters = [
  ['overview', 'Finite generic chaining in Lean', []],
  ['mixed-tails', '1 Mixed tails and the expected maximum', ['notation', 'theorem-1', 'lemma-1', 'lemma-2']],
  ['gaussian-width', '2 Gaussian width and comparison', ['theorem-2', 'lemma-3', 'lemma-4']],
  ['local-growth', '3 From local Gaussian width to a sequence of nets', ['lemma-5', 'lemma-6']],
  ['rectangles', '4 Application to rectangle probabilities', ['lemma-7', 'application-to-the-rectangle-clt']],
  ['verification', '5 Checking the Lean statements', ['sources-and-verification']],
  ['dependencies', 'Dependency graph', []],
];
const contents = page.querySelector('#contents ul');
const chapterPages = new Map();
for (const [id, title, sectionIds] of chapters) {
  const chapter = page.createElement('article');
  chapter.id = id;
  chapter.className = 'chapter';
  main.append(chapter);
  chapterPages.set(id, chapter);
  const h = page.createElement('h1');
  h.textContent = title;
  chapter.append(h);
  for (const sectionId of sectionIds) chapter.append(page.getElementById(sectionId));
  const li = page.createElement('li');
  const link = page.createElement('a');
  link.href = '#' + id;
  link.textContent = id === 'overview' ? 'Overview and theorem index' : title;
  li.append(link);
  contents.append(li);
}
const intro = chapterPages.get('overview');
intro.querySelector('h1').remove();
intro.id = 'overview';
index.querySelector('p').textContent = 'Select a result to read its statement. Open Proof for the argument or L∃∀N for the checked Lean declarations and their exact types.';
while (article.firstChild) intro.append(article.firstChild);
article.remove();
const oldAnchor = page.createElement('span');
oldAnchor.id = 'finite-generic-chaining-in-lean';
intro.prepend(oldAnchor);
const graphPage = chapterPages.get('dependencies');
const graphBody = page.createElement('div');
graphBody.id = 'proof-dependencies';
graph.removeChild(graph.querySelector('summary'));
while (graph.firstChild) graphBody.append(graph.firstChild);
graph.replaceWith(Object.assign(page.createElement('a'), {href:'#dependencies', textContent:'View the dependency graph'}));
graphPage.append(graphBody);
const overviewLinks = page.createElement('nav');
overviewLinks.className = 'local_toc';
overviewLinks.setAttribute('aria-label','Chapters');
overviewLinks.append(contents.cloneNode(true));
intro.append(overviewLinks);
const tocFooter = page.createElement('li');
tocFooter.classList.add('resource-links');
tocFooter.innerHTML = '<a href="https://github.com/VC2015/generic-chaining/blob/main/docs/REPORT.pdf">PDF report</a><a href="https://github.com/VC2015/generic-chaining">GitHub</a>';
contents.append(tocFooter);
for (const section of results) {
  const heading = section.querySelector('h2');
  const number = heading.firstElementChild.textContent;
  const title = heading.lastElementChild.textContent;
  const lead = heading.nextElementSibling;
  const statement = page.createElement('div');
  statement.className = 'statement';
  const proof = section.querySelector('details');
  const lean = proof.nextElementSibling;
  const leanLinks = [...section.querySelectorAll(':scope > p')].find(p => p.firstElementChild?.textContent === 'Lean.');
  const uses = leanLinks.nextElementSibling;
  leanLinks.firstElementChild.remove();
  lean.querySelector('summary').after(leanLinks);
  while (lead.nextElementSibling && lead.nextElementSibling !== uses && lead.nextElementSibling !== proof) {
    statement.append(lead.nextElementSibling);
  }
  const proofLabel = proof.querySelector('summary');
  proofLabel.textContent = 'Proof';
  proofLabel.title = 'Read the proof outline';
  proof.className = 'proof';
  proof.append(uses);
  const proofBody = page.createElement('div');
  proofBody.className = 'proof_content';
  while (proofLabel.nextSibling) proofBody.append(proofLabel.nextSibling);
  proof.append(proofBody);
  section.insertBefore(lead, heading);
  heading.after(statement);
  heading.className = 'thmheading';
  heading.innerHTML = '<span class="thm-name"></span><span class="tools"><a class="permalink" aria-label="Link to statement">#</a><button class="lean-button" aria-haspopup="dialog">L∃∀N</button></span><span class="check" title="Proved in Lean" aria-label="Proved in Lean">✓</span>';
  heading.firstElementChild.textContent = number + '. (' + title + ')';
  heading.querySelector('a').href = '#' + section.id;
  heading.querySelector('button').setAttribute('aria-label', 'Lean declarations for ' + number);
  lean.className = 'lean-source';
  lean.querySelector('summary').textContent = 'Lean declarations and types';
}

for (const a of page.querySelectorAll('a[href^="#"]')) {
  if (!page.getElementById(a.getAttribute('href').slice(1))) throw new Error('Broken link: ' + a);
}
page.querySelector('#navigation-script').textContent = readFileSync(local('navigation.js'), 'utf8');
const output = '<!doctype html>\n' + page.documentElement.outerHTML + '\n';
writeFileSync(local('../BLUEPRINT.html'), output);
console.log('Built ' + results.length + ' results and ' + page.querySelectorAll('mjx-container').length + ' formulas.');
