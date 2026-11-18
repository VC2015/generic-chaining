(() => {
  const chapters = [...document.querySelectorAll('.chapter')];
  const mainPane = document.querySelector('.content');
  const menu = document.getElementById('toc-toggle');
  const toc = document.getElementById('contents');
  const desktop = matchMedia('(min-width: 1024px)');
  const dialog = document.getElementById('lean-dialog');
  const dialogBody = document.getElementById('dialog-body');
  document.documentElement.classList.add('interactive');
  function menuState() {
    menu.setAttribute('aria-expanded', String(getComputedStyle(toc).display !== 'none'));
  }
  menu.onclick = () => {
    document.body.classList.toggle(desktop.matches ? 'nav-closed' : 'nav-open');
    menuState();
  };
  desktop.addEventListener('change', menuState);
  function jump() {
    const target = document.getElementById(location.hash.slice(1)) || chapters[0];
    const chapter = target.closest('.chapter') || chapters[0];
    chapters.forEach(c => { c.hidden = c !== chapter; });
    const index = chapters.indexOf(chapter);
    toc.querySelectorAll('li').forEach(li => {
      const a = li.querySelector('a');
      const active = a.hash === '#' + chapter.id;
      li.classList.toggle('current', active);
      if (active) a.setAttribute('aria-current','page'); else a.removeAttribute('aria-current');
    });
    for (const [id, offset] of [['previous', -1], ['next', 1]]) {
      const link = document.getElementById(id);
      const adjacent = chapters[index + offset];
      if (adjacent) {link.href = '#' + adjacent.id; link.removeAttribute('aria-disabled');}
      else {link.removeAttribute('href'); link.setAttribute('aria-disabled', 'true');}
    }
    if (dialog.open) dialog.close();
    const details = target.closest('details');
    if (details) details.open = true;
    mainPane.scrollTop = 0;
    if (chapter !== target) target.scrollIntoView({block:'start'});
    document.body.classList.remove('nav-open');
    menuState();
  }
  window.addEventListener('hashchange', jump);
  toc.addEventListener('click', e => {
    if (e.target.closest('a')?.hash === location.hash) jump();
  });
  document.querySelectorAll('.lean-button').forEach(button => {
    button.addEventListener('click', () => {
      const source = button.closest('.result').querySelector('.lean-source');
      dialogBody.replaceChildren(...[...source.children].filter(x => x.tagName !== 'SUMMARY').map(x => x.cloneNode(true)));
      dialog.showModal();
    });
  });
  document.getElementById('close-dialog').onclick = () => dialog.close();
  dialog.onclick = e => { if (e.target === dialog) dialog.close(); };
  for (const [id, open] of [['hide-proofs', false], ['show-proofs', true]]) {
    document.getElementById(id).onclick = () => {
      document.querySelectorAll('.chapter:not([hidden]) details.proof').forEach(d => {d.open = open;});
    };
  }
  jump();
})();
