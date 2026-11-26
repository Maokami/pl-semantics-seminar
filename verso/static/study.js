(() => {
  const panel = document.querySelector('main .study');
  if (!panel) return;
  const {session, thread, revision} = panel.dataset;
  const main = panel.closest('main');
  const url = new URL(location.href);
  const headings = [...main.querySelectorAll('h1[id],h2[id],h3[id]')];
  const title = h => h.textContent.replace(/🔗/g, '').trim();
  const tag = 'Session ' + session;
  const repo = 'https://github.com/Maokami/pl-semantics-seminar';
  const link = (text, href) => Object.assign(document.createElement('a'), {textContent: text, href});
  function sectionAt(node) {
    return headings.filter(h => h.contains(node) || (h.compareDocumentPosition(node) & Node.DOCUMENT_POSITION_FOLLOWING)).pop() || headings[0];
  }
  function sectionURL(h) {
    const u = new URL(url); u.hash = h.id; return u.href;
  }

  const presenter = panel.querySelector('.study-links');
  for (const h of headings.filter(h => /Exercises|Reading for the Seminar|Solutions|Sources and Formalization/i.test(title(h)))) {
    presenter.append(link(title(h), sectionURL(h)), ' ');
  }
  const definitions = [...main.querySelectorAll('section li a')].filter(a => {
    const li = a.closest('li');
    return /^Definitions\./.test(li.textContent.trim());
  });
  for (const a of definitions) presenter.append(link(a.textContent, a.href), ' ');

  const key = 'pl-study-notes:' + session;
  const saved = panel.querySelector('.saved div');
  let notes = [];
  try { notes = JSON.parse(localStorage.getItem(key)) || []; } catch {}
  function persist(next) {
    try { localStorage.setItem(key, JSON.stringify(next)); notes = next; draw(); }
    catch { alert('This browser could not save the reading note.'); }
  }
  function draw() {
    saved.replaceChildren();
    if (!notes.length) saved.textContent = 'Select a passage to save it on this device.';
    for (const [i, note] of notes.entries()) {
      const row = document.createElement('p');
      const remove = Object.assign(document.createElement('button'), {textContent: 'Remove', type: 'button'});
      remove.onclick = () => persist(notes.filter((_, j) => j !== i));
      const u = new URL(url); u.hash = note.id;
      row.append(link(note.quote, u.href), ' ', remove); saved.append(row);
    }
  }
  draw();
  const menu = document.createElement('div'); menu.className = 'study-selection'; menu.hidden = true;
  const propose = link('Suggest a correction', '#');
  const save = Object.assign(document.createElement('button'), {textContent:'Save for rereading', type:'button'});
  const close = Object.assign(document.createElement('button'), {textContent:'Close', type:'button'});
  menu.append(propose, save, close); document.body.append(menu);
  let selected;
  save.onclick = () => { if (selected) persist([...notes, selected]); menu.hidden = true; };
  close.onclick = () => { menu.hidden = true; };
  function selectionChanged() {
    const sel = getSelection();
    if (!sel.rangeCount || sel.isCollapsed || !main.contains(sel.anchorNode) || !main.contains(sel.focusNode)
        || panel.contains(sel.anchorNode) || panel.contains(sel.focusNode)) { if (!menu.matches(':focus-within,:hover')) menu.hidden = true; return; }
    const quote = sel.toString().trim().slice(0, 750);
    if (!quote) return;
    const h = sectionAt(sel.getRangeAt(0).startContainer);
    selected = {id:h.id, quote};
    const u = new URL(repo + '/issues/new');
    u.search = new URLSearchParams({title:'['+tag+'] ',labels:'textbook feedback',body:
      'Section: '+sectionURL(h)+'\nRevision: '+revision+'\n\n'+quote.split('\n').map(s=>'> '+s).join('\n')+'\n\nSuggested change and reason:\n'});
    propose.href = u.href; menu.hidden = false;
  }
  document.addEventListener('selectionchange', selectionChanged);
  document.addEventListener('keydown', e => { if (e.key === 'Escape') menu.hidden = true; });

  const comments = panel.querySelector('.comments');
  comments.addEventListener('toggle', () => {
    if (!comments.open || comments.querySelector('script, iframe')) return;
    const s = document.createElement('script');
    s.src = 'https://giscus.app/client.js'; s.crossOrigin = 'anonymous'; s.async = true;
    Object.assign(s.dataset, {repo:'Maokami/pl-semantics-seminar', repoId:'R_kgDOV5jDyw',
      category:'General', categoryId:'DIC_kwDOV5jDy84DMBZ9',mapping:thread ? 'number' : 'specific',
      term:thread || tag + ' · ' + title(headings[0]), strict:'1', reactionsEnabled:'1',inputPosition:'top',theme:'preferred_color_scheme',lang:'ko'});
    comments.querySelector('.giscus').append(s);
  });
})();
