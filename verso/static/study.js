(() => {
  const panel = document.querySelector('main .study');
  if (!panel) return;
  const {session, thread, revision} = panel.dataset;
  const main = panel.closest('main');
  const url = new URL(location.href);
  const headings = [...main.querySelectorAll('h1[id],h2[id],h3[id]')].filter(h => !panel.contains(h));
  const title = h => h.textContent.replace(/🔗/g, '').trim();
  const tag = 'Session ' + session;
  const repo = 'https://github.com/Maokami/pl-semantics-seminar';
  const link = (text, href) => Object.assign(document.createElement('a'), {textContent: text, href});
  function sectionAt(node) {
    return headings.filter(h => h.contains(node) || (h.compareDocumentPosition(node) & Node.DOCUMENT_POSITION_FOLLOWING)).pop() || headings[0];
  }
  const prep = main.querySelector('.chapter-appendix[data-kind="seminar"]');
  const presenter = panel.querySelector('.presenter');
  if (prep) {
    const links = presenter.querySelector('p');
    links.classList.add('seminar-links');
    prep.append(links);
    presenter.remove();
  }
  const exercises = main.querySelector('.chapter-appendix[data-kind="exercises"]');
  const board = panel.querySelector('.board');
  if (board && exercises) {
    exercises.insertBefore(board, exercises.querySelector('summary').nextSibling);
    const lab = panel.querySelector('.lean-lab');
    if (lab) board.after(lab);
    const tools = panel.querySelector('.meeting-tools');
    if (!tools.children.length) tools.remove();
  }
  const comments = panel.querySelector('.comments');
  const api = 'https://api.github.com/repos/Maokami/pl-semantics-seminar/discussions';
  const requested = url.searchParams.get('question');
  function discussionURL(number) {
    const dest = new URL(location.pathname, location.href);
    if (number) dest.searchParams.set('question', number);
    dest.hash = 'chapter-discussion';
    return dest.href;
  }
  function isChapterQuestion(q) {
    return q.category?.slug === 'q-a' && q.title.startsWith('[' + tag + ']');
  }
  function questionTitle(q) {
    return q.title.slice(tag.length + 2).trim() || q.title;
  }
  function whenVisible(element, run) {
    if (!('IntersectionObserver' in window)) { run(); return; }
    const observer = new IntersectionObserver(entries => {
      if (entries.some(entry => entry.isIntersecting)) {
        observer.disconnect();
        run();
      }
    }, {rootMargin:'300px'});
    observer.observe(element);
  }
  const feed = panel.querySelector('.question-feed');
  const refresh = panel.querySelector('.refresh-questions');
  let listRequest = 0;
  async function loadQuestions() {
    const request = ++listRequest;
    refresh.hidden = false;
    refresh.disabled = true;
    feed.setAttribute('aria-busy', 'true');
    if (!feed.textContent) feed.textContent = 'Loading recent questions…';
    try {
      const response = await fetch(api + '?per_page=100&sort=updated&direction=desc&_=' + Date.now(), {cache:'no-store'});
      if (!response.ok) throw new Error();
      const discussions = await response.json();
      if (request !== listRequest) return;
      const questions = discussions.filter(q => isChapterQuestion(q) && (q.state === 'open' || q.answer_chosen_at));
      const list = document.createElement('ul');
      for (const q of questions.slice(0, 6)) {
        const li = document.createElement('li');
        const status = document.createElement('small');
        status.textContent = q.answer_chosen_at ? 'Answered' : q.comments === 1 ? '1 reply' : q.comments + ' replies';
        li.append(link(questionTitle(q), discussionURL(q.number)), ' ', status);
        list.append(li);
      }
      if (list.children.length) feed.replaceChildren(list);
      else feed.textContent = discussions.length < 100 ? 'No open or answered questions for this chapter yet.'
        : 'No chapter questions among the latest 100 discussions.';
    } catch {
      if (request === listRequest) feed.textContent = 'Recent questions could not be loaded. Try Refresh or open All chapter questions.';
    } finally {
      if (request === listRequest) {
        refresh.disabled = false;
        feed.setAttribute('aria-busy', 'false');
      }
    }
  }
  refresh.onclick = loadQuestions;
  whenVisible(feed, loadQuestions);
  // Returning from GitHub can leave the same document alive, including in the back/forward cache.
  let away = false;
  function resume() {
    if (!away || document.hidden || !listRequest) return;
    away = false;
    loadQuestions();
  }
  window.addEventListener('blur', () => { away = true; });
  window.addEventListener('focus', resume);
  document.addEventListener('visibilitychange', () => { if (document.hidden) away = true; else resume(); });
  window.addEventListener('pageshow', event => { if (event.persisted) { away = true; resume(); } });


  async function loadComments() {
    const help = comments.querySelector('.discussion-help');
    let number = thread, category = 'General', categoryId = 'DIC_kwDOV5jDy84DMBZ9';
    if (requested !== null) {
      const back = link('Back to chapter discussion', discussionURL());
      try {
        if (!/^[1-9]\d{0,9}$/.test(requested)) throw new Error();
        const response = await fetch(api + '/' + requested + '?_=' + Date.now(), {cache:'no-store'});
        if (!response.ok) throw new Error();
        const q = await response.json();
        if (!isChapterQuestion(q)) throw new Error();
        number = String(q.number);
        category = q.category.name;
        categoryId = q.category.node_id;
        comments.querySelector('h3').textContent = questionTitle(q);
        const body = document.createElement('blockquote');
        body.className = 'question-body';
        studyMath.render(body, q.body || '', true);
        help.before(body);
        help.replaceChildren(back, ' · ', link('View question on GitHub ↗', q.html_url),
          ' · Sign in with GitHub to reply here.');
      } catch {
        help.replaceChildren('This question could not be loaded for this chapter. ', back);
        return;
      }
    }
    const s = document.createElement('script');
    s.src = 'https://giscus.app/client.js'; s.crossOrigin = 'anonymous'; s.async = true;
    Object.assign(s.dataset, {repo:'Maokami/pl-semantics-seminar', repoId:'R_kgDOV5jDyw',
      category, categoryId, mapping:number ? 'number' : 'specific',
      term:number || tag + ' · ' + title(headings[0]), strict:'1', reactionsEnabled:'1',
      inputPosition:'top',theme:'preferred_color_scheme',lang:'en'});
    s.onerror = () => help.append(' The embedded comments could not load. Use the GitHub link above.');
    comments.querySelector('.giscus').append(s);
  }
  whenVisible(comments, loadComments);

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
    const details = saved.closest('details');
    details.hidden = !notes.length;
    details.querySelector('summary').textContent = 'Saved on this device (' + notes.length + ')';
    if (!notes.length) saved.textContent = 'Select a passage to save it on this device.';
    for (const [i, note] of notes.entries()) {
      const row = document.createElement('p');
      const remove = Object.assign(document.createElement('button'), {textContent: 'Remove', type: 'button'});
      remove.onclick = () => persist(notes.filter((_, j) => j !== i));
      const u = new URL(url); u.hash = note.passage || note.id;
      row.append(link(note.quote, u.href), ' ', remove); saved.append(row);
    }
  }
  draw();
  const menu = document.createElement('div');
  menu.className = 'study-selection';
  menu.hidden = true;
  menu.setAttribute('role', 'group');
  menu.setAttribute('aria-label', 'Share selected passage');
  const button = label => Object.assign(document.createElement('button'), {type:'button', textContent:label});
  const copy = link('Copy link', '#');
  const ask = link('Ask a question', '#');
  const propose = link('Suggest edit', '#');
  const discuss = button('Quote for discussion');
  const save = button('Save');
  const close = button('Close');
  menu.append(copy, ask, propose, discuss, save, close);
  const status = document.createElement('div');
  status.className = 'passage-status';
  status.setAttribute('role', 'status');
  document.body.append(menu, status);
  let selected, trigger, timer;
  function announce(text) {
    clearTimeout(timer);
    status.textContent = text;
    timer = setTimeout(() => { status.textContent = ''; }, 5500);
  }
  async function write(text) {
    try { await navigator.clipboard.writeText(text); return true; }
    catch { return window.prompt('Copy the text below, then choose OK.', text) !== null; }
  }
  function hide() {
    menu.hidden = true;
    if (trigger?.isConnected) trigger.focus({preventScroll:true});
    trigger = null;
  }
  copy.onclick = async event => {
    event.preventDefault();
    if (await write(copy.href)) { hide(); announce('Passage link copied.'); }
  };
  discuss.onclick = async () => {
    const text = markdownQuote(selected.quote) + '\n\n[' + tag + ' · passage](' + copy.href + ')';
    if (!await write(text)) return;
    hide();
    if (requested !== null) { location.assign(discussionURL()); return; }
    comments.focus({preventScroll:true});
    comments.scrollIntoView({block:'center'});
    announce('Quote and link copied. Paste them into your chapter comment.');
  };
  for (const [control, mode] of [[ask, 'question'], [propose, 'correction']]) {
    control.onclick = event => {
      event.preventDefault();
      hide();
      panel.dispatchEvent(new CustomEvent('compose', {detail:{mode, selected}}));
    };
  }
  save.onclick = () => { persist([...notes, selected]); hide(); announce('Passage saved on this device.'); };
  close.onclick = hide;
  const markdownQuote = text => text.split('\n').map(line => '> ' + line).join('\n');

  function choose(block, quote) {
    status.textContent = '';
    const h = sectionAt(block);
    selected = {id:h.id, passage:block.id, quote};
    const u = new URL('https://maokami.github.io/pl-semantics-seminar/chapter-' + session + '/');
    u.hash = block.id;
    copy.href = u.href;
    const context = markdownQuote(quote) + '\n\n' + u.href + '\nRevision: ' + revision;
    const draft = (path, fields) => repo + path + '?' + new URLSearchParams({
      ...fields, title:'[' + tag + '] ', body:context,
    });
    ask.href = draft('/discussions/new', {category:'q-a'});
    propose.href = draft('/issues/new', {template:'correction.md'});
    menu.hidden = false;
  }
  function blockOf(node) {
    return (node.nodeType === Node.ELEMENT_NODE ? node : node.parentElement)?.closest('[data-passage]');
  }
  function quoteOf(fragment) {
    // KaTeX renders both visual and accessible copies of a formula.
    for (const math of fragment.querySelectorAll('.katex')) {
      const tex = math.querySelector('annotation')?.textContent;
      if (tex) math.replaceWith('$' + tex + '$');
    }
    return fragment.textContent.trim().replace(/\s+/g, ' ').slice(0, 750);
  }
  function selectionChanged() {
    const sel = getSelection();
    if (!sel.rangeCount || sel.isCollapsed) {
      if (!trigger && !menu.matches(':focus-within,:hover')) menu.hidden = true;
      return;
    }
    const range = sel.getRangeAt(0).cloneRange();
    // A selection ending inside KaTeX's visual tree still quotes the whole formula.
    const formulaAt = node => (node.nodeType === Node.ELEMENT_NODE ? node : node.parentElement)?.closest('.katex');
    const firstMath = formulaAt(range.startContainer), lastMath = formulaAt(range.endContainer);
    if (firstMath) range.setStartBefore(firstMath);
    if (lastMath) range.setEndAfter(lastMath);
    const block = blockOf(range.startContainer);
    if (!block || !blockOf(range.endContainer)) return;
    const quote = quoteOf(range.cloneContents());
    if (quote) { trigger = null; choose(block, quote); }
  }
  document.addEventListener('selectionchange', selectionChanged);

  // A picker works with a tap or keyboard when dragging over typeset math is difficult.
  const picker = panel.querySelector('.passage-picker');
  const blocks = [...main.querySelectorAll('[data-passage]')];
  let picking = false;
  function stopPicking() {
    picking = false;
    main.classList.remove('picking-passage');
    for (const block of blocks) block.removeAttribute('tabindex');
  }
  picker.onclick = () => {
    picking = true;
    main.classList.add('picking-passage');
    for (const block of blocks) block.tabIndex = 0;
    blocks[0].focus();
    announce('Choose a passage. Use Tab and Enter, or tap a paragraph. Escape cancels.');
  };
  function pick(event) {
    if (!picking || (event.type === 'keydown' && event.key !== 'Enter' && event.key !== ' ')) return;
    const block = blockOf(event.target);
    if (!block) return;
    event.preventDefault();
    stopPicking();
    trigger = picker;
    choose(block, quoteOf(block.cloneNode(true)));
    copy.focus({preventScroll:true});
  }
  main.addEventListener('click', pick, true);
  main.addEventListener('keydown', pick);
  document.addEventListener('keydown', e => {
    if (e.key === 'Escape') {
      if (picking) { stopPicking(); picker.focus(); }
      if (!menu.hidden) hide();
    }
  });

})();
