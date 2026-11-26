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
  function sectionURL(h) {
    const u = new URL(url); u.hash = h.id; return u.href;
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
    board.after(lab);
    panel.querySelector('.meeting-tools')?.remove();
  }
  const questionList = document.createElement('div');
  questionList.setAttribute('aria-live', 'polite');
  const feed = panel.querySelector('.question-feed');
  (feed || prep || presenter).append(questionList);
  async function loadQuestions() {
    if (questionList.dataset.loading) return;
    questionList.dataset.loading = 'true';
    questionList.textContent = 'Loading recent questions…';
    const api = 'https://api.github.com/repos/Maokami/pl-semantics-seminar';
    try {
      const latest = await fetch(api + '/discussions?per_page=100&sort=updated&direction=desc');
      if (!latest.ok) throw new Error('GitHub unavailable');
      const discussions = await latest.json();
      if (feed) {
        const chapterThread = discussions.find(d => String(d.number) === thread);
        if (chapterThread) panel.querySelector('.reply-count').textContent =
          chapterThread.comments === 1 ? '1 comment' : chapterThread.comments + ' comments';
      }
      const questions = discussions.filter(d => d.category?.slug === 'q-a' &&
        (feed ? (d.state === 'open' || d.answer_chosen_at) : (d.state === 'open' && !d.answer_chosen_at)) &&
        d.title.startsWith('[' + tag + ']'));
      const list = document.createElement('ul');
      for (const q of questions.slice(0, 6)) {
        const li = document.createElement('li');
        const label = feed ? q.title.replace('[' + tag + ']', '').trim() || q.title : q.title;
        li.append(link(label, q.html_url));
        if (feed) {
          const status = document.createElement('small');
          status.textContent = q.answer_chosen_at ? 'Answered' : q.comments === 1 ? '1 reply' : q.comments + ' replies';
          li.append(status);
        }
        list.append(li);
      }
      if (list.children.length) questionList.replaceChildren(list);
      else if (feed) questionList.textContent = discussions.length < 100
        ? 'No open or answered questions for this chapter yet.'
        : 'No chapter questions among the latest 100 discussions.';
      else questionList.textContent = 'No unanswered chapter questions among the latest discussions.';
    } catch {
      if (feed) questionList.textContent = 'The preview is unavailable. All chapter questions are still available on GitHub.';
      else questionList.textContent = 'Open Unanswered questions above to read the list on GitHub.';
      delete questionList.dataset.loading;
    }
  }
  if (feed && 'IntersectionObserver' in window) {
    const observer = new IntersectionObserver(entries => {
      if (entries.some(entry => entry.isIntersecting)) {
        observer.disconnect();
        loadQuestions();
      }
    }, {rootMargin: '300px'});
    observer.observe(feed);
  } else if (feed) loadQuestions();
  else (prep || presenter).addEventListener('toggle', e => { if (e.currentTarget.open) loadQuestions(); });

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
    if (feed) {
      const details = saved.closest('details');
      details.hidden = !notes.length;
      details.querySelector('summary').textContent = 'Saved on this device (' + notes.length + ')';
    }
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
  if (panel.classList.contains('study-pilot')) {
    const compose = (mode, event) => {
      event.preventDefault();
      menu.hidden = true;
      panel.dispatchEvent(new CustomEvent('compose', {detail:{mode, selected}}));
    };
    const ask = link('Ask about this passage', '#');
    ask.onclick = event => compose('question', event);
    propose.textContent = 'Suggest a correction';
    propose.onclick = event => compose('correction', event);
    save.textContent = 'Save passage'; close.textContent = 'Close';
    menu.prepend(ask);
  }
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
    u.search = new URLSearchParams({title:'['+tag+'] ',template:'correction.md',body:
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
      term:thread || tag + ' · ' + title(headings[0]), strict:'1', reactionsEnabled:'1',inputPosition:'top',theme:'preferred_color_scheme',lang:panel.classList.contains('study-pilot') ? 'en' : 'ko'});
    comments.querySelector('.giscus').append(s);
  });
})();
