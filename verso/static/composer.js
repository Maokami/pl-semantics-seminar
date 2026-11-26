(() => {
  const panel = document.querySelector('.study-pilot');
  if (!panel) return;
  const {session, revision} = panel.dataset;
  const sections = [...panel.closest('main').querySelectorAll('h1[id], h2[id], h3[id]')].filter(h => !panel.contains(h));
  const root = 'https://github.com/Maokami/pl-semantics-seminar';
  const nameOf = h => h.textContent.replace(/🔗/g, '').trim();
  const entry = document.createElement('a');
  const studyURL = new URL(location.href);
  studyURL.hash = 'study-together';
  entry.className = 'study-inline';
  entry.href = studyURL.href;
  entry.textContent = 'Study together ↓';
  sections[0].after(entry);
  const dialog = document.createElement('dialog');
  dialog.className = 'reader-composer'; dialog.lang = 'en';
  dialog.setAttribute('aria-labelledby', 'composer-title');
  dialog.innerHTML = `<form>
    <div class="composer-heading"><div><small></small><h2 id="composer-title"></h2></div><button type="button" class="dismiss" aria-label="Close editor">×</button></div>
    <label>Section<select name="section"></select></label>
    <blockquote hidden></blockquote>
    <label><span class="prompt"></span><textarea name="message" rows="5" required></textarea></label>
    <p class="handoff">Write in English or Korean. Sign in to GitHub to review and post publicly.</p>
    <p class="long-draft" hidden>Copy this longer draft, then paste it into the GitHub form. <button type="button" class="copy">Copy draft</button></p>
    <footer><button type="button" class="cancel">Close</button><button type="submit" class="primary">Review on GitHub ↗</button></footer>
  </form>`;
  document.body.append(dialog);
  const form = dialog.querySelector('form');
  const select = form.elements.section, message = form.elements.message;
  const quoteBox = dialog.querySelector('blockquote');
  for (const h of sections) select.add(new Option(nameOf(h), h.id));
  const publicChapter = new URL("https://maokami.github.io/pl-semantics-seminar/chapter-" + session + "/");
  let copiedBody;
  let mode, quoted, focusOrigin;
  const draftKey = () => 'pl-composer:' + session + ':' + mode;
  function storeDraft() {
    try { sessionStorage.setItem(draftKey(), JSON.stringify({text:message.value, section:select.value, quote:quoted})); } catch {}
  }
  function open(modeName, selection) {
    focusOrigin = document.activeElement;
    mode = modeName;
    let draft = {};
    try { draft = JSON.parse(sessionStorage.getItem(draftKey())) || {}; } catch {}
    select.value = selection?.id || draft.section || sections[0].id;
    if (select.selectedIndex < 0) select.selectedIndex = 0;
    quoted = selection?.quote || (draft.section === select.value && draft.quote) || '';
    message.value = draft.text || '';
    quoteBox.textContent = quoted; quoteBox.hidden = !quoted;
    const question = mode === 'question';
    dialog.querySelector('small').textContent = nameOf(sections[0]);
    dialog.querySelector('h2').textContent = question ? 'Ask a question' : 'Suggest a correction';
    dialog.querySelector('.prompt').textContent = question ? 'What would you like to ask?' : 'What would you change?';
    message.placeholder = question ? 'Which step is unclear?' : 'Describe the change and why it would help.';
    dialog.showModal(); message.focus();
    update();
  }
  function payload() {
    const sectionURL = new URL(publicChapter); sectionURL.hash = select.value;
    const titleLine = message.value.trim().split(/\n/)[0];
    const body = [message.value.trim(), quoted && '> ' + quoted.replaceAll('\n', '\n> '),
      sectionURL.href, 'Revision: ' + revision].filter(Boolean).join('\n\n');
    const target = new URL(root + (mode === 'question' ? '/discussions/new' : '/issues/new'));
    target.searchParams.set(mode === 'question' ? 'category' : 'template', mode === 'question' ? 'q-a' : 'correction.md');
    target.searchParams.set('title', '[Session ' + session + '] ' + Array.from(titleLine).slice(0, 72).join(''));
    target.searchParams.set('body', body);
    return {target, body};
  }
  function update() {
    const {target, body} = payload();
    const needsCopy = target.href.length >= 7000;
    dialog.querySelector('.long-draft').hidden = !needsCopy;
    dialog.querySelector('.copy').textContent = copiedBody === body ? 'Copied' : 'Copy draft';
    dialog.querySelector('.primary').disabled = !message.value.trim() || (needsCopy && copiedBody !== body);
    storeDraft();
  }
  message.addEventListener('input', update);
  select.onchange = () => { quoted = ''; quoteBox.hidden = true; update(); };
  dialog.querySelector('.copy').onclick = async () => {
    const {body} = payload();
    try { await navigator.clipboard.writeText(body); }
    catch { if (window.prompt('Copy the full draft, then choose OK.', body) === null) return; }
    copiedBody = body;
    update();
  };
  form.onsubmit = e => {
    e.preventDefault();
    if (dialog.querySelector('.primary').disabled) return;
    const {target} = payload();
    if (target.href.length >= 7000) target.searchParams.delete('body');
    window.open(target.href, '_blank', 'noopener,noreferrer');
  };
  for (const b of dialog.querySelectorAll('.cancel,.dismiss')) b.onclick = () => dialog.close();
  dialog.addEventListener('close', () => { focusOrigin?.focus?.(); });
  panel.addEventListener('click', event => {
    const el = event.target.closest('[data-compose]');
    if (!el) return;
    event.preventDefault();
    open(el.dataset.compose);
  });
  panel.addEventListener('compose', e => open(e.detail.mode, e.detail.selected));
})();
