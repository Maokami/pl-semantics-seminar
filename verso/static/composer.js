(() => {
  const panel = document.querySelector('.study-pilot');
  if (!panel) return;
  const {session, revision} = panel.dataset;
  const sections = [...panel.closest('main').querySelectorAll('h1[id], h2[id], h3[id]')];
  const root = 'https://github.com/Maokami/pl-semantics-seminar';
  const nameOf = h => h.textContent.replace(/🔗/g, '').trim();
  const bar = document.createElement('nav');
  bar.className = 'study-inline'; bar.lang = 'ko'; bar.ariaLabel = '이 장에 참여하기';
  bar.innerHTML = '<button type="button" data-compose="question">질문 쓰기</button><button type="button" data-compose="correction">수정 제안</button><button type="button" data-discuss>의견·답글 쓰기</button>';
  sections[0].after(bar);
  const dialog = document.createElement('dialog');
  dialog.className = 'reader-composer'; dialog.lang = 'ko';
  dialog.setAttribute('aria-labelledby', 'composer-title');
  dialog.innerHTML = `<form>
    <header><div><small></small><h2 id="composer-title"></h2></div><button type="button" class="dismiss" aria-label="작성 창 닫기">×</button></header>
    <label>어느 절에 관한 글인가요?<select name="section"></select></label>
    <blockquote hidden></blockquote>
    <label><span class="prompt"></span><textarea name="message" rows="5" required></textarea></label>
    <p class="handoff">다음 화면에서 내용을 확인한 뒤 공개 게시합니다. GitHub 로그인이 필요합니다.</p>
    <p class="long-draft" hidden>긴 글은 복사한 뒤 GitHub 본문에 붙여 넣어 주세요. <button type="button" class="copy">본문 복사</button></p>
    <footer><button type="button" class="cancel">닫기</button><button type="submit" class="primary">GitHub에서 확인 ↗</button></footer>
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
  function currentSection() {
    return sections.filter(h => h.getBoundingClientRect().top <= 100).pop() || sections[0];
  }
  function open(modeName, selection) {
    focusOrigin = document.activeElement;
    mode = modeName;
    let draft = {};
    try { draft = JSON.parse(sessionStorage.getItem(draftKey())) || {}; } catch {}
    select.value = selection?.id || draft.section || currentSection().id;
    if (select.selectedIndex < 0) select.selectedIndex = 0;
    quoted = selection?.quote || (draft.section === select.value && draft.quote) || '';
    message.value = draft.text || '';
    quoteBox.textContent = quoted; quoteBox.hidden = !quoted;
    const question = mode === 'question';
    dialog.querySelector('small').textContent = nameOf(sections[0]);
    dialog.querySelector('h2').textContent = question ? '질문 쓰기' : '수정 제안';
    dialog.querySelector('.prompt').textContent = question ? '어느 부분이 궁금한가요?' : '어떻게 바꾸면 좋을까요?';
    message.placeholder = question ? '어디까지 이해했고, 어느 단계에서 막혔나요?' : '현재 문장에서 고칠 부분과 그 이유를 적어 주세요.';
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
    dialog.querySelector('.copy').textContent = copiedBody === body ? '복사됨' : '본문 복사';
    dialog.querySelector('.primary').disabled = !message.value.trim() || (needsCopy && copiedBody !== body);
    storeDraft();
  }
  message.addEventListener('input', update);
  select.onchange = () => { quoted = ''; quoteBox.hidden = true; update(); };
  dialog.querySelector('.copy').onclick = async () => {
    const {body} = payload();
    try { await navigator.clipboard.writeText(body); }
    catch { if (window.prompt('전체 본문을 복사한 뒤 확인을 누르세요.', body) === null) return; }
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
  document.addEventListener('click', event => {
    const el = event.target.closest('[data-compose],[data-discuss]');
    if (!el || !(panel.contains(el) || bar.contains(el))) return;
    event.preventDefault();
    if (el.dataset.compose) open(el.dataset.compose);
    else {
      const comments = panel.querySelector('.comments');
      comments.open = true; comments.querySelector('summary').focus(); comments.scrollIntoView({block:'start'});
    }
  });
  panel.addEventListener('compose', e => open(e.detail.mode, e.detail.selected));
})();
