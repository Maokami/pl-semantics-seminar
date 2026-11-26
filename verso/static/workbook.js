// These pilot sheets use only Lean core and the workbook's pinned IMP modules.
(() => {
  const lab = document.querySelector('.lean-lab');
  if (!lab) return;
  const {session, revision} = lab.dataset;
  const firstTheorem = {'01': 'plusFour', '02': 'sequenceRun', '03': 'assignmentResult'}[session];
  const base = 'https://raw.githubusercontent.com/Maokami/pl-semantics-labs/' + revision + '/';
  const button = lab.querySelector('.lab-start');
  const status = lab.querySelector('.lab-status');
  button.hidden = false;
  lab.querySelector('.lab-instruction').textContent =
    'Find ' + firstTheorem + ' in the editor and replace sorry with a proof. Use the editor’s download option to keep your changes.';
  async function loadFile(path, expectedImport) {
    const response = await fetch(base + path);
    if (!response.ok) throw new Error(path);
    const text = await response.text();
    if (!expectedImport) return text;
    const firstLine = 'import ' + expectedImport + '\n';
    if (!text.startsWith(firstLine)) throw new Error('Unexpected workbook import');
    return text.slice(firstLine.length);
  }
  button.addEventListener('click', async () => {
    button.disabled = true;
    status.textContent = 'Loading the workbook…';
    try {
      const files = [loadFile('PLBook/IMP/Language.lean')];
      if (session === '01') files.push(loadFile('Labs/Evaluation.lean', 'PLBook.IMP.Language'));
      files.push(loadFile('Exercises/Session' + session + '.lean', session === '01' ? 'Labs.Evaluation' : 'PLBook.IMP.Language'));
      const source = '-- Workbook ' + session + ': find theorem ' + firstTheorem + ' below.\n' + (await Promise.all(files)).join('\n');
      const url = 'https://live.lean-lang.org/#project=lean-v4.35.0&code=' + encodeURIComponent(source);
      const fullScreen = document.createElement('a');
      fullScreen.href = url;
      fullScreen.target = '_blank';
      fullScreen.rel = 'noopener';
      fullScreen.textContent = 'Open starter in a new tab ↗';
      button.replaceWith(fullScreen);
      const frame = document.createElement('iframe');
      frame.src = url;
      frame.title = 'Interactive Lean workbook, Session ' + session;
      lab.append(frame);
      status.textContent = '';
    } catch {
      status.textContent = 'The browser editor could not load the workbook. Retry or open the workbook source.';
      button.disabled = false;
    }
  });
})();
