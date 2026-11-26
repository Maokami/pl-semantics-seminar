// Verso links to directory indexes. Browsers require the filename on file: URLs.
if (location.protocol === 'file:') {
  document.addEventListener('DOMContentLoaded', () => {
    for (const link of document.querySelectorAll('a[href]')) {
      const url = new URL(link.href);
      if (url.protocol === 'file:' && url.pathname.endsWith('/')) {
        url.pathname += 'index.html';
        link.href = url.href;
      }
    }
  });
}

// Keep the original sections, IDs and permalink links available to the table of contents.
(() => {
  if (!document.querySelector('main .study')) return;
  const kinds = new Map([
    ['Exercises', 'exercises'], ['Reading for the Seminar', 'seminar'],
    ['Solutions and Further Reading', 'solutions'], ['Sources and Formalization', 'sources'],
  ]);
  const disclosures = [];
  for (const heading of document.querySelectorAll('main section > h2[id]')) {
    const name = heading.textContent.replace(/🔗/g, '').trim();
    if (!kinds.has(name)) continue;
    const section = heading.parentElement;
    const details = document.createElement('details');
    const summary = document.createElement('summary');
    details.className = 'chapter-appendix';
    details.dataset.kind = kinds.get(name);
    const content = [...section.childNodes];
    summary.append(heading);
    details.append(summary, ...content.filter(node => node !== heading));
    section.append(details);
    disclosures.push(details);
  }
  function reveal(hash) {
    let id;
    try { id = decodeURIComponent(hash.slice(1)); } catch { return; }
    const target = document.getElementById(id);
    const details = target?.closest('.chapter-appendix');
    if (details) {
      details.open = true;
      target.scrollIntoView();
    }
  }
  reveal(location.hash);
  window.addEventListener('hashchange', () => reveal(location.hash));
  document.addEventListener('click', event => {
    const a = event.target.closest('a[href]');
    if (!a) return;
    const url = new URL(a.href);
    if (url.pathname === location.pathname && url.origin === location.origin && url.hash === location.hash) reveal(url.hash);
  });
  let closed = [];
  window.addEventListener('beforeprint', () => {
    closed = disclosures.filter(d => !d.open);
    closed.forEach(d => { d.open = true; });
  });
  window.addEventListener('afterprint', () => closed.forEach(d => { d.open = false; }));
})();
