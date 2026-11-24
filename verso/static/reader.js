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
