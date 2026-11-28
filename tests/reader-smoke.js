// Runs on the generated chapter, with external requests disabled by the test server.
window.addEventListener('load', () => {
  function check(condition, message) {
    if (!condition) throw new Error(message);
  }
  const dialog = document.querySelector('.reader-composer');
  const menu = document.querySelector('.study-selection');
  const blocks = document.querySelectorAll('main [data-passage]');
  function pick(block) {
    document.querySelector('.passage-picker').click();
    block.click();
  }
  const message = dialog.querySelector('textarea');
  const close = () => dialog.querySelector('.cancel').click();
  try {
    const expected = 'ch01-s4-p-example-1-2-equation-1';
    check(location.hash === '#' + expected && document.getElementById(expected).querySelector('code.math'),
          'Historical feedback link did not resolve to the derivation');
    check(document.querySelector('[data-review-source="issues/13"] a:last-child').hash === '#' + expected,
          'Published decision lost its passage');
    pick(blocks[0]);
    const rect = menu.getBoundingClientRect();
    check(rect.width > 0 && rect.left >= 0 && rect.right <= innerWidth + 1, 'Passage menu overflow');
    menu.children[1].click();
    message.value = 'A question about the first passage';
    message.dispatchEvent(new Event('input'));
    close();
    pick(blocks[1]);
    menu.children[1].click();
    check(message.value === '', 'Question draft leaked into another passage');
    close();
    pick(blocks[0]);
    menu.children[1].click();
    check(message.value === 'A question about the first passage', 'Returning to the original passage lost its draft');
    close();
    pick(blocks[0]);
    menu.children[4].click();
    pick(blocks[0]);
    menu.children[4].click();
    check(document.querySelectorAll('.saved div > p').length === 1, 'Duplicate bookmark');
    pick(blocks[1]);
    menu.children[5].click();
    check(menu.hidden && document.activeElement === blocks[1], 'Close lost the reading position');
    document.body.dataset.readerTest = 'passed';
  } catch (error) {
    document.body.dataset.readerTest = error.message;
  }
});
