// The manuscript loads KaTeX. Preserve the author's Markdown for copying and GitHub.
window.studyMath = (() => {
  function typeset(element, tex, displayMode = false) {
    try {
      window.katex.render(tex, element, {displayMode, throwOnError:true, trust:false, maxSize:10});
    } catch {
      element.textContent = (displayMode ? '$$' : '$') + tex + (displayMode ? '$$' : '$');
      element.title = 'This expression could not be previewed.';
    }
  }

  function render(element, source, withLinks = false) {
    const formulas = [];
    const nodes = document.createDocumentFragment();
    function addText(text) {
      if (!withLinks) { nodes.append(text); return; }
      for (const part of text.split(/(https?:\/\/[^\s<>]+)/g)) {
        if (/^https?:\/\//.test(part)) {
          const a = document.createElement('a');
          a.href = part; a.textContent = part; nodes.append(a);
        } else nodes.append(part);
      }
    }
    // Skip code spans, fenced code and escaped dollars while recognizing inline and display math.
    const tokens = /```[\s\S]*?(?:```|$)|`[^`\n]*`|\\\$|\$\$([\s\S]+?)\$\$|\$(?![\s$])((?:\\.|[^$\\\n])+?)(?<!\s)\$(?!\d)/g;
    let last = 0;
    for (const match of source.matchAll(tokens)) {
      addText(source.slice(last, match.index));
      const tex = match[1] ?? match[2];
      if (tex === undefined) nodes.append(match[0]);
      else {
        const span = document.createElement('span');
        typeset(span, tex, match[1] !== undefined);
        nodes.append(span);
        formulas.push(tex);
      }
      last = match.index + match[0].length;
    }
    addText(source.slice(last)); element.replaceChildren(nodes);
    return [...new Set(formulas)];
  }
  return {typeset, render};
})();
