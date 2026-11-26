"""Add addressable passages to Verso's chapter HTML, before adding reader controls."""
import hashlib
from html import unescape
import re

# Verso emits paragraphs and code listings as complete p/pre elements.
ELEMENT = re.compile(r'<h[1-3]\b[^>]*\bid="(?P<section>[^"]+)"[^>]*>|'
                     r'<(?P<tag>p|pre)(?P<attrs>\s[^>]*|)>(?P<body>.*?)</(?P=tag)>', re.S)
LABEL = re.compile(r'<strong>\s*(Definition|Lemma|Theorem|Proposition|Corollary|Example|Exercise)'
                   r'\s+(\d+(?:\.\d+)+)\b')


def address_passages(page):
    start = page.index('<section>', page.index('<main>'))
    end = page.index('</main>', start)
    section = None
    counts = {}

    def address(match):
        nonlocal section
        if match['section']:
            section = match['section']
            return match[0]
        if not section or re.search(r'\bid="', match['attrs']):
            return match[0]
        content = match['body'].strip()
        text = ' '.join(unescape(re.sub(r'<[^>]+>', '', content)).split())
        if not text:
            return match[0]
        label = LABEL.match(content)
        key = (label[1].lower() + '-' + label[2].replace('.', '-') if label
               else hashlib.sha256(text.encode()).hexdigest()[:12])
        base = f'{section}-p-{key}'
        counts[base] = count = counts.get(base, 0) + 1
        anchor = base if count == 1 else f'{base}-{count}'
        return f'<{match["tag"]} id="{anchor}" data-passage' + match[0][len(match['tag']) + 1:]

    return page[:start] + ELEMENT.sub(address, page[start:end]) + page[end:]
