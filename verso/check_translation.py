"""Check items that must survive translation. Mathematical prose still needs review."""
from collections import Counter
from pathlib import Path
import re

from editions import ROOT, units

PATTERNS = {
    'section tags': r'^tag := "([^"]+)"',
    'chapter file': r'^file := "([^"]+)"',
    'Lean panels': r'^```lean\n([\s\S]*?)\n```',
    'mathematical formulas': r'\$\$?`([^`]+)`',
    'external sources': r'\]\((https?://[^ )]+)\)',
}


def check():
    for n in next(units(True))[-1]:
        name = f'Ch{n:02}.lean'
        english, korean = [(directory/name).read_text() for directory in
                           (ROOT/'PLBook', ROOT/'PLBook/Ko')]
        for label, pattern in PATTERNS.items():
            expected, got = [Counter(re.findall(pattern,s,re.M)) for s in (english,korean)]
            if expected != got:
                raise ValueError(f'{name}: {label}: missing {expected-got}, added {got-expected}')
        if english.count('\n# ') != korean.count('\n# '):
            raise ValueError(f'{name}: different section count')
    print('All seven translations preserve section identifiers, formulas, Lean panels and references.')


if __name__ == '__main__':
    check()
