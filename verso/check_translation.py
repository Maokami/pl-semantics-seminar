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


# The Korean v1.2 pilot has its own definitions, proof and source apparatus.
PILOT = ROOT / 'PLBook/Ko/Ch03.lean'
CARD = ROOT / 'PLBook/Ko/LanguageCard.lean'
GLOSSARY = ROOT / 'PLBook/Ko/Glossary.lean'


def check_pilot_terms():
    """Read the forbidden spellings from the published glossary itself."""
    forbidden = set()
    for line in GLOSSARY.read_text().splitlines():
        if not line.startswith('* *'):
            continue
        _, marker, variants = line.partition(' · 금지 변형 ')
        if not marker:
            raise ValueError(f'Missing glossary column: {line}')
        if variants != '없음':
            spellings = re.findall(r'`([^`]+)`', variants)
            if not spellings:
                raise ValueError(f'Invalid glossary variants: {variants}')
            forbidden.update(spellings)
    for path in (PILOT, CARD):
        for number, line in enumerate(path.read_text().splitlines(), start=1):
            for variant in forbidden:
                if variant in line:
                    raise ValueError(f'{path.name}:{number}: glossary forbids {variant!r}')


def check():
    check_pilot_terms()
    for n in next(units(True))[-1]:
        name = f'Ch{n:02}.lean'
        if name == PILOT.name:
            continue
        english, korean = [(directory/name).read_text() for directory in
                           (ROOT/'PLBook', ROOT/'PLBook/Ko')]
        for label, pattern in PATTERNS.items():
            expected, got = [Counter(re.findall(pattern,s,re.M)) for s in (english,korean)]
            if expected != got:
                raise ValueError(f'{name}: {label}: missing {expected-got}, added {got-expected}')
        if english.count('\n# ') != korean.count('\n# '):
            raise ValueError(f'{name}: different section count')
    print('Legacy translations match their originals. Korean pilot and IMP card pass the glossary check.')


if __name__ == '__main__':
    check()
