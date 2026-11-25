"""Check items that must survive translation. Mathematical prose still needs review."""
from collections import Counter
from pathlib import Path
import re
import hashlib
import json

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


# These Korean chapters still translate the English sources at 1238e83.
# Keep checking their structural content even in a build tree without Git history.
LEGACY_ENGLISH = {
    "Ch01.lean": "e21e6773568b90be37962057ac58827dc24b53403f0a9a94267756f61ecde4e2",
    "Ch02.lean": "a8be99f1972feb5febc31afb1667804506c12fd6fdbd834e62f125d3e0673cd1",
    "Ch04.lean": "0959583b0d4217d798f0771a05f038c8a9a2b550251c5e179fdddb2baddcc1c2",
    "Ch05.lean": "74cc9e84023b099693335d5f330d1fb980b70e61473b49f56c53b6089b829579",
    "Ch06.lean": "84ae179d10d94926de0fe162d0ae122c1b57e6a63f2885f0c80248d5020bc336",
    "Ch07.lean": "0b7cd4eebe9daf947de6c99504799d8bc67611354510c25d0291109d2265730e",
}


def translation_signature(text):
    counts = [sorted(Counter(re.findall(p, text, re.M)).items()) for p in PATTERNS.values()]
    data = json.dumps([text.count('\n# '), *counts], ensure_ascii=False)
    return hashlib.sha256(data.encode()).hexdigest()


def check():
    check_pilot_terms()
    for n in next(units(True))[-1]:
        name = f'Ch{n:02}.lean'
        if name == PILOT.name:
            continue
        english, korean = [(directory/name).read_text() for directory in
                           (ROOT/'PLBook', ROOT/'PLBook/Ko')]
        if name in LEGACY_ENGLISH:
            if translation_signature(korean) != LEGACY_ENGLISH[name]:
                raise ValueError(f'{name}: Korean translation differs from the English source at 1238e83')
            continue
        for label, pattern in PATTERNS.items():
            expected, got = [Counter(re.findall(pattern,s,re.M)) for s in (english,korean)]
            if expected != got:
                raise ValueError(f'{name}: {label}: missing {expected-got}, added {got-expected}')
        if english.count('\n# ') != korean.count('\n# '):
            raise ValueError(f'{name}: different section count')
    print('Legacy translations match their originals. Korean pilot and IMP card pass the glossary check.')


if __name__ == '__main__':
    check()
