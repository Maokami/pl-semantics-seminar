"""Render the weekly reading assignments as a Verso chapter."""
from functools import lru_cache
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def study_groups():
    return json.loads((ROOT / "sessions.json").read_text())


@lru_cache(maxsize=None)
def chapter_slug(number, ko=False):
    """Return the chapter address in the requested edition."""
    folder = ROOT / ("PLBook/Ko" if ko else "PLBook")
    source = (folder / f"Ch{number:02}.lean").read_text()
    slug = re.search(r'^file := "(chapter-[0-9]+)"$', source, re.M)[1]
    if not ko and number == 7 and slug == "chapter-06":
        return "chapter-06-legacy"  # Main.lean disambiguates the earlier English chapter.
    return slug


def section_target(span):
    chapter, section = map(int, span.split("–")[0].split("."))
    slug = chapter_slug(chapter)
    source = (ROOT / "PLBook" / f"Ch{chapter:02}.lean").read_text()
    sections = re.findall(r'^# [^\n]+\n%%%\n(.*?)^%%%$', source, re.M | re.S)
    tags = [re.search(r'^tag := "([^"]+)"$', meta, re.M)[1]
            for meta in sections if 'number := false' not in meta]
    tag = tags[section - 1]
    if slug == "chapter-06-legacy":
        tag = tag.replace("ch06-", "ch06-legacy-", 1)
    return f"{slug}/index.html#{tag}"


def render_guide():
    blocks = ['''import VersoManual

open Verso.Genre Manual

#doc (Manual) "세미나 · 42회 읽기 일정" =>
%%%
tag := "seminar"
file := "seminar"
shortTitle := "Reading schedule (Korean)"
number := false
%%%

모임 전에는 ‘함께 읽을 절’을 읽고 예제의 계산을 종이에 써 봅니다. 담당자는 ‘담당자 자료’에서 해당 규칙이나 정리를 찾아 아래 과제에 필요한 식이나 유도 트리를 준비합니다. 예를 들어 3회에는 같은 순차 명령을 실행한 두 트리를 나란히 그리고, 두 중간 상태가 같아지는 곳에 귀납가정을 표시합니다.

모임은 60분입니다. 처음 10분에는 예제와 기호를 확인하고, 30분 동안 칠판에서 문제를 함께 풀고, 마지막 20분에는 다른 참가자가 핵심 단계를 다시 설명합니다. 7회와 13회에는 혼자 완성한 증명과 독서·발표 준비에 각각 걸린 시간을 확인합니다.

TAPL은 Benjamin Pierce의 _Types and Programming Languages_입니다. TAPL과 Reynolds의 목차 링크는 소장본에서 읽을 절을 찾는 데 씁니다. S1·S2·S4는 한국어 발표 자료입니다.

1–13회는 Winskel의 IMP를 따라 실행·표시·명세를 연결합니다. 작은걸음은 Concrete Semantics, 고정점은 Reynolds, 전체 정확성 실습은 Hitchhiker’s Guide를 참고합니다. 14–26회에는 TAPL의 타입 이론과 Pfenning의 표현 독립성을, 27–31회에는 Cambridge 강의 노트의 PCF를, 32–36회에는 Reynolds와 Leroy의 효과·제어·동시성을 읽고, 37–42회의 분석과 컴파일은 Leroy 강좌를 중심으로 읽습니다.

[한국어판 · 1–7회](ko/index.html) · [영문 교재 PDF](print/pl-study.pdf) · [한국어 강의계획서 PDF](print/syllabus-ko.pdf)''']
    groups = study_groups()
    shortcuts = []
    for group in groups:
        first, last = group["sessions"][0]["week"], group["sessions"][-1]["week"]
        shortcuts.append(f'* [{first}–{last}회 · {group["title"]}](seminar/index.html#week-{first:02})')
    blocks.append("\n".join(shortcuts))
    for group in groups:
        for row in group["sessions"]:
            n = row["week"]
            blocks.append(f'# {n}회 · {row["title"]}\n%%%\ntag := "week-{n:02}"\nnumber := false\n%%%')
            sections = ", ".join(f'[§{span}]({section_target(span)})' for span in row["read"])
            blocks.append(f'*함께 읽을 절*　{sections}')
            blocks.append(row["task"])
            label = row["source"].replace("_", r"\_")
            blocks.append(f'*담당자 자료*　[{label}]({row["url"]})')
            if "extra" in row:
                title, url = row["extra"]
                blocks.append(f'*심화*　[{title}]({url})')
    blocks.append("""# 심화 읽기
%%%
tag := "further-reading"
number := false
%%%

19회 뒤에는 TAPL §12.1에서 재귀 없는 단순 타입 람다 계산의 정규화를 증명할 수 있다. 28회에는 일반 재귀를 추가하여 어느 결론이 달라지는지 확인한다. 31회 뒤 재귀 타입을 연구할 때는 TAPL 20–21장의 타입 규칙과 Winskel 12–13장의 의미 모델을 대조한다.

39–41회의 분석을 확장하려면 Concrete Semantics §§13.3–13.5에서 수집 의미론과 일반 추상 해석기를, §13.9에서 넓히기(widening)와 좁히기(narrowing)를 읽는다. 동시성을 더 공부할 때는 Reynolds 9장의 통신 프로세스, 타입과 모듈을 더 공부할 때는 Reynolds 18장의 모듈 명세가 출발점이다.""")
    path = ROOT / "PLBook/Seminar.lean"
    source = "\n\n".join(blocks) + "\n"
    if not path.exists() or path.read_text() != source:
        path.write_text(source)


if __name__ == "__main__":
    render_guide()
