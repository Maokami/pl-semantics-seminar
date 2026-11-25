import VersoManual

open Verso.Genre Manual

#doc (Manual) "Glossary for Sessions 1–3" =>
%%%
tag := "pilot-glossary"
file := "glossary"
number := false
%%%

The Korean column gives the term to use when discussing the English text. The last column links to the definition and identifies the session that introduces it.

*Source labels.* \[This book\] marks a statement or a connection formulated here for the book’s definitions. \[Corresponding: source reference\] identifies a rule or theorem of the same form on another source’s definitions. For example, CS denotes Nipkow and Klein’s _Concrete Semantics_.

*Proof labels.* Each numbered result has one proof label.

* \[Checked\] The book build checks a proof of the stated result on the stated definitions.
* \[Selected cases checked\] The build checks only the cases identified in the text.
* \[Externally checked: appendix reference\] The cited external declaration matches the statement. The appendix identifies the repository, revision and declaration.
* \[Paper proof only: source reference\] The proof is given on paper. The reference locates it in the cited source or, for a result of this book, in the text.

:::table +header
*
  * English
  * Korean
  * Meaning
  * First use
*
  * variable name
  * 변수 이름
  * A string identifying a variable.
  * Session 1 · [A.1](imp-card/index.html#imp-a1)
*
  * arithmetic expression
  * 산술식
  * A literal, a variable, or a sum or difference of two expressions.
  * Session 1 · [A.1](imp-card/index.html#imp-a1)
*
  * constructor
  * 생성자
  * An operation that makes one form of a syntax tree from its fields.
  * Session 1 · [A.1](imp-card/index.html#imp-a1)
*
  * store
  * 상태
  * A total function from variable names to integers.
  * Session 1 · [A.2](imp-card/index.html#imp-a2)
*
  * store update
  * 상태 갱신
  * The store obtained by assigning one name its specified value and preserving all other lookups.
  * Session 1 · [A.2](imp-card/index.html#imp-a2)
*
  * evaluation function
  * 평가 함수
  * The function computing the integer value of an arithmetic expression in a store.
  * Session 1 · [A.3](imp-card/index.html#imp-a3)
*
  * structural recursion
  * 구조적 재귀
  * A definition by constructors whose recursive calls act on immediate parts.
  * Session 1 · [A.3](imp-card/index.html#imp-a3)
*
  * structural induction
  * 구조적 귀납법
  * A proof by constructors in which the claim may be assumed for the immediate parts.
  * Session 1 · [A.3](imp-card/index.html#imp-a3)
*
  * induction hypothesis
  * 귀납가정
  * The claim assumed for an immediate subexpression or subderivation in an induction step.
  * Session 1 · [A.3](imp-card/index.html#imp-a3)
*
  * judgment
  * 판단
  * An assertion whose derivability is specified by inference rules.
  * Session 1 · [A.3](imp-card/index.html#imp-a3)
*
  * evaluation judgment
  * 평가 판단
  * The assertion that an expression evaluates to a given integer in a given store.
  * Session 1 · [A.3](imp-card/index.html#imp-a3)
*
  * inference rule
  * 추론 규칙
  * A rule licensing a conclusion once the premise judgments have been derived and any additional tests have been satisfied.
  * Session 1 · [A.3](imp-card/index.html#imp-a3)
*
  * derivation
  * 유도
  * A finite tree recording the rules and premises that establish a judgment.
  * Session 1 · [A.3](imp-card/index.html#imp-a3)
*
  * inversion
  * 역전
  * Recovering possible last rules and their premises from the conclusion of a derivation.
  * Session 1 · [A.3](imp-card/index.html#imp-a3)
*
  * Boolean expression
  * 조건식
  * An expression whose value in a store is true or false.
  * Session 2 · [A.4](imp-card/index.html#imp-a4)
*
  * command
  * 명령
  * An IMP program built from skip, assignment, sequencing, a conditional, or a loop.
  * Session 2 · [A.4](imp-card/index.html#imp-a4)
*
  * guard
  * 가드
  * The Boolean expression that controls a branch or loop.
  * Session 2 · [A.4](imp-card/index.html#imp-a4)
*
  * big-step semantics
  * 큰걸음 의미론
  * Rules relating a command and its initial store to the final store of a terminating execution.
  * Session 2 · [A.5](imp-card/index.html#imp-a5)
*
  * execution judgment
  * 실행 판단
  * The assertion that a command started in a given store terminates in a specified store.
  * Session 2 · [A.5](imp-card/index.html#imp-a5)
*
  * sequencing
  * 순차 합성
  * Composition that uses the first command’s final store as the second command’s initial store.
  * Session 2 · [A.5](imp-card/index.html#imp-a5)
*
  * derived rule
  * 파생 규칙
  * A rule whose instances follow from the defining rules.
  * Session 2 · [A.5](imp-card/index.html#imp-a5)
*
  * side condition
  * 측면 조건
  * A test that must hold for a rule to apply. In a loop rule the test computes the value of the guard.
  * Session 2 · [A.5](imp-card/index.html#imp-a5)
*
  * height of a derivation
  * 유도의 높이
  * Zero at a rule without execution premises, and one plus the maximum height of the immediate execution subderivations otherwise.
  * Session 3 · [§3.1](chapter-03/index.html#ch03-s1)
*
  * determinacy
  * 결정성
  * Uniqueness of the final store for a given command and initial store, whenever a terminating execution exists.
  * Session 3 · [§3.2](chapter-03/index.html#ch03-s2)
*
  * induction property
  * 귀납 성질
  * The statement to be proved for each object of the induction. Here the object is an execution derivation.
  * Session 3 · [§3.1](chapter-03/index.html#ch03-s1)
*
  * induction on derivations
  * 유도에 대한 귀납법
  * A proof by the last rule, assuming the property for each immediate premise derivation.
  * Session 3 · [§3.1](chapter-03/index.html#ch03-s1)
*
  * partial function
  * 부분 함수
  * A function defined on a subset of its inputs, with one output at each input where it is defined.
  * Session 3 · [§3.3](chapter-03/index.html#ch03-s3)
:::
