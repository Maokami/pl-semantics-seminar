import VersoManual

open Verso.Genre Manual

#doc (Manual) "Glossary" =>
%%%
tag := "glossary"
file := "glossary"
number := false
%%%

The Korean column gives the term to use when discussing the English text. The last column links to the definition and identifies the session that introduces it.

*Reading the chapter notes.* Each chapter ends with *Sources and Formalization*. Look up a result by its number. The source describes where the statement comes from. The proof note describes what has been verified.

* *Formulated in this book* (자체 진술). The book formulates the statement for its own definitions.
* *Corresponds to* (대응 정리). The cited result has the same form on the source’s definitions. CS abbreviates Nipkow and Klein’s _Concrete Semantics_.
* *Source* (원전). The cited work supplies the statement.
* *Checked in Lean* (Lean으로 검사됨). The book build checks a proof of the stated result on the stated definitions.
* *Selected cases checked in Lean* (일부 경우만 Lean으로 검사됨). The build checks the cases identified in the note.
* *Externally checked* (외부에서 검사됨). The statement matches a checked declaration in the cited development. The linked card gives the repository, revision and declaration.
* *Paper proof only* (종이 증명만). The note locates the argument in the chapter or its source and identifies a sketch or an omitted proof where applicable.

*Order conventions.* In [§8.4](chapter-08/index.html#ch08-s4) and [§34.1](chapter-34/index.html#ch34-s1), moving upward in the information order can make an undefined result defined. In [§17.1](chapter-17/index.html#ch17-s1), moving upward in the precision order can replace a known integer by the unknown abstract value. For type substitutions in [C.5](lambda-card/index.html#lambda-c5), the more general substitution is on the left: the right substitution factors through it.

# Part 1 · IMP
%%%
tag := "glossary-part-1"
number := false
%%%

:::table +header
*
  * English
  * Korean
  * Meaning
  * First use
*
  * arithmetic expression
  * 산술식
  * A literal, a variable, or a sum or difference of two expressions.
  * Session 1 · [A.1](imp-card/index.html#imp-a1)
*
  * binder
  * 바인더
  * A syntactic construct that binds occurrences of a name within its scope.
  * Session 1 · [§1.3](chapter-01/index.html#ch01-s3)
*
  * constructor
  * 생성자
  * An operation that builds a syntax tree from its fields.
  * Session 1 · [§1.1](chapter-01/index.html#ch01-s1)
*
  * derivation
  * 유도
  * A finite tree recording the rules and premises that establish a judgment.
  * Session 1 · [§1.4](chapter-01/index.html#ch01-s4)
*
  * evaluation function
  * 평가 함수
  * The function computing the integer value of an arithmetic expression in a store.
  * Session 1 · [§1.2](chapter-01/index.html#ch01-s2)
*
  * evaluation judgment
  * 평가 판단
  * The assertion that an expression evaluates to a given integer in a given store.
  * Session 1 · [§1.4](chapter-01/index.html#ch01-s4)
*
  * free variable
  * 자유 변수
  * A variable with an occurrence outside the scope of any binder for that name.
  * Session 1 · [§1.3](chapter-01/index.html#ch01-s3)
*
  * IMP store
  * 상태
  * A total function from variable names to integers.
  * Session 1 · [§1.1](chapter-01/index.html#ch01-s1)
*
  * IMP store update
  * 상태 갱신
  * The store obtained by assigning one name its specified value and preserving all other lookups.
  * Session 1 · [§1.1](chapter-01/index.html#ch01-s1)
*
  * induction hypothesis
  * 귀납가정
  * The claim assumed for an immediate subexpression or subderivation in an induction step.
  * Session 1 · [§1.1](chapter-01/index.html#ch01-s1)
*
  * induction on derivations
  * 유도에 대한 귀납법
  * A proof by the last rule, assuming the property for each immediate premise derivation.
  * Session 1 · [§1.5](chapter-01/index.html#ch01-s5)
*
  * induction property
  * 귀납 성질
  * The statement to be proved for each object of the induction.
  * Session 1 · [§1.5](chapter-01/index.html#ch01-s5)
*
  * inference rule
  * 추론 규칙
  * A rule licensing a conclusion once the premise judgments have been derived and any additional tests have been satisfied.
  * Session 1 · [§1.4](chapter-01/index.html#ch01-s4)
*
  * inversion
  * 역전
  * Recovering possible last rules and their premises from the conclusion of a derivation.
  * Session 1 · [§1.4](chapter-01/index.html#ch01-s4)
*
  * judgment
  * 판단
  * An assertion whose derivability is specified by inference rules.
  * Session 1 · [§1.4](chapter-01/index.html#ch01-s4)
*
  * structural induction
  * 구조적 귀납법
  * A proof by constructors in which the claim may be assumed for the immediate parts.
  * Session 1 · [§1.1](chapter-01/index.html#ch01-s1)
*
  * structural recursion
  * 구조적 재귀
  * A definition by constructors whose recursive calls act on immediate parts.
  * Session 1 · [§1.2](chapter-01/index.html#ch01-s2)
*
  * variable name
  * 변수 이름
  * A string identifying a variable.
  * Session 1 · [§1.1](chapter-01/index.html#ch01-s1)
*
  * big-step semantics
  * 큰걸음 의미론
  * Rules relating a complete computation to its result.
  * Session 2 · [§2.2](chapter-02/index.html#ch02-s2)
*
  * Boolean expression
  * 조건식
  * An expression whose value in a store is true or false.
  * Session 2 · [§2.1](chapter-02/index.html#ch02-s1)
*
  * command
  * 명령
  * An IMP program built from skip, assignment, sequencing, a conditional, or a loop.
  * Session 2 · [§2.1](chapter-02/index.html#ch02-s1)
*
  * derived rule
  * 파생 규칙
  * A rule whose instances follow from the defining rules.
  * Session 2 · [§2.2](chapter-02/index.html#ch02-s2)
*
  * execution judgment
  * 실행 판단
  * The assertion that a command started in a given store terminates in a specified store.
  * Session 2 · [§2.2](chapter-02/index.html#ch02-s2)
*
  * guard
  * 가드
  * The Boolean expression that controls a branch or loop.
  * Session 2 · [§2.1](chapter-02/index.html#ch02-s1)
*
  * height of a derivation
  * 유도의 높이
  * Zero at a rule without execution premises, and one plus the maximum height of the immediate execution subderivations otherwise.
  * Session 2 · [§2.4](chapter-02/index.html#ch02-s4)
*
  * sequencing
  * 순차 합성
  * Composition that uses the first command’s final store as the second command’s initial store. For state transformers, extend the second transformer strictly and compose it with the first (§8.2).
  * Session 2 · [§2.2](chapter-02/index.html#ch02-s2)
*
  * side condition
  * 측면 조건
  * A test that must hold for a rule to apply. In a loop rule the test computes the value of the guard.
  * Session 2 · [§2.2](chapter-02/index.html#ch02-s2)
*
  * command determinacy
  * 결정성
  * Uniqueness of the final store for a given command and initial store, whenever a terminating execution exists.
  * Session 3 · [§3.2](chapter-03/index.html#ch03-s2)
*
  * partial function and its graph
  * 부분 함수와 그 그래프
  * A function defined on a subset of its inputs, with one output at each input where it is defined. Its graph is the set of its input–output pairs.
  * Session 3 · [§3.3](chapter-03/index.html#ch03-s3)
*
  * constructor equation
  * 생성자 등식
  * An equation giving the result at one constructor in terms of its fields and the results at its children.
  * Session 4 · [§4.1](chapter-04/index.html#ch04-s1)
*
  * fold
  * 접기
  * A function on expressions computed by replacing each constructor with its specified operation.
  * Session 4 · [§4.1](chapter-04/index.html#ch04-s1)
*
  * configuration
  * 구성
  * A pair consisting of a residual command and the current store.
  * Session 5 · [§5.1](chapter-05/index.html#ch05-s1)
*
  * finite path
  * 유한 경로
  * Zero or more consecutive transitions from one configuration to another.
  * Session 5 · [§5.2](chapter-05/index.html#ch05-s2)
*
  * infinite path
  * 무한 경로
  * A sequence of configurations indexed by the natural numbers, with a transition at each successive pair.
  * Session 5 · [§5.3](chapter-05/index.html#ch05-s3)
*
  * progress
  * 진행
  * Every configuration whose command is different from skip has a successor.
  * Session 5 · [§5.2](chapter-05/index.html#ch05-s2)
*
  * residual command
  * 잔여 명령
  * The command describing the work still to do.
  * Session 5 · [§5.1](chapter-05/index.html#ch05-s1)
*
  * transition
  * 전이
  * A single step between configurations allowed by the small-step rules.
  * Session 5 · [§5.1](chapter-05/index.html#ch05-s1)
*
  * path lifting
  * 경로 올리기
  * Placing every command on a path in the same sequence context while retaining its store and each edge.
  * Session 6 · [§6.1](chapter-06/index.html#ch06-s1)
*
  * sequence context
  * 순차 합성 문맥
  * The operation of placing a command to the left of a fixed suffix in a sequence.
  * Session 6 · [§6.1](chapter-06/index.html#ch06-s1)
*
  * execution relation
  * 실행 관계
  * The set of initial–final store pairs for a command.
  * Session 7 · [§7.1](chapter-07/index.html#ch07-s1)
*
  * loop unfolding
  * 루프 펼침
  * Replacing `while b do c` by `if b then (c; while b do c) else skip`.
  * Session 7 · [§7.2](chapter-07/index.html#ch07-s2)
*
  * observation
  * 관찰
  * What an equivalence compares about a run. In Definition 7.1 it is the entire final store of each terminating execution.
  * Session 7 · [§7.1](chapter-07/index.html#ch07-s1)
*
  * program equivalence
  * 프로그램 동치
  * Two commands have the same set of initial–final store pairs.
  * Session 7 · [§7.1](chapter-07/index.html#ch07-s1)
*
  * bottom
  * 바닥
  * The element ⊥, which is not a store. As the result of a command it records that there is no final store (nontermination).
  * Session 8 · [§8.1](chapter-08/index.html#ch08-s1)
*
  * increasing sequence
  * 증가하는 열
  * r\_n ⊑ r\_\{n+1\} for every n.
  * Session 8 · [§8.4](chapter-08/index.html#ch08-s4)
*
  * information order
  * 정보 순서
  * An outcome is below another if it is bottom or the two are equal. Moving upward adds information. State transformers are ordered pointwise.
  * Session 8 · [§8.4](chapter-08/index.html#ch08-s4)
*
  * least upper bound
  * 최소 상계
  * An upper bound below every upper bound; written ⨆\_n r\_n.
  * Session 8 · [§8.4](chapter-08/index.html#ch08-s4)
*
  * meaning of a command
  * 명령의 의미
  * The state transformer f\_c given by Definition 8.4 (loops added in Session 9).
  * Session 8 · [§8.2](chapter-08/index.html#ch08-s2)
*
  * outcome
  * 결과
  * An element of Σ⊥ = Σ ∪ \{⊥\}: a store or bottom.
  * Session 8 · [§8.1](chapter-08/index.html#ch08-s1)
*
  * state transformer
  * 상태 변환기
  * A total function from stores to outcomes.
  * Session 8 · [§8.1](chapter-08/index.html#ch08-s1)
*
  * strict extension
  * 엄격 확장
  * For a state transformer g, the function g† on outcomes with g†(⊥) = ⊥ and g†(t) = g(t) for stores t.
  * Session 8 · [§8.2](chapter-08/index.html#ch08-s2)
*
  * upper bound
  * 상계
  * An element above every member of the sequence.
  * Session 8 · [§8.4](chapter-08/index.html#ch08-s4)
*
  * approximation (of a loop)
  * 근사
  * The transformer `w_n`, obtained by applying `F` n times to the transformer that is ⊥ everywhere. `n` is its stage.
  * Session 9 · [§9.1](chapter-09/index.html#ch09-s1)
*
  * continuous operator
  * 연속 연산자
  * A monotone operator on transformers that preserves least upper bounds of increasing sequences.
  * Session 9 · [§9.3](chapter-09/index.html#ch09-s3)
*
  * fixed point
  * 고정점
  * A transformer `g` with `F(g) = g`.
  * Session 9 · [§9.3](chapter-09/index.html#ch09-s3)
*
  * least fixed point
  * 최소 고정점
  * A fixed point that lies below every fixed point in the pointwise order.
  * Session 9 · [§9.3](chapter-09/index.html#ch09-s3)
*
  * stage
  * 단계
  * The index of a loop approximation in the unfolding sequence.
  * Session 9 · [§9.1](chapter-09/index.html#ch09-s1)
*
  * unfolding operator
  * 펼침 연산자
  * The operator `F` on transformers. It tests the guard, runs the body, and passes the body's result to a proposed loop meaning.
  * Session 9 · [§9.1](chapter-09/index.html#ch09-s1)
*
  * nested induction
  * 중첩 귀납법
  * An induction carried out inside one case of another induction, with the outer induction hypotheses still available.
  * Session 10 · [§10.3](chapter-10/index.html#ch10-s3)
*
  * relational composition
  * 관계 합성
  * The set of pairs (s,t) such that some intermediate store m has (s,m) in the first relation and (m,t) in the second.
  * Session 10 · [§10.1](chapter-10/index.html#ch10-s1)
*
  * assertion
  * 단언
  * A statement about a store that is true or false at each store
  * Session 11 · [§11.2](chapter-11/index.html#ch11-s2)
*
  * assertion written with expressions
  * 식으로 쓴 단언
  * An assertion φ(a\_1,…,a\_j) that reads the store only through the values of expressions
  * Session 11 · [§11.2](chapter-11/index.html#ch11-s2)
*
  * expression substitution lemma
  * 식 치환 보조정리
  * eval(a\[e/x\], s) = eval(a, s\[x ↦ eval(e,s)\])
  * Session 11 · [§11.1](chapter-11/index.html#ch11-s1)
*
  * Hoare triple
  * Hoare 삼중항
  * \{P\} c \{Q\}: precondition, command, postcondition
  * Session 11 · [§11.2](chapter-11/index.html#ch11-s2)
*
  * partial correctness
  * 부분 정확성
  * The validity notion of Def 11.4; it constrains only terminating executions
  * Session 11 · [§11.2](chapter-11/index.html#ch11-s2)
*
  * postcondition
  * 사후 조건
  * The assertion promised of every final store in a triple
  * Session 11 · [§11.2](chapter-11/index.html#ch11-s2)
*
  * precondition
  * 사전 조건
  * The assertion required of the initial store in a triple
  * Session 11 · [§11.2](chapter-11/index.html#ch11-s2)
*
  * substituted assertion
  * 치환한 단언
  * Q\[e/x\]: holds at s when Q holds at s\[x ↦ eval(e,s)\]
  * Session 11 · [§11.3](chapter-11/index.html#ch11-s3)
*
  * substitution
  * 치환
  * a\[e/x\]: the expression a with each occurrence of x replaced once by e
  * Session 11 · [§11.1](chapter-11/index.html#ch11-s1)
*
  * valid triple
  * 타당한 삼중항
  * Every terminating execution from a store satisfying P ends in a store satisfying Q
  * Session 11 · [§11.2](chapter-11/index.html#ch11-s2)
*
  * consequence rule
  * 귀결 규칙
  * The rule strengthening a precondition and weakening a postcondition
  * Session 12 · [§12.2](chapter-12/index.html#ch12-s2)
*
  * derivable triple
  * 유도 가능한 삼중항
  * A triple with a finite derivation in the Hoare proof system, written ⊢\_H \{P\} c \{Q\}.
  * Session 12 · [§12.2](chapter-12/index.html#ch12-s2)
*
  * guard assertion
  * 가드 단언
  * The assertion T\_b (resp. F\_b) holding at a store exactly when the guard's value there is true (resp. false).
  * Session 12 · [§12.1](chapter-12/index.html#ch12-s1)
*
  * Hoare proof system
  * Hoare 증명 체계
  * The six rules (skip, assignment, sequence, conditional, while, consequence) that derive triples without mentioning executions.
  * Session 12 · [§12.2](chapter-12/index.html#ch12-s2)
*
  * loop invariant
  * 루프 불변식
  * An assertion P with ⊨ \{P ∧ T\_b\} c \{P\} for the loop `while b do c`.
  * Session 12 · [§12.1](chapter-12/index.html#ch12-s1)
*
  * soundness
  * 건전성
  * Every derivable triple is valid.
  * Session 12 · [§12.3](chapter-12/index.html#ch12-s3)
*
  * strong induction
  * 강한 귀납법
  * Prove L(j) for every natural number j by proving L(j) from L(j′) for all j′ < j
  * Session 13 · [§13.3](chapter-13/index.html#ch13-s3)
*
  * total correctness (valid for total correctness)
  * 전체 정확성
  * ⊨\_tot \{P\} c \{Q\}: from every store satisfying P some execution of c terminates in a store satisfying Q
  * Session 13 · [§13.1](chapter-13/index.html#ch13-s1)
*
  * total while rule
  * 전체 정확성 반복문 규칙
  * From ⊢\_tot \{P ∧ T\_b ∧ (μ=j)\} c \{P ∧ (μ<j)\} for every j ∈ ℕ, conclude ⊢\_tot \{P\} while b do c \{P ∧ F\_b\}
  * Session 13 · [§13.2](chapter-13/index.html#ch13-s2)
*
  * total-correctness proof system
  * 전체 정확성 증명 체계
  * The rules of Def 12.2 with the while rule replaced by the total while rule; derivability is written ⊢\_tot
  * Session 13 · [§13.2](chapter-13/index.html#ch13-s2)
*
  * variant
  * 변량
  * A function μ from stores to natural numbers that every execution of a loop body, from a store where the guard is true, must strictly lower
  * Session 13 · [§13.2](chapter-13/index.html#ch13-s2)
*
  * well-founded relation (Further Reading only)
  * 정초 관계
  * A relation with no infinite descending chain; it supports induction from all smaller elements
  * Session 13 · [Further reading](chapter-13/index.html#ch13-s6)
*
  * branch distance
  * 상대 거리
  * The signed offset measured from the instruction after the branch.
  * Session 14 · [B.1](machine-card/index.html#machine-b1)
*
  * branch-free code
  * 분기 없는 코드
  * Code using only push, load, plus and opp.
  * Session 14 · [§14.1](chapter-14/index.html#ch14-s1)
*
  * bridge lemma
  * 다리 보조정리
  * Lemma 14.3: list execution of branch-free code is realized by machine transitions.
  * Session 14 · [§14.3](chapter-14/index.html#ch14-s3)
*
  * code
  * 코드
  * A finite list of instructions.
  * Session 14 · [B.2](machine-card/index.html#machine-b2)
*
  * code at a position
  * 위치에 놓인 코드
  * `at(C,pc,K)`: C splits as C1 ++ K ++ C2 with |C1| = pc.
  * Session 14 · [B.2](machine-card/index.html#machine-b2)
*
  * conditional branch
  * 조건 분기 명령
  * beq or ble.
  * Session 14 · [B.1](machine-card/index.html#machine-b1)
*
  * instruction
  * 기계 명령어
  * One of the nine machine operations of B.1.
  * Session 14 · [B.1](machine-card/index.html#machine-b1)
*
  * joining paths
  * 경로 잇기
  * Composing two finite paths that meet at a configuration.
  * Session 14 · [B.5](machine-card/index.html#machine-b5)
*
  * list execution
  * 목록 실행
  * `run_s(K)`: the partial function on stacks computed by branch-free code in store s.
  * Session 14 · [§14.1](chapter-14/index.html#ch14-s1)
*
  * machine configuration
  * 기계 구성
  * A program counter, a stack and a store.
  * Session 14 · [B.3](machine-card/index.html#machine-b3)
*
  * program counter
  * 프로그램 카운터
  * The position of the next instruction.
  * Session 14 · [B.3](machine-card/index.html#machine-b3)
*
  * stack
  * 스택
  * A finite list of integers with its top on the left.
  * Session 14 · [B.3](machine-card/index.html#machine-b3)
*
  * branch instruction
  * 분기 명령
  * `branch(d)`: moves the program counter from pc to pc+1+d, nothing else.
  * Session 15 · [§15.1](chapter-15/index.html#ch15-s1)
*
  * compilation with two distances
  * 거리를 인자로 받는 조건식 컴파일
  * `cbexp(b,d1,d0)`: code for b that ends d1 or d0 past its end.
  * Session 15 · [§15.1](chapter-15/index.html#ch15-s1)
*
  * contract of compiled Boolean expressions
  * 조건식 코드의 계약
  * From any position where K sits, reach pc+|K|+sel(B(b,s),d1,d0) with stack and store unchanged (Definition 15.1).
  * Session 15 · [§15.2](chapter-15/index.html#ch15-s2)
*
  * true exit / false exit
  * 참 출구 / 거짓 출구
  * pc+|K|+d1 and pc+|K|+d0 for a block K at pc.
  * Session 15 · [§15.2](chapter-15/index.html#ch15-s2)
*
  * backward branch
  * 뒤로 가는 분기
  * A branch instruction with a negative distance; ends every compiled loop.
  * Session 16 · [§16.1](chapter-16/index.html#ch16-s1)
*
  * contract of compiled commands
  * 명령 코드의 계약
  * For every s ⊢ c ⇓ t and every C, pc, S with at(C,pc,K): C ⊢ ⟨pc,S,s⟩ →\* ⟨pc+|K|,S,t⟩ (Definition 16.1).
  * Session 16 · [§16.2](chapter-16/index.html#ch16-s2)
*
  * layout of a compiled command
  * 명령 컴파일의 배치
  * Where each part of a command's code starts, relative to the position of the block; for a loop: test at pc, body at pc+|Kb|, backward branch at pc+|Kb|+|K1|, end at pc+|Kb|+|K1|+1.
  * Session 16 · [§16.1](chapter-16/index.html#ch16-s1)
*
  * terminates / diverges / goes wrong (machine)
  * 정상 종료 / 발산 / 오류로 멈춤
  * The three behaviours of a compiled program (B.9).
  * Session 16 · [B.9](machine-card/index.html#machine-b9)
*
  * test (of a conditional or loop)
  * 검사 코드
  * The code cbexp(b,0,|K1|+1) of the guard at the head of a compiled conditional or loop.
  * Session 16 · [§16.1](chapter-16/index.html#ch16-s1)
*
  * abstract evaluation
  * 추상 평가
  * eval♯(e, A) and B♯(b, A): the value when every operand is known, ⊤ otherwise.
  * Session 17 · [§17.2](chapter-17/index.html#ch17-s2)
*
  * abstract store
  * 추상 상태
  * A function from names to abstract values, ⊤ at all but finitely many names. Written by listing its entries, e.g. \{x ↦ 7\}; \{\} has no entries.
  * Session 17 · [§17.1](chapter-17/index.html#ch17-s1)
*
  * abstract transfer
  * 추상 전이
  * f♯\_c : Σ♯ → Σ♯, defined by recursion on c (Definition 17.6).
  * Session 17 · [§17.2](chapter-17/index.html#ch17-s2)
*
  * abstract value
  * 추상 값
  * An integer or ⊤, read "unknown".
  * Session 17 · [§17.1](chapter-17/index.html#ch17-s1)
*
  * analysis soundness
  * 분석 건전성
  * Theorem 17.8: the transfer result describes every final store of a run from a described store.
  * Session 17 · [§17.3](chapter-17/index.html#ch17-s3)
*
  * concretization
  * 구체화
  * γ(A), the set of stores s with s(x) = n for every entry x ↦ n of A.
  * Session 17 · [§17.1](chapter-17/index.html#ch17-s1)
*
  * describes (an abstract store describes a store)
  * 기술하다
  * A describes s when s ∈ γ(A).
  * Session 17 · [§17.1](chapter-17/index.html#ch17-s1)
*
  * entry (of an abstract store)
  * 항목
  * A pair x ↦ n with A(x) = n an integer.
  * Session 17 · [§17.1](chapter-17/index.html#ch17-s1)
*
  * join
  * 이음
  * Name by name: a ⊔ a' = a if a = a', else ⊤. The join of abstract stores keeps their common entries. It is their least upper bound.
  * Session 17 · [§17.1](chapter-17/index.html#ch17-s1)
*
  * precision order
  * 정밀도 순서
  * An abstract store is below another when it contains every entry of the other. Moving upward forgets information: a known integer lies below unknown, and the empty abstract store is greatest.
  * Session 17 · [§17.1](chapter-17/index.html#ch17-s1)
*
  * constant folding
  * 상수 접기
  * Computing an operation on literal operands at compile time.
  * Session 18 · [§18.1](chapter-18/index.html#ch18-s1)
*
  * constant propagation
  * 상수 전파
  * Replacing a variable read by the literal that the abstract store records for that variable.
  * Session 18 · [§18.1](chapter-18/index.html#ch18-s1)
*
  * program transformation
  * 프로그램 변환
  * A function that maps each program to another program.
  * Session 18 · [§18.1](chapter-18/index.html#ch18-s1)
*
  * simplifying constructor
  * 단순화 생성자
  * A function that builds an expression, guard or command from its parts and simplifies constant parts, keeping the value at every store.
  * Session 18 · [§18.1](chapter-18/index.html#ch18-s1)
*
  * bounded iteration
  * 제한 반복
  * `iter(F,D,n,X)`: apply `F` until `F(X) ⊆ X`, or return the fallback set when the fuel is exhausted.
  * Session 19 · [§19.2](chapter-19/index.html#ch19-s2)
*
  * dead variable
  * 죽은 변수
  * A name not in `live(c,L)`.
  * Session 19 · [§19.1](chapter-19/index.html#ch19-s1)
*
  * fallback set
  * 대체 집합
  * The set `D` returned when the fuel runs out.
  * Session 19 · [§19.2](chapter-19/index.html#ch19-s2)
*
  * fuel
  * 연료
  * The natural-number bound `n` of a bounded iteration.
  * Session 19 · [§19.2](chapter-19/index.html#ch19-s2)
*
  * live variable
  * 생존 변수
  * A name in `live(c,L)`. Its value before `c` may influence a name of `L` after `c`.
  * Session 19 · [§19.1](chapter-19/index.html#ch19-s1)
*
  * liveness transfer
  * 생존 전달 함수
  * `live(c,L)`: the names needed before `c` when `L` is observed after `c`.
  * Session 19 · [§19.1](chapter-19/index.html#ch19-s1)
*
  * loop head
  * 루프 머리
  * The point just before each test of a loop's guard.
  * Session 19 · [§19.2](chapter-19/index.html#ch19-s2)
*
  * observed set
  * 관찰 집합
  * The set `L` of names read after a command.
  * Session 19 · [§19.1](chapter-19/index.html#ch19-s1)
*
  * post-fixed point
  * 후고정점
  * A set `H` with `F(H) ⊆ H`. CS calls it a "pre-fixpoint".
  * Session 19 · [§19.2](chapter-19/index.html#ch19-s2)
*
  * read names
  * 읽는 변수
  * `RV(c)`: the names in the expressions and guards of a command. Assignment targets are excluded.
  * Session 19 · [§19.1](chapter-19/index.html#ch19-s1)
*
  * agreement on a set
  * 집합 위의 일치 (X 위에서 일치한다)
  * `s(y) = u(y)` for every `y ∈ X`; written `s|_X = u|_X`
  * Session 20 · [§20.1](chapter-20/index.html#ch20-s1)
*
  * dead assignment
  * 죽은 대입
  * In `elim(x := e, L)`, the assignment when `x ∉ L`
  * Session 20 · [§20.1](chapter-20/index.html#ch20-s1)
*
  * dead-assignment elimination
  * 죽은 대입 제거
  * The transformation `elim(c, L)` that replaces dead assignments by skip (Definition 20.1)
  * Session 20 · [§20.1](chapter-20/index.html#ch20-s1)
:::

# Part 2 · Functions and Types
%%%
tag := "glossary-part-2"
number := false
%%%

:::table +header
*
  * English
  * Korean
  * Meaning
  * First use
*
  * abstraction
  * 람다 추상
  * `λx.t`, a function with parameter `x` and body `t`
  * Session 22 · [C.1](lambda-card/index.html#lambda-c1)
*
  * alpha-equivalence
  * 알파 동치
  * Relation between terms obtained by renaming parameters together with the occurrences they bind
  * Session 22 · [§22.1](chapter-22/index.html#ch22-s1)
*
  * application
  * 적용
  * `t1 t2`, a function term applied to an argument
  * Session 22 · [C.1](lambda-card/index.html#lambda-c1)
*
  * body
  * 본체
  * The term within the scope of the parameter of an abstraction.
  * Session 22 · [C.1](lambda-card/index.html#lambda-c1)
*
  * bound occurrence
  * 묶인 출현
  * An occurrence inside the body of an abstraction with the same parameter
  * Session 22 · [C.1](lambda-card/index.html#lambda-c1)
*
  * capture
  * 포획
  * A free occurrence in the inserted term becomes bound by an abstraction of the target term
  * Session 22 · [§22.2](chapter-22/index.html#ch22-s2)
*
  * capture-avoiding substitution
  * 포획 회피 치환
  * `[x ↦ s]t`: replace the free occurrences of `x` by `s`, renaming any parameter that would capture a free variable of the inserted term.
  * Session 22 · [§22.2](chapter-22/index.html#ch22-s2)
*
  * closed term
  * 닫힌 항
  * A term with no free variables
  * Session 22 · [C.1](lambda-card/index.html#lambda-c1)
*
  * fresh variable
  * 새 변수
  * A variable that occurs nowhere in the given terms and differs from the given variables
  * Session 22 · [§22.1](chapter-22/index.html#ch22-s1)
*
  * parameter
  * 매개변수
  * The variable bound by an abstraction.
  * Session 22 · [C.1](lambda-card/index.html#lambda-c1)
*
  * size of a term
  * 항의 크기
  * The number of nodes of the syntax tree
  * Session 22 · [§22.1](chapter-22/index.html#ch22-s1)
*
  * term
  * 항
  * A variable, an abstraction or an application in the untyped lambda calculus.
  * Session 22 · [C.1](lambda-card/index.html#lambda-c1)
*
  * call by name
  * 이름 호출
  * The strategy that substitutes the operand unevaluated
  * Session 23 · [C.1](lambda-card/index.html#lambda-c1)
*
  * call by value
  * 값 호출
  * The strategy that contracts a redex only when its operand is a value
  * Session 23 · [C.1](lambda-card/index.html#lambda-c1)
*
  * computation rule / congruence rule
  * 계산 규칙 / 합동 규칙
  * An evaluation rule without / with an evaluation premise
  * Session 23 · [C.1](lambda-card/index.html#lambda-c1)
*
  * contract (a redex)
  * (레덱스를) 축약하다
  * Replace `(λx.t₁₂) t₂` by `[x ↦ t₂]t₁₂`
  * Session 23 · [§23.1](chapter-23/index.html#ch23-s1)
*
  * determinacy of one-step evaluation
  * 한 걸음 평가의 결정성
  * Each term has at most one next term under the given strategy
  * Session 23 · [§23.2](chapter-23/index.html#ch23-s2)
*
  * diverge / divergence
  * 발산하다 / 발산
  * No normal form is reachable from the term under the given strategy
  * Session 23 · [§23.3](chapter-23/index.html#ch23-s3)
*
  * evaluation strategy
  * 평가 전략
  * A set of one-step rules that decides which redex is contracted next
  * Session 23 · [§23.1](chapter-23/index.html#ch23-s1)
*
  * normal form
  * 정규형
  * A term with no step
  * Session 23 · [C.1](lambda-card/index.html#lambda-c1)
*
  * operator / operand
  * 연산자 / 피연산자
  * In an application `t₁ t₂`, the term `t₁` / the term `t₂`
  * Session 23 · [§23.1](chapter-23/index.html#ch23-s1)
*
  * redex
  * 레덱스
  * A term `(λx.t12) t2`
  * Session 23 · [C.1](lambda-card/index.html#lambda-c1)
*
  * value
  * 값
  * A term in one of the value forms of the card
  * Session 23 · [C.1](lambda-card/index.html#lambda-c1)
*
  * canonical form
  * 정준형
  * A shape that a value of a given type can have.
  * Session 24 · [§24.2](chapter-24/index.html#ch24-s2)
*
  * evaluation derivation
  * 평가 유도
  * A derivation of one step `t → t'` by the evaluation rules.
  * Session 24 · [§24.1](chapter-24/index.html#ch24-s1)
*
  * inversion of typing
  * 타입 판단의 역전
  * Reading the type and the premise typings off the unique typing rule for a term's form.
  * Session 24 · [§24.2](chapter-24/index.html#ch24-s2)
*
  * numeric value
  * 수 값
  * `0` or `succ nv` for a numeric value `nv`.
  * Session 24 · [§24.1](chapter-24/index.html#ch24-s1)
*
  * preservation
  * 보존
  * A step from a term of type `T` gives a term of type `T`.
  * Session 24 · [§24.3](chapter-24/index.html#ch24-s3)
*
  * progress (of a typed term)
  * 진행
  * A well-typed closed term is a value or takes a step.
  * Session 24 · [§24.3](chapter-24/index.html#ch24-s3)
*
  * safety table
  * 안전성 표
  * The table in C.8 with one row per construct group: canonical forms, progress cases, preservation cases.
  * Session 24 · [§24.4](chapter-24/index.html#ch24-s4)
*
  * stuck term
  * 막힌 항
  * A closed normal form that is not a value.
  * Session 24 · [§24.1](chapter-24/index.html#ch24-s1)
*
  * type safety
  * 타입 안전성
  * A well-typed term never reaches a stuck term.
  * Session 24 · [§24.4](chapter-24/index.html#ch24-s4)
*
  * typing judgment
  * 타입 판단
  * `Γ | Σ ⊢ t : T`, defined by the typing rules
  * Session 24 · [C.2](lambda-card/index.html#lambda-c2)
*
  * well-typed term
  * 타입이 있는 항
  * A term `t` with `⊢ t : T` for some type `T`.
  * Session 24 · [§24.2](chapter-24/index.html#ch24-s2)
*
  * permutation (of a context)
  * 순열 (문맥의)
  * A context with the same bindings in another order
  * Session 25 · [§25.2](chapter-25/index.html#ch25-s2)
*
  * type-preserving term substitution lemma
  * 타입 보존 항 치환 보조정리
  * Theorem 25.5: `Γ,x:S ⊢ t:T` and `Γ ⊢ s:S` give `Γ ⊢ [x↦s]t:T`
  * Session 25 · [§25.3](chapter-25/index.html#ch25-s3)
*
  * typing context
  * 타입 문맥
  * A finite sequence of bindings `x:T` with distinct variables
  * Session 25 · [§25.1](chapter-25/index.html#ch25-s1)
*
  * weakening
  * 약화
  * Adding a binding for a new variable keeps a typing judgment
  * Session 25 · [§25.2](chapter-25/index.html#ch25-s2)
*
  * codomain (of a function type)
  * 공역
  * `T_2` in `T_1 → T_2`
  * Session 26 · [§26.1](chapter-26/index.html#ch26-s1)
*
  * domain (of a function type)
  * 정의역
  * `T_1` in `T_1 → T_2`
  * Session 26 · [§26.1](chapter-26/index.html#ch26-s1)
*
  * case term / branch
  * case 항 / 가지
  * `case t0 of inl x1 ⇒ t1 | inr x2 ⇒ t2`; `t1`, `t2` are its branches
  * Session 27 · [§27.1](chapter-27/index.html#ch27-s1)
*
  * Curry–Howard correspondence
  * 커리–하워드 대응
  * Types read as propositions, derivations as proofs, terms as records of proofs
  * Session 27 · [§27.5](chapter-27/index.html#ch27-s5)
*
  * injection
  * 주입
  * `inl t as T`, `inr t as T`
  * Session 27 · [§27.1](chapter-27/index.html#ch27-s1)
*
  * left / right summand
  * 왼쪽 / 오른쪽 합항
  * `T1` / `T2` in `T1 + T2`
  * Session 27 · [§27.1](chapter-27/index.html#ch27-s1)
*
  * pair / component
  * 쌍 / 성분
  * `{t1,t2}`; `t1` and `t2` are its first and second components
  * Session 27 · [§27.1](chapter-27/index.html#ch27-s1)
*
  * product type
  * 곱 타입
  * `T1 × T2`, the type of pairs
  * Session 27 · [§27.1](chapter-27/index.html#ch27-s1)
*
  * projection
  * 사영
  * `t.1`, `t.2`
  * Session 27 · [§27.1](chapter-27/index.html#ch27-s1)
*
  * sum type
  * 합 타입
  * `T1 + T2`, the type of tagged terms of type `T1` or `T2`
  * Session 27 · [§27.1](chapter-27/index.html#ch27-s1)
*
  * checker
  * 타입 검사기
  * The function `check` of Definition 28.1 on annotated terms
  * Session 28 · [§28.1](chapter-28/index.html#ch28-s1)
*
  * constraint set
  * 제약 집합
  * A finite set of equations between types
  * Session 28 · [C.5](lambda-card/index.html#lambda-c5)
*
  * degree (of a constraint set)
  * 차수
  * The pair (number of type variables, total size), compared lexicographically
  * Session 28 · [§28.3](chapter-28/index.html#ch28-s3)
*
  * more general
  * 더 일반적인
  * `σ ⊑ σ'`: `σ' = γ ∘ σ` for some `γ`
  * Session 28 · [C.5](lambda-card/index.html#lambda-c5)
*
  * occurs check
  * 출현 검사
  * The test `X ∉ FV(T)` before binding `X` to `T` in `unify`
  * Session 28 · [C.5](lambda-card/index.html#lambda-c5)
*
  * principal type
  * 주 타입
  * The type of a principal solution; every type of the term is obtained from it by a substitution
  * Session 28 · [§28.4](chapter-28/index.html#ch28-s4)
*
  * principal unifier
  * 주 단일화자
  * A unifier more general (`⊑`) than every unifier of the same set
  * Session 28 · [C.5](lambda-card/index.html#lambda-c5)
*
  * size (of a type)
  * 크기
  * Number of nodes of a type
  * Session 28 · [§28.3](chapter-28/index.html#ch28-s3)
*
  * type substitution
  * 타입 치환
  * A finite map from type variables to types, applied to all variables at once
  * Session 28 · [C.5](lambda-card/index.html#lambda-c5)
*
  * type variable
  * 타입 변수
  * `X, Y, Z`: in C.5 an unknown type to be determined by inference
  * Session 28 · [C.5](lambda-card/index.html#lambda-c5)
*
  * unification
  * 단일화
  * Computing a principal unifier of a constraint set, or failing when there is none
  * Session 28 · [§28.2](chapter-28/index.html#ch28-s2)
*
  * unifier
  * 단일화자
  * A substitution that makes both sides of every equation of a constraint set identical
  * Session 28 · [C.5](lambda-card/index.html#lambda-c5)
*
  * generalization
  * 일반화
  * Quantifying type variables of the right-hand side's type at a let
  * Session 29 · [§29.2](chapter-29/index.html#ch29-s2)
*
  * generalization condition
  * 일반화 조건
  * No quantified variable is free in Γ
  * Session 29 · [§29.2](chapter-29/index.html#ch29-s2)
*
  * instance (of a scheme)
  * 인스턴스
  * `[X1↦S1,…,Xn↦Sn]T` for a scheme `∀X1…Xn.T`
  * Session 29 · [§29.2](chapter-29/index.html#ch29-s2)
*
  * let-polymorphism
  * let 다형성
  * Using a let-bound variable at several instances of its type scheme
  * Session 29 · [§29.2](chapter-29/index.html#ch29-s2)
*
  * quantified variable
  * 양화 변수
  * One of the `Xi` of a scheme `∀X1…Xn.T`
  * Session 29 · [§29.2](chapter-29/index.html#ch29-s2)
*
  * type scheme
  * 타입 스킴
  * `∀X1…Xn.T`, occurring only in contexts
  * Session 29 · [§29.2](chapter-29/index.html#ch29-s2)
*
  * alias
  * 별칭
  * Two variables that name the same location
  * Session 30 · [§30.1](chapter-30/index.html#ch30-s1)
*
  * allocation
  * 할당
  * Creating a new cell at a fresh location (E-RefV)
  * Session 30 · [§30.1](chapter-30/index.html#ch30-s1)
*
  * cell
  * 셀
  * The entry of a store at one location
  * Session 30 · [§30.1](chapter-30/index.html#ch30-s1)
*
  * location
  * 위치
  * A run-time name of a cell; a value that no program contains
  * Session 30 · [§30.1](chapter-30/index.html#ch30-s1)
*
  * run-time store
  * 저장소
  * A finite map μ from locations to values.
  * Session 30 · [§30.1](chapter-30/index.html#ch30-s1)
*
  * run-time store update lemma
  * 저장소 갱신 보조정리
  * Lemma 30.3: writing a value of the cell's type keeps the store well typed
  * Session 30 · [§30.2](chapter-30/index.html#ch30-s2)
*
  * store typing
  * 저장소 타입
  * A finite map Σ from locations to the types of their contents
  * Session 30 · [§30.1](chapter-30/index.html#ch30-s1)
*
  * store weakening
  * 저장소 약화
  * Lemma 30.2: a typing survives extension of the store typing
  * Session 30 · [§30.2](chapter-30/index.html#ch30-s2)
*
  * value restriction
  * 값 제한
  * Generalize at let only when the right-hand side is a value
  * Session 30 · [§30.5](chapter-30/index.html#ch30-s5)
*
  * well-typed store
  * 타입이 맞는 저장소
  * `Γ | Σ ⊢ μ`: equal domains, and each stored value has its recorded type
  * Session 30 · [§30.1](chapter-30/index.html#ch30-s1)
*
  * abstract type
  * 추상 타입
  * The type variable `X` inside the body of an unpacking
  * Session 31 · [§31.2](chapter-31/index.html#ch31-s2)
*
  * client (of a package)
  * 클라이언트
  * A term that unpacks the package
  * Session 31 · [§31.2](chapter-31/index.html#ch31-s2)
*
  * escape condition
  * 탈출 조건
  * The side condition `X ∉ FV(T2)` of T-Unpack
  * Session 31 · [§31.2](chapter-31/index.html#ch31-s2)
*
  * existential type
  * 존재 타입
  * `{∃X,T}`, the type of a package
  * Session 31 · [§31.2](chapter-31/index.html#ch31-s2)
*
  * package
  * 패키지
  * `{*U,t} as {∃X,T}`, a representation type with an implementation
  * Session 31 · [§31.2](chapter-31/index.html#ch31-s2)
*
  * representation type
  * 표현 타입
  * The type `U` hidden in a package
  * Session 31 · [§31.2](chapter-31/index.html#ch31-s2)
*
  * type abstraction
  * 타입 추상화
  * `λX.t`, binds a type variable in the types written in `t`
  * Session 31 · [§31.1](chapter-31/index.html#ch31-s1)
*
  * type application
  * 타입 적용
  * `t [T]`, supplies a type argument
  * Session 31 · [§31.1](chapter-31/index.html#ch31-s1)
*
  * type substitution lemma
  * 타입 치환 보조정리
  * Substituting a well-formed type for a type variable throughout a typing derivation preserves the judgment under the substituted context.
  * Session 31 · [§31.3](chapter-31/index.html#ch31-s3)
*
  * universal type
  * 전칭 타입
  * `∀X.T`, the type of a type abstraction
  * Session 31 · [§31.1](chapter-31/index.html#ch31-s1)
*
  * unpacking
  * 패키지 열기
  * `let {X,x} = t1 in t2`
  * Session 31 · [§31.2](chapter-31/index.html#ch31-s2)
*
  * well-formed type
  * 정형 타입
  * A type whose free type variables are bound in Γ
  * Session 31 · [C.7](lambda-card/index.html#lambda-c7)
*
  * term–store configuration
  * 구성
  * A pair `t | μ` of a term and a store; Part 2 reading of the IMP configuration of A.6
  * Session 32 · [§32.3](chapter-32/index.html#ch32-s3)
:::

# Part 3 · Logical Relations and PCF
%%%
tag := "glossary-part-3"
number := false
%%%

:::table +header
*
  * English
  * Korean
  * Meaning
  * First use
*
  * client body / counter context
  * 클라이언트 본문 / 카운터 문맥
  * A term typed in `Γ_ctr = start:X, tick:X→X, get:X→Nat`.
  * Session 33 · [§33.2](chapter-33/index.html#ch33-s2)
*
  * client fragment
  * 클라이언트 조각
  * Types `X | Nat | T→T`, terms variable/abstraction/application.
  * Session 33 · [§33.2](chapter-33/index.html#ch33-s2)
*
  * client tree
  * 클라이언트 트리
  * A first-order client built from done, adv and test.
  * Session 33 · [§33.1](chapter-33/index.html#ch33-s1)
*
  * counter observation
  * 관찰값
  * `obs(k,d)`, the number a client tree returns from an element.
  * Session 33 · [§33.1](chapter-33/index.html#ch33-s1)
*
  * environment
  * 환경
  * A function giving each variable of a context an element of the meaning of its type.
  * Session 33 · [§33.2](chapter-33/index.html#ch33-s2)
*
  * fundamental theorem (of a logical relation)
  * 기본 정리
  * Every well-typed term is related to itself in related environments.
  * Session 33 · [§33.3](chapter-33/index.html#ch33-s3)
*
  * logical relation
  * 논리 관계
  * The relations `R_T` defined by recursion on types: R at X, equality at Nat, related arguments to related results at arrows.
  * Session 33 · [§33.3](chapter-33/index.html#ch33-s3)
*
  * meaning (of a type, of a term)
  * 의미
  * `⟦T⟧_A`, the set of a type; `⟦t⟧_A ρ`, the element a typed term describes in an environment.
  * Session 33 · [§33.2](chapter-33/index.html#ch33-s2)
*
  * related environments
  * 관계된 환경
  * `ρ(x) R_T ρ'(x)` for every binding `x:T` of the context.
  * Session 33 · [§33.3](chapter-33/index.html#ch33-s3)
*
  * representation independence
  * 표현 독립성
  * Every client gives the same observable result with either of two implementations of an abstract type.
  * Session 33 · [§33.4](chapter-33/index.html#ch33-s4)
*
  * admissible property
  * 허용 성질
  * A chain-closed property that holds at ⊥.
  * Session 34 · [§34.3](chapter-34/index.html#ch34-s3)
*
  * chain-closed property
  * 사슬 닫힌 성질
  * A property that holds at the least upper bound of every increasing sequence at whose elements it holds.
  * Session 34 · [§34.3](chapter-34/index.html#ch34-s3)
*
  * continuous function
  * 연속 함수
  * A monotone function that preserves least upper bounds of increasing sequences.
  * Session 34 · [§34.1](chapter-34/index.html#ch34-s1)
*
  * domain
  * 영역
  * A partial order with a least element in which every increasing sequence has a least upper bound.
  * Session 34 · [§34.1](chapter-34/index.html#ch34-s1)
*
  * flat domain
  * 평탄 영역
  * A set with ⊥ added below every element and no other strict comparisons. Σ\_⊥ (Session 8) and ℕ\_⊥ are instances.
  * Session 34 · [§34.1](chapter-34/index.html#ch34-s1)
*
  * function domain
  * 함수 영역
  * The continuous functions between two domains, ordered pointwise.
  * Session 34 · [§34.2](chapter-34/index.html#ch34-s2)
*
  * monotone function
  * 단조 함수
  * A function with d ⊑ d′ ⇒ f(d) ⊑ f(d′).
  * Session 34 · [§34.1](chapter-34/index.html#ch34-s1)
*
  * Scott induction (fixed-point induction)
  * Scott 귀납 (고정점 귀납)
  * An admissible property preserved by a continuous f holds at fix(f).
  * Session 34 · [§34.3](chapter-34/index.html#ch34-s3)
*
  * strict function
  * 엄격 함수
  * A function sending ⊥ to ⊥. The word comes from Session 8's strict extension.
  * Session 34 · [§34.1](chapter-34/index.html#ch34-s1)
*
  * numeral
  * 수 항
  * The numeric value `\overline{n}`: `succ` applied `n` times to `0`.
  * Session 35 · [§35.1](chapter-35/index.html#ch35-s1)
*
  * PCF
  * PCF
  * The typed language of Booleans, natural numbers and functions with call-by-name evaluation and the recursion operator `fix`.
  * Session 35 · [§35.1](chapter-35/index.html#ch35-s1)
*
  * recursion operator
  * 재귀 연산자
  * The term former `fix`. `fix t` evaluates by evaluating `t (fix t)` and means the least fixed point of the meaning of `t`.
  * Session 35 · [§35.1](chapter-35/index.html#ch35-s1)
*
  * soundness of evaluation
  * 평가의 건전성
  * If `t ⇓ v` then `⟦t⟧ = ⟦v⟧` (Theorem 35.8).
  * Session 35 · [§35.4](chapter-35/index.html#ch35-s4)
*
  * unfolding equation
  * 펼침 등식
  * The meaning of a recursive term equals the meaning of its unfolding.
  * Session 35 · [§35.4](chapter-35/index.html#ch35-s4)
*
  * closure under evaluation
  * 평가에 대한 닫힘
  * If every value of `t` is a value of `t'`, every element approximating `t` approximates `t'`.
  * Session 36 · [§36.3](chapter-36/index.html#ch36-s3)
*
  * computational adequacy
  * 계산적 적절성
  * If a closed term of ground type means a number or truth value, it evaluates to the corresponding value.
  * Session 36 · [§36.1](chapter-36/index.html#ch36-s1)
*
  * formal approximation relation
  * 형식 근사 관계
  * The relation `d ◁_T t` between elements of `[[T]]` and closed terms of type `T`, defined by induction on `T`.
  * Session 36 · [§36.2](chapter-36/index.html#ch36-s2)
*
  * ground type
  * 기저 타입
  * The type Nat or Bool.
  * Session 36 · [§36.1](chapter-36/index.html#ch36-s1)
*
  * related pair
  * 관계된 쌍
  * A pair `(d, u)` with `d ◁_T u`.
  * Session 36 · [§36.2](chapter-36/index.html#ch36-s2)
*
  * soundness (of the denotation)
  * 건전성
  * If a closed term evaluates to a value, the two have the same meaning.
  * Session 36 · [§36.1](chapter-36/index.html#ch36-s1)
*
  * closing substitution
  * 닫는 치환
  * One closed term of the declared type for each variable of a context.
  * Session 37 · [§37.1](chapter-37/index.html#ch37-s1)
*
  * fundamental property
  * 기본 성질
  * The meaning of a well-typed term approximates each closed instance under a related environment and substitution.
  * Session 37 · [§37.1](chapter-37/index.html#ch37-s1)
*
  * related environment and substitution
  * 관계된 환경과 치환
  * `ρ(x_i) ◁_{T_i} u_i` for every variable `x_i` of the context.
  * Session 37 · [§37.1](chapter-37/index.html#ch37-s1)
*
  * full abstraction
  * 완전 추상화
  * The property that two closed terms which no closed program of ground type can tell apart have the same meaning. A semantics with it is \*fully abstract\*. PCF with the semantics of Session 35 does not have it.
  * Session 38 · [§38.3](chapter-38/index.html#ch38-s3)
*
  * parallel or
  * 병렬 논리합
  * A Boolean function that returns true when either argument is true, even if the other is undefined.
  * Session 38 · [§38.3](chapter-38/index.html#ch38-s3)
:::
