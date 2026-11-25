import PLBook.Ch01
import PLBook.Ch02
import PLBook.Ch03
import PLBook.Ch04
import PLBook.Ch05
import PLBook.Ch06
import PLBook.Ch07
import PLBook.Ch08
import PLBook.Ch09
import PLBook.Ch10
import PLBook.Ch11
import PLBook.Ch12
import PLBook.Ch13
import PLBook.Ch14
import PLBook.Ch15
import PLBook.Ch16
import PLBook.Ch17
import PLBook.Ch18
import PLBook.Ch19
import PLBook.Ch20
import PLBook.Ch21
import PLBook.Ch22
import PLBook.Ch23
import PLBook.Ch24
import PLBook.Ch25
import PLBook.Ch26
import PLBook.Ch27
import PLBook.Ch28
import PLBook.Ch29
import PLBook.Ch30
import PLBook.Ch31
import PLBook.Ch32
import PLBook.Ch33
import PLBook.Ch34
import PLBook.Ch35
import PLBook.Ch36
import PLBook.Ch37
import PLBook.Ch38
import PLBook.LanguageCard
import PLBook.MachineCard
import PLBook.LambdaCard
import PLBook.Glossary

open Verso.Genre Manual

#doc (Manual) "Programming Languages" =>
%%%
authors := ["HyperAccel PL Study Group"]
shortTitle := "Programming Languages"
tag := "pl-study"
%%%

To give a semantics to a programming language is to say precisely what its programs mean. Once that is done, claims about programs become mathematical statements that can be proved: that two programs behave alike, that a compiler preserves the behavior of the programs it translates, that a program accepted by a type checker never gets stuck. This book develops the definitions and proof techniques that make such statements precise, and it proves them for small but complete languages.

One theme runs through the book. A program can be described in several ways: by the steps of its execution, by the function it computes, by the code it is compiled to, by the type it is assigned. A theorem of semantics states the conditions under which two such descriptions agree on what can be observed. Part 1 follows this theme for IMP, a small imperative language, from rules of execution through denotations and Hoare logic to the correctness of a compiler and of two program optimizations. Part 2 turns to functions and types and proves type safety as the language grows from numbers to references and type abstraction. Part 3 uses logical relations to show when two implementations of an interface cannot be told apart, and when the mathematical meaning of a program determines the result of running it.

The book assumes experience with programming and none with formal proof. Induction is introduced in the first chapter, and nearly every later proof is an induction of the same kind.

*How to read this book.* The book was written for a seminar of thirty-eight one-hour sessions, and each chapter is one session. A chapter opens with a short motivation. A summary headed “In this session” then states its main theorem, the definitions it relies on, and the one case of the proof that is worked in full. The numbered sections that follow are the text of the session. After them come exercises, a plan for the hour, solutions with further reading, and notes that give the source of each result and say whether it has been checked in Lean. Chapters within a part should be read in order. Part 1 is complete by itself. Part 2 can be read after Sessions 1–3, which supply its rules, derivations and induction. Part 3 builds on the fixed points of Sessions 8–9 and on the typed languages of Part 2. Three reference cards collect the definitions and rules: the [IMP language card](imp-card/index.html), the [stack machine card](machine-card/index.html) and the [lambda language card](lambda-card/index.html). The [glossary](glossary/index.html) gives each term with its Korean equivalent.

{include 1 PLBook.Ch01}

{include 1 PLBook.Ch02}

{include 1 PLBook.Ch03}

{include 1 PLBook.Ch04}

{include 1 PLBook.Ch05}

{include 1 PLBook.Ch06}

{include 1 PLBook.Ch07}

{include 1 PLBook.Ch08}

{include 1 PLBook.Ch09}

{include 1 PLBook.Ch10}

{include 1 PLBook.Ch11}

{include 1 PLBook.Ch12}

{include 1 PLBook.Ch13}

{include 1 PLBook.Ch14}

{include 1 PLBook.Ch15}

{include 1 PLBook.Ch16}

{include 1 PLBook.Ch17}

{include 1 PLBook.Ch18}

{include 1 PLBook.Ch19}

{include 1 PLBook.Ch20}

{include 1 PLBook.Ch21}

{include 1 PLBook.Ch22}

{include 1 PLBook.Ch23}

{include 1 PLBook.Ch24}

{include 1 PLBook.Ch25}

{include 1 PLBook.Ch26}

{include 1 PLBook.Ch27}

{include 1 PLBook.Ch28}

{include 1 PLBook.Ch29}

{include 1 PLBook.Ch30}

{include 1 PLBook.Ch31}

{include 1 PLBook.Ch32}

{include 1 PLBook.Ch33}

{include 1 PLBook.Ch34}

{include 1 PLBook.Ch35}

{include 1 PLBook.Ch36}

{include 1 PLBook.Ch37}

{include 1 PLBook.Ch38}

{include 1 PLBook.LanguageCard}

{include 1 PLBook.MachineCard}

{include 1 PLBook.LambdaCard}

{include 1 PLBook.Glossary}
