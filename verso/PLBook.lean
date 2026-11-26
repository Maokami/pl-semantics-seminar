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

Suppose a compiler removes an assignment whose value is overwritten before it is read. Why is the change safe? If a type checker accepts a program, what prevents that program from calling a number as a function? To answer questions like these, we give programming languages mathematical definitions and use them to reason about programs, their execution and their transformations.

Part 1 begins with IMP, a small language of assignments, conditionals and loops. We define how its programs run, then use those definitions to prove properties of loops, verify a compiler and justify two optimizations. Part 2 introduces functions and types. The central question is what a program’s type tells us about its execution, even as the language gains references and abstract types. Part 3 brings these ideas together. We ask when a client can distinguish two implementations of the same interface. We then return to recursion and prove that whenever the mathematical meaning of a closed numeric program predicts a result, running the program produces it.

The book assumes programming experience and introduces proofs from the beginning. In the first chapter, one expression is enough to learn how to read a rule, build a derivation and choose what to induct on. The same habits carry over to proofs about loops, functions and recursion.

*How to read this book.* Each of the thirty-eight chapters was written for a one-hour seminar. The opening summary identifies the proof or calculation to work through on the board. Exercises, a plan for the hour and solutions follow the main text. Part 1 can be read on its own. Part 2 needs only the first three chapters of Part 1. The optional Part 3 draws on the fixed points of Sessions 8–9 and the typed languages of Part 2. The [IMP](imp-card/index.html), [stack machine](machine-card/index.html) and [lambda calculus](lambda-card/index.html) reference cards collect the rules. The [glossary](glossary/index.html) gives the Korean equivalents of technical terms.

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
