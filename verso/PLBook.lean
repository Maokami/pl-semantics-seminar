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

This is the textbook of the HyperAccel PL Study Group. It teaches the semantics of programming languages in 38 sessions of one hour, one chapter for each session. Before a session, one member reads the chapter. A session has three parts: ten minutes on the definitions and an example, thirty minutes in which that member leads the proof of one case of the main theorem on a whiteboard, and twenty minutes of review. The book assumes programming experience. It does not assume experience with proofs. Sessions 1–3 introduce inference rules, derivations and induction, and the later sessions use them in the same way.

*What the theorems say.* Most theorems of the book have one shape. A program is described in two ways, and the theorem states under which assumptions the two descriptions agree on what can be observed.

* Session 6. A command runs from store $`s` to store $`t` by the big-step rules exactly when small steps take it to $`\mathsf{skip}` with store $`t`. In symbols, $`s\vdash c\Downarrow t` if and only if $`\langle c,s\rangle\to^*\langle\mathsf{skip},t\rangle`.
* Session 16. If a command terminates, the code compiled from it runs to its end and produces the same store.
* Session 26. A closed term that has a type is a value or can take a step, and the step keeps the type.

Reading such a theorem means finding its assumptions and its observation. Sessions 21, 32 and 38 close the three parts by restating the main theorems with every premise in place.

*Part 1 · IMP (Sessions 1–21).* One small imperative language with assignment, conditionals and loops is used throughout. Sessions 1–7 define how expressions and commands execute and develop induction on derivations. Sessions 8–13 give each command a mathematical meaning as a function on stores, prove that this meaning agrees with execution, and prove programs correct in Hoare logic. Sessions 14–20 compile the language to a stack machine and analyze it. They prove that compilation, constant propagation and the elimination of dead assignments preserve what a program computes. Part 1 is a complete course by itself.

*Part 2 · Functions and types (Sessions 22–32).* One typed lambda calculus grows by one feature at a time: Booleans and numbers, functions, products and sums, type inference and let-polymorphism, references, and type abstraction. The recurring question is what a type checker guarantees. A well-typed program does not get stuck. Sessions 24, 26, 27 and 30 each add rows to one safety table and prove one new case. Session 31 shows how an existential type hides the representation of an abstract type.

*Part 3 · Logical relations and PCF (Sessions 33–38, optional).* Session 33 proves that two implementations of an abstract type that are related operation by operation give every client the same observable result. Sessions 34–37 lead to computational adequacy for PCF: if the mathematical meaning of a closed program of ground type is the number $`n`, then the program evaluates to $`n`.

*How a chapter is organized.* Every chapter opens with a session card. The card lists the definitions the session uses and where they come from, at most five new terms, the main theorem and its source, the case to present on the board, an outline of the proof, and what changed from the previous session. The numbered sections are the reading for the session. Three unnumbered sections follow: exercises, a plan for the hour, and solutions with further reading.

*Labels.* Each numbered result says where it comes from and how it was checked. \[This book\] marks a statement formulated here for the book’s definitions. \[Corresponding: …\] names a theorem of the same form in another text. \[Checked\] means that building the book checks a Lean proof of the stated result on the shared definitions. \[Externally checked: …\] means that the statement matches a checked declaration in the cited development. \[Paper proof only: …\] means that the proof is given on paper. [Label key](glossary/index.html)

*Reference pages.* Three cards collect the definitions and rules, and each card section names the session that introduces it: the [IMP language card](imp-card/index.html), the [stack machine card](machine-card/index.html) and the [lambda language card](lambda-card/index.html). The [glossary](glossary/index.html) lists every technical term with its Korean equivalent and the place where it is defined.

*Sources.* The IMP definitions follow the Lean port of Xavier Leroy’s course on compiler verification. Sessions 8–10 follow Reynolds, _Theories of Programming Languages_, and Winskel, _The Formal Semantics of Programming Languages_. Sessions 11–13 follow Nipkow and Klein, _Concrete Semantics_. Part 2 follows Pierce, _Types and Programming Languages_. Session 33 follows Pfenning’s lecture notes on representation independence, and Sessions 34–38 follow the Cambridge lecture notes on denotational semantics. Each chapter cites the sections it uses.

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
