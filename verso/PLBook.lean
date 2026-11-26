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

We can often say something about a program before we run it, even on a first reading. The program is new to us, but we know the language it is written in. Which of the conclusions we draw as we read can we rely on, and under what assumptions? This book explores that question through programming language semantics. We give small languages precise mathematical definitions and use them to prove claims about the programs we write in them.

Part 1 begins with IMP, a language of assignments, conditionals, and loops. We define how its programs run. With that definition in hand, we can prove what remains true from one iteration of a loop to the next. We can also show that whenever a source program terminates, its compiled code terminates with the same final values for all its variables. Part 2 asks what we can know before execution begins. For a well-typed program with no free variables, type safety gives a guarantee at every stage of a run from empty memory. Either the program has reached a value or it can take another step. We study this guarantee for functions and mutable references, then see how an abstract type lets a program use data without knowing how they are represented.

Part 3 turns to what a program can observe. Two implementations of an interface may represent their data differently. We study a small language of clients that use a counter through its interface. Under what conditions does every well-typed client of numeric type denote the same number with either implementation? The final chapters bring a related question to recursion. Suppose our mathematical model assigns a number to a program of natural-number type with no free variables. What justifies the prediction that the program will terminate and return that number?

The book assumes programming experience and introduces proof from the beginning. In the first chapter we take a familiar arithmetic expression, give rules for evaluating it, and prove that once the values of its variables are fixed, the rules determine a unique result. This is a pattern worth learning early. A good proof often begins by asking exactly what a familiar claim means.

*How to read this book.* Each of the thirty-eight chapters is designed for a one-hour seminar, with a proof or calculation to work through together. Part 1 can be read on its own. Readers interested in functions and types can move to Part 2 after Chapters 1–3. The optional Part 3 draws on the fixed points of Chapters 8–9 and the typed languages of Part 2. Three reference cards collect the rules for [IMP](imp-card/index.html), the [stack machine](machine-card/index.html), and the [lambda calculus](lambda-card/index.html). The [glossary](glossary/index.html) gives Korean equivalents for the technical terms.

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
