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

Can a compiler replace `x := x + 0` with `skip`, the command that does nothing? In our first language, both commands leave every integer variable with its original value. Yet the assignment takes one step and `skip` takes none. Whether the replacement preserves behavior depends on what we observe.

We start by giving expressions and loops precise rules of execution. With those rules we can prove that a compiled program produces the same result whenever its source program terminates. Later chapters ask what types guarantee about execution and when a client can distinguish two implementations of the same interface. We assume familiarity with programming. The first chapter introduces proof by induction as we show that two ways of evaluating an expression always give the same integer.

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
