import VersoManual

open Verso.Genre Manual

#doc (Manual) "What Type Safety Says" =>
%%%
tag := "ch32"
file := "chapter-32"
%%%

* *Definitions.* The typed language and the judgment $`\Gamma\mid\Sigma\vdash t:T` ([Lambda card, Judgments](lambda-card/index.html)). Closed terms and $`\to^*` ([C.1](lambda-card/index.html#lambda-c1)). Stuck terms ([C.2](lambda-card/index.html#lambda-c2)). Injections and case terms ([C.4](lambda-card/index.html#lambda-c4)). Stores, store typings, $`\Sigma\subseteq\Sigma'` and well-typed stores ([C.6](lambda-card/index.html#lambda-c6)). The general statements, safety and Rows 1–6 of the safety table ([C.8](lambda-card/index.html#lambda-c8)). Free variables of a typed term ([Session 25, Lemma 25.1](chapter-25/index.html#ch25-s1)). Inversion for products and sums and the substitution lemma ([Session 27, Lemmas 27.1 and 27.4](chapter-27/index.html#ch27-s1)). Store weakening and canonical forms for Ref ([Session 30, Lemmas 30.2 and 30.4](chapter-30/index.html#ch30-s2)).
* *New terms.* None. [Glossary and label key](glossary/index.html)
* *Safety, restated.* For every $`\Sigma`, $`\mu`, $`t`, $`t'`, $`\mu'` and $`T`: if $`\varnothing\mid\Sigma\vdash t:T`, $`\varnothing\mid\Sigma\vdash\mu` and $`t\mid\mu\to^*t'\mid\mu'`, then there is a store typing $`\Sigma'` with $`\varnothing\mid\Sigma'\vdash t':T` and $`\varnothing\mid\Sigma'\vdash\mu'`, and $`t'` is a value or $`t'\mid\mu'\to t''\mid\mu''` for some $`t''` and $`\mu''`. There is no new theorem: §32.1 restates this statement and [Session 30, Theorems 30.5–30.6](chapter-30/index.html#ch30-s3) with every premise, and names the premises that [Session 24, Theorems 24.3–24.4](chapter-24/index.html#ch24-s3), [Session 26, Theorem 26.3](chapter-26/index.html#ch26-s2) and [Session 27, Theorem 27.3](chapter-27/index.html#ch27-s2) wrote into their notation.
* *Source.* No new source. Each restated theorem keeps the source and proof status of its session: TAPL §8.3 for Session 24, §9.3 for Sessions 26 and 27, §13.5 for Session 30. [Source sections](lambda-card/index.html#lambda-sources) · [TAPL contents](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)
* *Board case.* Row 3 of the safety table with every premise, applied to the first two steps of $`u` (§32.2). Six steps: progress and preservation for each step, then the premises used.
* *Proof outline.* No induction. Each entry of the table is applied in three moves: check its premises, name the rule that steps or the lemma that retypes, and read off the next term, store and store typing.
* *From Session 31.* Session 31 added Row 6 without proof. Here the rows proved in Sessions 24, 26, 27, 29 and 30 are collected in their final form, with the premises that each session left implicit.

Let $`u=\mathsf{case}\ (\mathsf{inr}\ (\mathsf{ref}\ 0)\ \mathsf{as}\ \mathsf{Nat}+\mathsf{Ref}\ \mathsf{Nat})\ \mathsf{of}\ \mathsf{inl}\ y\Rightarrow\{y,\mathsf{ref}\ y\}\mid\mathsf{inr}\ x\Rightarrow\{{!}x,x\}`. It has type $`\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}`. From the empty store it allocates a cell, selects the right branch, reads the cell and ends at a pair. Type safety says that no such run gets stuck. The rows of the safety table behind that claim were proved in Sessions 24, 26, 27, 29 and 30, each for its own language and each with premises hidden in its notation. Session 24 wrote $`\vdash t:T` for a language without variables. Sessions 26 and 27 used the same notation for the empty context. From Session 30 it abbreviates $`\varnothing\mid\varnothing\vdash t:T`, and progress also needs a well-typed store. This session writes every premise back, runs $`u` through progress and preservation for two steps, and states what type safety does not say.

# The safety table with its premises
%%%
tag := "ch32-s1"
%%%

[Session 24, Theorems 24.3–24.4](chapter-24/index.html#ch24-s3) prove progress and preservation for the language of C.2. [Session 26, Theorem 26.3](chapter-26/index.html#ch26-s2) proves them for C.2–C.3, [Session 27, Theorem 27.3](chapter-27/index.html#ch27-s2) for C.2–C.4, and [Session 30, Theorems 30.5–30.6](chapter-30/index.html#ch30-s3) for the typed language of Session 30, which adds let ([Session 29, Proposition 29.1](chapter-29/index.html#ch29-s1)) and references. A later pair is not a corollary of an earlier one. Its canonical-forms lemma must exclude the new values, its substitution lemma has new cases, and from Session 30 its congruence cases use store weakening. For the terms of an earlier session, with $`\Sigma=\varnothing` and the empty store, the statements of Session 30 read as the earlier ones (C.8). The final statements are these. After them, each premise is listed with the place where it was hidden, the entries that use it, and what fails without it.

*Theorem 30.5 (Progress), restated.* For every term $`t`, type $`T` and store typing $`\Sigma`: if $`\varnothing\mid\Sigma\vdash t:T`, then $`t` is a value or, for every store $`\mu` with $`\varnothing\mid\Sigma\vdash\mu`, there are $`t'` and $`\mu'` with $`t\mid\mu\to t'\mid\mu'`.

*Theorem 30.6 (Preservation), restated.* For every $`\Gamma`, $`\Sigma`, $`\mu`, $`t`, $`t'`, $`\mu'` and $`T`: if $`\Gamma\mid\Sigma\vdash t:T`, $`\Gamma\mid\Sigma\vdash\mu` and $`t\mid\mu\to t'\mid\mu'`, then there is a store typing $`\Sigma'` with $`\Sigma\subseteq\Sigma'`, $`\Gamma\mid\Sigma'\vdash t':T` and $`\Gamma\mid\Sigma'\vdash\mu'`.

*Safety, restated from C.8.* For every $`\Sigma`, $`\mu`, $`t`, $`t'`, $`\mu'` and $`T`: if $`\varnothing\mid\Sigma\vdash t:T`, $`\varnothing\mid\Sigma\vdash\mu` and $`t\mid\mu\to^*t'\mid\mu'`, then there is a store typing $`\Sigma'` with $`\varnothing\mid\Sigma'\vdash t':T` and $`\varnothing\mid\Sigma'\vdash\mu'`, and $`t'` is a value or $`t'\mid\mu'\to t''\mid\mu''` for some $`t''` and $`\mu''`. A program starts with $`\Sigma=\varnothing` and $`\mu=\varnothing`, which meet both premises.

* *The empty context.* The language of Session 24 had no variables, and Sessions 26 and 27 wrote $`\vdash t:T` for $`\varnothing\vdash t:T`. A term typed in the empty context is closed ([Session 25, Lemma 25.1](chapter-25/index.html#ch25-s1)). Only the T-Var case of progress needs the premise to reach its conclusion. The other cases pass it on to premises with the same context, and use it to apply canonical forms, which are stated for the empty context. Without it, progress fails for the right branch of $`u`: $`x{:}\mathsf{Ref}\ \mathsf{Nat}\mid\varnothing\vdash\{{!}x,x\}:\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}`, and $`\{{!}x,x\}` is neither a value nor able to step. Preservation holds in every context.
* *A well-typed store.* Before Session 30 there was no store: read $`\Sigma=\varnothing` and $`\mu=\varnothing`. Progress uses $`\mathrm{dom}(\mu)=\mathrm{dom}(\Sigma)` for T-Deref and T-Assign. Preservation uses the premise for E-RefV, E-DerefLoc and E-Assign. Without it, the term reached after the first step of $`u`, started in the empty store, gets stuck (§32.2).
* *A growing store typing.* Preservation gives some $`\Sigma'` with $`\Sigma\subseteq\Sigma'`. Only E-RefV makes it larger. Safety therefore quantifies the store typing inside its induction on paths ([Session 30, §30.4](chapter-30/index.html#ch30-s4)). If $`\Sigma'=\Sigma` were required, preservation would fail at the first step of $`u`: the term reached contains a location, and the empty store typing gives it no type.
* *The language of the session.* A row that adds forms of value adds exclusion cases to every earlier canonical-forms statement ([Session 26, Lemma 26.2(3)](chapter-26/index.html#ch26-s2); [Session 27, Lemma 27.2(3)](chapter-27/index.html#ch27-s2); [Session 30, Lemma 30.4(b)](chapter-30/index.html#ch30-s3)). A row that adds typing rules adds cases to the substitution lemma ([Session 27, Lemma 27.4](chapter-27/index.html#ch27-s3); [Session 29, §29.1](chapter-29/index.html#ch29-s1); [Session 30, §30.3](chapter-30/index.html#ch30-s3)). From Session 30 the substitution lemma carries a store typing.

Collected, the table of [C.8](lambda-card/index.html#lambda-c8) reads as follows. Each row names what its entries use besides inversion and the induction hypothesis. From Session 30, every computation rule of Rows 1–4 keeps the store and takes $`\Sigma'=\Sigma`. Every congruence rule takes $`\Sigma'` from its premise and retypes the other immediate subterms by store weakening ([Session 30, Lemma 30.2](chapter-30/index.html#ch30-s2)).

* *Row 1 · Bool and Nat · Session 24.* Canonical forms for Bool and Nat. Progress uses them for the guard of a conditional and the argument of succ, pred and iszero. Preservation uses no lemma.
* *Row 2 · Functions and Unit · Session 26.* Canonical forms for $`T_1\to T_2` and Unit. Progress: the empty context excludes T-Var, and T-App uses canonical forms. Preservation: E-AppAbs uses the substitution lemma.
* *Row 3 · Products and sums · Session 27.* Canonical forms for $`T_1\times T_2` and $`T_1+T_2`. Progress: T-Proj1, T-Proj2 and T-Case use them. Preservation: E-CaseInl and E-CaseInr use the substitution lemma.
* *Row 4 · let · Session 29.* No canonical form. Preservation: E-LetV uses the substitution lemma.
* *Row 5 · References · Session 30.* Canonical form for $`\mathsf{Ref}\ T_1`: a location $`l` with $`\Sigma(l)=T_1`. Progress: T-Ref needs a fresh location, and T-Deref and T-Assign need the well-typed store. Preservation: E-RefV enlarges $`\Sigma` and uses store weakening, E-DerefLoc uses the well-typed store, and E-Assign uses store update ([Session 30, Lemma 30.3](chapter-30/index.html#ch30-s2)).
* *Row 6 · Universal and existential types · Session 31.* Stated without proof, with the type substitution lemma ([Session 31, Lemma 31.4 and Theorem 31.5](chapter-31/index.html#ch31-s3)). Its preservation entry also uses the substitution lemma for a language with the forms of C.7, and no session proves the new cases. Safety for the typed language of Session 31 rests on these statements.

# One program, two steps
%%%
tag := "ch32-s2"
%%%

The typing derivation $`D_0` of $`\varnothing\mid\varnothing\vdash u:\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}` ends with T-Case. Its premises are (i) $`\varnothing\mid\varnothing\vdash\mathsf{inr}\ (\mathsf{ref}\ 0)\ \mathsf{as}\ \mathsf{Nat}+\mathsf{Ref}\ \mathsf{Nat}:\mathsf{Nat}+\mathsf{Ref}\ \mathsf{Nat}`, by T-Inr above T-Ref above T-Zero; (ii) $`y{:}\mathsf{Nat}\mid\varnothing\vdash\{y,\mathsf{ref}\ y\}:\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}`, by T-Pair from T-Var and T-Ref; and (iii) $`x{:}\mathsf{Ref}\ \mathsf{Nat}\mid\varnothing\vdash\{{!}x,x\}:\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}`, by T-Pair from T-Deref and T-Var. Let $`l` be a location, $`\mu_1=(\varnothing,l\mapsto 0)`, $`\Sigma_1=(\varnothing,l{:}\mathsf{Nat})`, and let $`u'` be $`u` with $`\mathsf{ref}\ 0` replaced by $`l`. The board case uses Row 3 with every premise written out. Fix a store typing $`\Sigma`.

* *Canonical forms.* For every value $`v`: if $`\varnothing\mid\Sigma\vdash v:T_1\times T_2`, then $`v=\{v_1,v_2\}` for values $`v_1,v_2`. If $`\varnothing\mid\Sigma\vdash v:T_1+T_2`, then $`v` is $`\mathsf{inl}\ v_1\ \mathsf{as}\ T_1+T_2` or $`\mathsf{inr}\ v_2\ \mathsf{as}\ T_1+T_2` for a value $`v_1` or $`v_2`. The proof excludes every other form of value, locations by Session 30, Lemma 30.4(b).
* *Progress.* Let $`D` derive $`\varnothing\mid\Sigma\vdash t:T` and end with T-Pair, T-Proj1, T-Proj2, T-Inl, T-Inr or T-Case, and let $`\varnothing\mid\Sigma\vdash\mu`. If progress holds for the premises of $`D` whose context is empty, then $`t` is a value or $`t\mid\mu` steps by a rule of C.4.
* *Preservation.* Let $`\Gamma\mid\Sigma\vdash t:T`, $`\Gamma\mid\Sigma\vdash\mu` and $`t\mid\mu\to t'\mid\mu'` by a rule of C.4. E-PairBeta1 and E-PairBeta2 keep the store and take $`\Sigma'=\Sigma`. So do E-CaseInl and E-CaseInr, which use the substitution lemma with $`\Sigma`. A congruence rule takes $`\Sigma'` and $`\mu'` from the induction hypothesis for its premise and retypes the other immediate subterms under $`\Sigma'` by store weakening.

*Board case.* We must show that $`u\mid\varnothing` takes two steps, and that after each step the term has type $`\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}` under a store typing that extends the previous one, with a store that is well typed under it. Start with $`\Sigma_0=\varnothing` and $`\mu_0=\varnothing`. This store is well typed, since both domains are empty.

1. *Progress at $`u`* (Row 3, T-Case). The context of $`D_0` is empty and $`\varnothing\mid\Sigma_0\vdash\mu_0`. The first part of $`u` is not a value, because $`\mathsf{ref}\ 0` is not. Apply progress to (i), whose context is empty. T-Inr passes to its premise $`\varnothing\mid\Sigma_0\vdash\mathsf{ref}\ 0:\mathsf{Ref}\ \mathsf{Nat}`. By Row 5, T-Ref, $`0` is a value and $`l\notin\mathrm{dom}(\mu_0)`, so E-RefV gives $`\mathsf{ref}\ 0\mid\mu_0\to l\mid\mu_1`. E-Inr and E-Case lift this step to $`u\mid\mu_0\to u'\mid\mu_1`.
2. *Preservation of step 1, its innermost rule* (Row 5, E-RefV). Since $`l\notin\mathrm{dom}(\mu_0)=\mathrm{dom}(\Sigma_0)`, the store typing $`\Sigma_1=(\Sigma_0,l{:}\mathsf{Nat})` is defined and $`\Sigma_0\subseteq\Sigma_1`. T-Loc gives $`\varnothing\mid\Sigma_1\vdash l:\mathsf{Ref}\ \mathsf{Nat}`. Store weakening types the stored $`0` under $`\Sigma_1`, so $`\varnothing\mid\Sigma_1\vdash\mu_1`.
3. *Preservation of step 1, its congruence rules* (Row 3, E-Inr and E-Case). Both take $`\Sigma_1` from step 2. T-Inr types $`\mathsf{inr}\ l\ \mathsf{as}\ \mathsf{Nat}+\mathsf{Ref}\ \mathsf{Nat}` under $`\Sigma_1`. Store weakening retypes (ii) and (iii) under $`\Sigma_1`. T-Case gives $`\varnothing\mid\Sigma_1\vdash u':\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}`.
4. *Progress at $`u'`* (Row 3, T-Case). Now $`\Sigma=\Sigma_1`, and $`\varnothing\mid\Sigma_1\vdash\mu_1` by step 2. The first part of $`u'` is a value of type $`\mathsf{Nat}+\mathsf{Ref}\ \mathsf{Nat}`, so the canonical forms of Row 3 make it an injection of a value. E-CaseInr gives $`u'\mid\mu_1\to[x\mapsto l]\{{!}x,x\}\mid\mu_1`, and $`[x\mapsto l]\{{!}x,x\}=\{{!}l,l\}`.
5. *Preservation of step 2* (Row 3, E-CaseInr). Session 27, Lemma 27.1(4) and then 27.1(3), read with $`\Sigma_1` and applied to the typing of step 3, give $`\varnothing\mid\Sigma_1\vdash l:\mathsf{Ref}\ \mathsf{Nat}` and $`x{:}\mathsf{Ref}\ \mathsf{Nat}\mid\Sigma_1\vdash\{{!}x,x\}:\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}`. The substitution lemma with $`\Sigma_1` gives $`\varnothing\mid\Sigma_1\vdash\{{!}l,l\}:\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}`. The store is unchanged, so $`\Sigma_1` is the new store typing.
6. *Premises used.* The empty context, in steps 1 and 4: progress was applied to (i) and never to (ii) or (iii), whose contexts are not empty. The well-typed store, in step 2, where $`\mathrm{dom}(\mu_0)=\mathrm{dom}(\Sigma_0)` makes $`\Sigma_1` defined. The growth $`\Sigma_0\subseteq\Sigma_1` and store weakening, in steps 2–3. The canonical forms of Row 3 under $`\Sigma_1\neq\varnothing`, in step 4. The substitution lemma with a store typing, in step 5.

The run ends with $`\{{!}l,l\}\mid\mu_1\to\{0,l\}\mid\mu_1`, by E-Pair1 above E-DerefLoc (Exercise 32.1). There progress needs a cell at $`l`, and the well-typed store gives $`l\in\mathrm{dom}(\Sigma_1)=\mathrm{dom}(\mu_1)`. Start $`u'` instead in the empty store. Still $`\varnothing\mid\Sigma_1\vdash u':\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}`, but the empty store is not well typed under $`\Sigma_1`. E-CaseInr gives $`\{{!}l,l\}\mid\varnothing`, which is not a value and has no step: E-Pair1 needs a step of $`{!}l`, which E-DerefLoc gives only with a cell at $`l`, and E-Pair2 needs $`{!}l` to be a value.

# What type safety does not say
%%%
tag := "ch32-s3"
%%%

As for IMP in [A.6](imp-card/index.html#imp-a6), call a pair $`t\mid\mu` a *configuration*. Call it typed under $`\Sigma` at $`T` when $`\varnothing\mid\Sigma\vdash t:T` and $`\varnothing\mid\Sigma\vdash\mu`. Safety speaks about every finite path from a typed program. Each configuration on the path is typed at $`T` under some store typing, and the last one is a value or takes a step. If the path ends at a value $`v`, then $`\varnothing\mid\Sigma'\vdash v:T`, and the canonical forms of $`T` give the shape of $`v`. The run of $`u` ends at $`\{0,l\}`: a pair, as Row 3 requires, of a numeric value and a location with $`\Sigma_1(l)=\mathsf{Nat}`, as Rows 1 and 5 require. Safety says nothing more.

* *Termination.* The conclusion of safety holds at every configuration of a path that never ends. The program of the Further problem has type Unit and never stops. Without references, every closed well-typed term of the typed language of Session 29 reaches a value. That is a separate theorem, normalization, with a different proof (TAPL §12.1 proves it for a smaller language), and this book does not prove it.
* *Which value.* E-RefV may choose any fresh location, so $`u` may also end at $`\{0,l'\}` with $`l'\neq l`. The two results differ by a renaming of locations ([Session 30, Further problem](chapter-30/index.html#ch30-s6)). Safety does not say that the result is unique.
* *Untyped terms.* Safety assumes a typing. Without one a term may get stuck, as $`\mathsf{if}\ 0\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ \mathsf{false}` does ([Session 24, §24.1](chapter-24/index.html#ch24-s1)), or may run well: $`\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{false}` has no type, yet it steps to $`0` ([Session 24, Exercise 24.2](chapter-24/index.html#ch24-s5)).
* *The inference form.* Theorems 30.5–30.6 concern the typed language, where T-Let generalizes nothing. Without the value restriction the inference form is not safe ([Session 30, Proposition 30.7](chapter-30/index.html#ch30-s5)). With it, this book does not prove the inference form safe.

# Exercises
%%%
tag := "ch32-s4"
number := false
%%%

*32.1.* Take the third step of $`u`, from $`\{{!}l,l\}\mid\mu_1`. Name the entries of Rows 3 and 5 that progress and preservation use, give the store typing after the step, and check the final value against the canonical forms of its type.

*32.2.* Let $`\mu=(\varnothing,l\mapsto\mathsf{true})`. Is $`\mu` well typed under $`\Sigma_1`? Run $`u'\mid\mu` to a value. Does the run get stuck? Does the final value have type $`\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}` under some store typing?

*Further problem.* Let $`p=\mathsf{let}\ r=\mathsf{ref}\ (\lambda y{:}\mathsf{Unit}.y)\ \mathsf{in}\ (r\mathrel{:=}(\lambda y{:}\mathsf{Unit}.({!}r)\,y);\ ({!}r)\ \mathsf{unit})`. Show that $`\vdash p:\mathsf{Unit}` and that the path from $`p\mid\varnothing` never ends. Give one store typing under which every configuration after the first step is typed. Why does this not contradict safety?

# Reading for the Seminar
%%%
tag := "ch32-s5"
number := false
%%%

*Definitions · 10 minutes.* Write Theorems 30.5–30.6 and the safety statement. Underline the premises: a typing, the empty context, a well-typed store, and a store typing $`\Sigma'` with $`\Sigma\subseteq\Sigma'`. For each, name the session whose notation hid it.

*Joint proof · 30 minutes.* The presenter writes Row 3 with every premise and runs $`u` through the six steps of §32.2, with one column for the term, one for the store and one for the store typing. Participants name the row and the entry at each step. Then do Exercise 32.1 together.

*Proof review · 20 minutes.* For each premise of §32.1, give the example that fails without it. Do Exercise 32.2. Close with the Further problem: a typed program that never stops.

*Facilitator’s hint.* Ask three questions at every step: which row, which entry, and which store typing.

# Solutions and Further Reading
%%%
tag := "ch32-s6"
number := false
%%%

*32.1.* Progress, Row 3, T-Pair: the first component $`{!}l` is not a value. Row 5, T-Deref: $`l` is a value of type $`\mathsf{Ref}\ \mathsf{Nat}` under $`\Sigma_1`, so it is a location with $`\Sigma_1(l)=\mathsf{Nat}`, and $`l\in\mathrm{dom}(\mu_1)` because $`\mu_1` is well typed. E-DerefLoc gives $`{!}l\mid\mu_1\to 0\mid\mu_1`, and E-Pair1 lifts it to $`\{0,l\}\mid\mu_1`. Preservation: E-DerefLoc takes $`\Sigma'=\Sigma_1`, and $`\mu_1(l)=0` has type $`\Sigma_1(l)=\mathsf{Nat}` because $`\mu_1` is well typed. E-Pair1 takes $`\Sigma_1` from its premise and retypes $`l` by store weakening, here trivially. T-Pair gives $`\varnothing\mid\Sigma_1\vdash\{0,l\}:\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}`. The value is a pair of values (Row 3) whose first component is a numeric value (Row 1) and whose second is a location with $`\Sigma_1(l)=\mathsf{Nat}` (Row 5).

*32.2.* No: $`\mathsf{true}` does not have type $`\Sigma_1(l)=\mathsf{Nat}`. E-CaseInr gives $`\{{!}l,l\}\mid\mu`, and E-Pair1 above E-DerefLoc gives $`\{\mathsf{true},l\}\mid\mu`, a value. The run does not get stuck. But no store typing gives $`\{\mathsf{true},l\}` the type $`\mathsf{Nat}\times\mathsf{Ref}\ \mathsf{Nat}`, since T-Pair would need $`\mathsf{true}` to have type Nat. The run is not stuck, yet the conclusion $`\varnothing\mid\Sigma'\vdash t':T` of safety fails at its end. Safety needs the well-typed store for its typing conclusion, not only for the absence of stuck configurations.

*Further problem.* Let $`\Sigma_p=(\varnothing,l{:}\mathsf{Unit}\to\mathsf{Unit})`. T-Abs and T-Ref give $`\mathsf{ref}\ (\lambda y{:}\mathsf{Unit}.y)` the type $`\mathsf{Ref}\ (\mathsf{Unit}\to\mathsf{Unit})`. With $`r` of that type in the context, T-Assign, T-Deref, T-App and the sequencing of C.3 give the body type Unit, and T-Let gives $`\vdash p:\mathsf{Unit}`. The steps: E-RefV under E-Let allocates $`l`; E-LetV substitutes $`l` for $`r`; E-Assign under E-App2 stores $`\lambda y{:}\mathsf{Unit}.({!}l)\,y` at $`l`; E-AppAbs gives $`({!}l)\ \mathsf{unit}`; E-DerefLoc under E-App1 gives $`(\lambda y{:}\mathsf{Unit}.({!}l)\,y)\ \mathsf{unit}`; E-AppAbs gives $`({!}l)\ \mathsf{unit}` again with the same store. The last two steps repeat forever. Every configuration after the first step is typed under $`\Sigma_p`, and [Session 30, §30.1](chapter-30/index.html#ch30-s1) types the stored abstraction. Safety asks only that each configuration on a finite path be typed and be a value or step, and each one steps.

*Further reading.* Robin Milner stated the slogan “well-typed programs cannot go wrong” in “A Theory of Type Polymorphism in Programming”, _Journal of Computer and System Sciences_ 17(3), 1978. Andrew Wright and Matthias Felleisen, “A Syntactic Approach to Type Soundness”, _Information and Computation_ 115(1), 1994, proved type soundness syntactically, from facts about single reduction steps. Progress and preservation are a form of that method. TAPL §8.3 presents safety as progress plus preservation, §13.5 extends it to references, and §12.1 proves normalization for functions. [TAPL contents](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf)

# Sources and Formalization
%%%
tag := "ch32-notes"
number := false
%%%

* *Theorem 30.5.* Restated from Session 30; see [its notes](chapter-30/index.html#ch30-notes).
* *Theorem 30.6.* Restated from Session 30; see [its notes](chapter-30/index.html#ch30-notes).
* *Safety (C.8).* Restated from Session 30; see [its notes](chapter-30/index.html#ch30-notes). Formulated in this book from [safety table C.8](lambda-card/index.html#lambda-c8). Paper proof only ([§30.4](chapter-30/index.html#ch30-s4)).
