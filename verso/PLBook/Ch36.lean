import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Interleaving and Atomicity" =>
%%%
tag := "ch36"
file := "chapter-36"
%%%

[Chapter PDF](print/chapter-36.pdf) · [Session 36](seminar/index.html#week-36)

Two threads each increment a shared integer initially equal to zero. The possible final values depend on which operations form one indivisible transition. Choosing an interleaving semantics therefore includes choosing a unit of atomic execution.

*Sources.* Reynolds, _Theories of Programming Languages_, chapter 8, especially §§8.1–8.2, pp. 155–159, on concurrent composition and critical regions. We compare two explicitly specified transition granularities under sequentially consistent shared memory. [Reynolds, shared-variable concurrency.](https://www.cs.cmu.edu/~jcr/tpl-toc.html)

# Configurations and schedules
%%%
tag := "ch36-s1"
%%%

A parallel configuration consists of two local control states and one shared store. At each step select one enabled thread and perform its next atomic action. Its local state and the shared store may change; the other local state stays fixed. When both threads have finished, the parallel command terminates. A *schedule* is the sequence of thread choices in a run. Each thread’s actions retain their own program order, even though the combined run may alternate between threads.

In the first semantics, an assignment `x := x + 1` reads, adds and writes in one transition. If increments from threads A and B are both pending at $`x = 0`, either can go first. In either order the first writes one and the second reads that one and writes two. In fact, after $`k` completed increments the value is $`k` by induction on steps. Every maximal execution completes both increments because each thread has just one enabled action and no blocking transition.

For a precise count of atomic executions, label the pending increments A and B. A configuration can be represented by a set of labels still pending together with the current integer. A step removes one label and increments the integer. From a starting value m the equation “current value plus number pending equals m plus two” is invariant: one summand rises by one and the other falls by one. An empty pending set is exactly termination. Consequently the invariant establishes the final value m plus two in *every* terminating execution. The decreasing number of pending labels gives a separate argument that every maximal execution actually terminates.

The schedule disappears from the final equation for a specific reason. In this model each thread reads the current shared value and writes its successor within the same transition. The invariant proof requires that exact update. If a source step exposes only the write while the read happened earlier, the value written need not be the successor of the current shared value. There is then no justification for the arithmetic step in the invariant proof, even if both threads execute exactly once.

# Separate reads and writes
%%%
tag := "ch36-s2"
%%%

In the second semantics, each thread first atomically loads $`x` into a private register, adds one to that register, then atomically writes its register back to $`x`. The private registers are distinct. A read observes the most recent shared write in the combined execution. Here is a complete legal schedule:

```
A reads 0     B reads 0
A computes 1  B computes 1
A writes 1    B writes 1
```

Each thread used the value returned by its own read. At the final configuration $`x = 1`. The second write overwrote a result based on the same old value. Running all three actions of A before B instead yields $`x = 2`.

*Proposition 36.1.* From initial zero the exact set of final values under separate reads and writes is one and two. There are exactly two writes. The first writer necessarily read zero, since no shared write preceded its read; it therefore writes one. The last writer read either before or after that first write. In the first case it writes one; in the second it writes two. The exhibited schedules realize both. Under the atomic assignment semantics only two is possible, so replacing an atomic increment with these steps fails to preserve its set of observations in this parallel context.

Write the order constraints for the six actions explicitly. Inside each thread its read precedes its compute and its compute precedes its write. There is no constraint between a read in A and a write in B beyond the order eventually chosen by the scheduler. For a final value of two, the last writer must have read one. The only action capable of supplying that one is the other thread's write, so that write must occur before the last writer's read. Conversely, that order forces the last writer to read one and then write two. This gives a necessary and sufficient ordering condition without enumerating all interleavings.

The equivalent condition for the final value one is that both reads occur before the first write. It permits many schedules. One thread may complete its private addition before the other has even read; what matters is whether it has made the new value visible. This is why a trace of source lines saying only “A incremented” and “B incremented” is insufficient evidence of atomic increments. The observation of lost updates depends on where a shared read and a shared write occur.

# Critical regions
%%%
tag := "ch36-s3"
%%%

Suppose both threads acquire the same mutex before their load and release it after their store. Acquisition succeeds only while the mutex is free, and a successful acquisition prevents another successful one until release. Therefore the shared read and write of each increment lie in a region that cannot overlap the other increment’s region. Each completed run induces an order of the two regions, so the second region reads one and the final value is two. This conclusion about completed runs uses mutual exclusion. A progress claim for a general lock implementation would separately require assumptions about waiting and scheduling.

Protecting only the writes permits both unprotected reads to observe zero before either write acquires the lock. Each write then serializes successfully but both still write one. Choosing the correct protected operation requires inspecting what earlier value each write depends on.

A lock proof can be phrased as an induction over critical-region completions. Assume the mutex begins free, both threads obey its acquisition protocol, and a thread releases it only after writing. At acquisition the shared cell equals the initial value plus the number of completed regions. While the owner holds the mutex no competing increment can modify the cell. Its saved read therefore still equals the shared value at the owner’s write. That write increases the cell exactly once, reestablishing the assertion on release. Applying the argument at two releases yields the same result as two indivisible increments. It says nothing about unrelated threads that bypass the protocol.

The two schedules below calculate the arithmetic part of this proof and of its counterexample. The function arguments represent the values actually sampled by the reads. Establishing that the mutex forces the serial read ordering is the preceding operational argument.

```lean
def writeIncrement (sample : Int) := sample + 1

example (m : Int) : writeIncrement (writeIncrement m) = m + 2 := by
  unfold writeIncrement
  omega

example (m : Int) : writeIncrement m ≠ writeIncrement (writeIncrement m) := by
  unfold writeIncrement
  omega
```

With both samples equal to m, the last writer produces the left value of the inequality. A sample taken after the first committed write produces the right value.

The enabled atomic steps determine which interleavings belong to the transition system. With a fixed initial store, compare the sets of reachable final shared stores before and after combining a read and a write into one atomic step.

# Exercises
%%%
tag := "ch36-s4"
number := false
%%%

1. Start from an arbitrary integer $`m`. Compute the two sets of final values for the two granularities.
2. Give a schedule where A reads first but B writes first. Can its final result be two?
3. Both threads access different shared variables using separate reads and writes. Explain which step of the lost-update argument is no longer available.

*Further problem.* Add a third thread reading x just once and returning the value observed. Restrict attention to complete runs from x = 0 in which the two split increments leave final x = 1. List the possible values returned by the reader and prove both completeness and attainability.

# Reading for the Seminar
%%%
tag := "ch36-s5"
number := false
%%%

*Definitions · 10 minutes.* Specify each transition and its private and shared components before proposing a schedule.

*Joint proof · 30 minutes.* Construct the lost-update run and prove that no final value other than one or two is reachable. Compare the proof with the atomic semantics.

*Proof review · 20 minutes.* Protect just the writes and test the same schedule. Move the start of the critical region until the unwanted outcome is excluded.

*Facilitator’s hint.* Focus on the thread performing the final write. Its saved register depends on the shared value at its read, not on the value just before its write.

# Solutions
%%%
tag := "ch36-s6"
number := false
%%%

*1.* Atomic increments give only $`m + 2`. Separate actions give $`m + 1` or $`m + 2` by the same first-writer argument.

*2.* For example A reads, B reads, B computes and writes, then A computes and writes. The final value is one. If A reads before B’s read and B writes before A, both reads precede either write, so two is impossible.

*3.* A write to one location cannot overwrite the value read from or written to the other. Projecting the interleaving onto either thread gives its isolated update on that variable.

*Further problem.* Since the final value is one, both incrementing threads must have sampled zero. Otherwise the final writer would have sampled one and written two. Thus each of the only two writes stores one. The reader can see zero if it reads before both writes and one if it reads after at least one write; no other integer has ever been stored. For witnesses, first schedule both incrementing reads. Place the extra read either immediately afterwards or after the first committed write, then finish the two increments. Both schedules still end at one. Merely knowing the final value constrains but does not completely determine observations made inside the run. A correctness condition including intermediate reads must account for those observation points.
