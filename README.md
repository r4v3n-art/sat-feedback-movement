# How Far Can a SAT Search Move on One Piece of Feedback?

C.J. Bordeleau · Independent Researcher · November 2026

How many times do you have to revise a plan when each rejection reveals just one broken rule? This paper answers that question for a class of Boolean constraints where you can change only a few decisions at a time.

[Read the paper (PDF)](paper/main.pdf) · [LaTeX source](paper/main.tex) · [Lean theorem statements and axiom audit](SatWalk/Main.lean)

## A party with hidden seating rules

You’re seating guests at two long tables, one in the garden and one in the hall, with plenty of room at both. The host knows all the family drama. You hand over a seating chart, and the host either approves it or tells you one rule you broke. Before asking again, you can move up to `B` guests to the other table. At least one must be named in the complaint.

Suppose the host tells you these two rules over the course of the evening.

- “At least one of Alex, Cam, or Jo needs to be in the garden to keep the cousins civil.”
- “At least one of Alex, Cam, or Sam needs to be in the garden to keep the speeches short.”

Each seating rule corresponds to a SAT clause with up to three conditions about who sits where. The paper makes one special promise. There is a chart where an **odd** number of the conditions in every rule hold. For each rule above, that means one or three of its guests are in the garden. Alex and Cam contribute the same count to both rules, so **Jo and Sam must be at the same table in that promised chart**. You’ve learned something about two guests the host never mentioned together. The solver keeps deductions like this and uses them to guide later moves. The host approves any chart that satisfies all the rules.

## From seating charts to a bound

The chart is the current assignment, a complaint is one violated clause, and moving a guest flips one Boolean variable. The paper counts **revisions**. You submit a chart, hear one complaint, move up to `B` guests, and submit again. A run with six revisions uses seven reports from the host, including final approval.

**What the learner can guarantee.** It keeps a pencil copy of the seating chart that meets every parity rule learned so far. When a reported rule has an even count on the pencil copy, the learner has found an independent fact and must correct the copy. On the first such correction it can repair the pencil copy by changing at most one seat, on the second at most two, and on the `i`th at most `i`. The submitted chart moves toward the pencil copy after each complaint. Even if a new complaint changes the plan mid-course, the `i`th correction adds at most `i/B` rounded up to the overall revision budget.

For example, if the learner makes four independent corrections over a run and may move two guests at once, the **whole run takes at most six revisions** (1 + 1 + 2 + 2). With one guest per revision, four corrections give a bound of ten. There can be at most `N` independent corrections for `N` guests.

**What any solver can be forced to spend.** The paper constructs parties with a set of public seating rules and a private list of preferences. The host checks the private list only when the chart passes every public rule. The public rules are chosen so that any two charts passing them differ on a fixed fraction of the guests. A wrong guess about a new private preference therefore forces a long trip to the next informative chart. With uniformly hidden preferences, even a solver that knows all the public rules guesses wrong on half the new preferences on average. The number of preferences is proportional to `N`, and each such trip costs at least a constant times `N/B` revisions.

Together these bounds give **Θ(N + N²/B)**. Up to constant factors, this is both what the learner can guarantee and what some party can force, even for a randomized solver in expectation. With one guest per revision the worst case grows quadratically. With enough room in the budget to reseat everyone at once, it still grows linearly.

## Why this matters

Think of a test rig where each run reports one failed check and you can change only a few settings before the next run. If your next candidate differs in five settings and the rig accepts two changes per run, it takes at least three runs just to reach it. Along the way another failure might change which candidate you want to try. The seating model puts a number on the combined cost of discovering the rules and acting on what you learn.

Memory matters even with the same feedback. On one family of seating problems, the host picks a broken rule uniformly at random each time. Moving a randomly chosen guest from that complaint takes exponentially many moves on average. A solver that remembers the rules and learns from them finishes within `N(N + 1)/2` single-guest moves on every run.

## Build and verify

Install [Elan](https://lean-lang.org/install/) and use the toolchain and dependency manifest committed here. The proof uses Lean and Mathlib 4.36.0. Run from the repository root.

```sh
lake exe cache get $(sed -n 's/^import \(Mathlib\.[A-Za-z0-9_.]*\)$/\1/p' SatWalk/*.lean | sort -u)
lake build
lake env lean SatWalk/Main.lean
```

The first command downloads compiled Mathlib dependencies. The final command prints the axioms of each audited declaration. The allowed set consists of `propext`, `Classical.choice`, and `Quot.sound`.

```sh
./scripts/verify.sh
python3 scripts/check_feedback.py
```

The verification script checks the axiom lists, exports the proof terms and invokes Lake's paranoid kernel replay. On Linux, the sandboxed replay requires working unprivileged user namespaces and bubblewrap. On macOS, the script runs the local checkers with Lake's sandbox disabled. Python 3.10 or later runs the supplementary finite examples using the standard library.

## Theorem map

| Paper claim | Lean entry point |
| --- | --- |
| Theorem 1.1, rank-sensitive movement bound and termination | [UpperBound.lean](SatWalk/UpperBound.lean) |
| Polynomial bit work and workspace in the dense implementation | [ResourceBound.lean](SatWalk/ResourceBound.lean) |
| Theorem 1.2, fixed-instance randomized lower bound for every sufficiently large size | [LowerBound.lean](SatWalk/LowerBound.lean) |
| Constant-distance-fraction LDPC construction and its signed CNF encoding | [LDPCCode.lean](SatWalk/LDPCCode.lean), [ParityGadget.lean](SatWalk/ParityGadget.lean) |
| Theorem 1.3, dense and sparse separation under fixed and uniform initialization | [Separation.lean](SatWalk/Separation.lean) |
| Binomial mistake tail and the optimal mean on simplex codes | [MistakeTail.lean](SatWalk/MistakeTail.lean), [SimplexCalibration.lean](SatWalk/SimplexCalibration.lean) |
| Exact mean hitting time for triple-first reporting | [PriorityCalibration.lean](SatWalk/PriorityCalibration.lean) |
| Equivariance of the memoryless kernel and of the history-aware learner | [Memoryless.lean](SatWalk/Memoryless.lean), [SignedLearner.lean](SatWalk/SignedLearner.lean) |

The [oracle model](SatWalk/Model.lean) defines the observable report and legal physical moves. Section 4 constructs the sparse family using permutation layers and obtains the hitting-time bound from a finite-horizon recurrence. The Lean proof follows both steps. The bit-cost theorem measures the formal machine's bit operations and temporary storage. Runtime and allocation by a particular Lean compiler are outside that model.

## Rebuild the paper

Install Noto Sans and run `tectonic paper/main.tex`. A current XeLaTeX installation also works with Noto Sans installed. The PDF in this repository is the author manuscript.

## Citation and licensing

Use [CITATION.cff](CITATION.cff) to cite the preprint or software artifact. The Lean code, scripts and build configuration are licensed under [Apache-2.0](LICENSE). The manuscript and PDF are licensed under [CC BY 4.0](paper/LICENSE.md).
