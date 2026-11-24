# Learning from Violated Clauses in Hidden SAT

*Tight Movement Bounds under an Odd-Parity Promise*

C.J. Bordeleau · Independent Researcher · November 2026

![Schematic of a cube of assignments. A crimson path doubles back on the left. On the right, cyan planes intersect and a stepped path approaches a gold vertex.](docs/figures/feedback-guided-search.jpg)

The crimson walker uses only the latest report of a broken rule. The cyan learner remembers earlier reports and uses their parity equations to guide its next move. [How to read the diagram](#two-searches-on-the-same-cube)

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

### Two searches on the same cube

![Schematic of a cube of assignments. A crimson path doubles back on the left. On the right, cyan planes intersect and a stepped path approaches a gold vertex.](docs/figures/feedback-guided-search.jpg)

In this schematic, each vertex represents one way to seat all $N$ guests. Both searchers hear one uniformly chosen complaint about their current chart.

**Left (crimson).** The memoryless walker moves one guest chosen uniformly from the complaint. It keeps no record of past complaints and can return to a chart it has already tried. For each fixed $0<\varepsilon<1$, there are families where each guest appears in only a bounded number of rules, yet from a uniformly random chart the walk takes $\Omega((2-\varepsilon)^N)$ moves in expectation.

**Right (cyan).** Each plane represents an affine parity equation over $\mathbb{F}_2$. Each independent equation halves the set of charts still possible as the promised odd-parity witness. The learner keeps a guide in their intersection and moves up to $B$ guests toward its current guide after each complaint. New feedback can change the guide along the way. The gold point represents one chart the host would accept.

With **one guest per move**, the learner needs at most $N(N+1)/2$ moves on every run, even on the crimson walk’s hard instances. The $\Theta(N+N^2/B)$ label gives the optimal worst-case cost across all promised instances when up to $B$ guests may move at once.

## Relation to earlier work

To our knowledge, this is the first tight bound on how many revisions a solver needs in this hidden-clause, odd-parity model for every batch size from one guest to the whole party. Earlier work studied how many trials it takes to learn from a rejected proposal and how many mistakes it takes to learn parity. Here the solver also has to *get to* its next proposal, and the paper proves how much that can cost even for the best strategy. [Hidden constraint problems](https://arxiv.org/abs/1406.5336) · [Learning parities](https://doi.org/10.1016/j.ipl.2010.10.009)

The dense example where a random walk takes exponential time is due to earlier work. The paper uses it to compare two solvers that receive the same kind of complaint and make different use of their history. [Zhou, He and Nie, Proposition 2](https://pmc.ncbi.nlm.nih.gov/articles/PMC2774825/)

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
