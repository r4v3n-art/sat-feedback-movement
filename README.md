# How Far Can a SAT Search Move on One Piece of Feedback?

C.J. Bordeleau · Independent Researcher · November 2026

A hidden CNF has a witness with an odd number of true literals in every clause. Each failed query reveals one violated clause. If a move can flip at most `B` variables and must touch that clause, the minimax movement cost on `N` variables is Θ(N + N²/B). The paper also compares the parity learner with memoryless search under the same uniform-clause feedback.

[Read the paper (PDF)](paper/main.pdf) · [LaTeX source](paper/main.tex) · [Lean theorem statements and axiom audit](SatWalk/Main.lean)

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
