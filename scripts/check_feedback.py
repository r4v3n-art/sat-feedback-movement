"""Finite, reproducible checks for the hidden-formula SAT paper. Python stdlib only."""
from fractions import Fraction
from functools import cache
from itertools import combinations, product
from math import comb
from typing import NamedTuple


class Clause(NamedTuple):
    mask: int            # Variables appearing in this clause, each once.
    positive: int        # Positive literal positions.

    def true_literals(self, assignment):
        return self.mask & ~(assignment ^ self.positive)


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def sparse_correction(coefficients):
    """Solve A v = (0,...,0,1); all nonpivot coordinates are zero."""
    pivots = {}
    for index, mask in enumerate(coefficients):
        rhs = int(index + 1 == len(coefficients))
        while mask:
            pivot = mask & -mask
            if pivot not in pivots:
                pivots[pivot] = mask, rhs
                break
            row, previous_rhs = pivots[pivot]
            mask ^= row
            rhs ^= previous_rhs
        else:
            raise AssertionError("The coefficients must be independent")
    answer = 0
    for pivot in sorted(pivots, reverse=True):
        row, rhs = pivots[pivot]
        if ((row & answer).bit_count() % 2) != rhs:
            answer |= pivot
    assert answer.bit_count() <= len(coefficients)
    return answer


def advance(x, guide, rows, clause, batch=1):
    """One move, with at most batch flips. Only the returned violated clause is visible to the learner."""
    assert not clause.true_literals(x)
    if clause.true_literals(guide).bit_count() % 2 == 0:
        rows = (*rows, clause.mask)
        guide ^= sparse_correction(rows)
    candidates = clause.true_literals(guide)
    assert candidates
    change = candidates & -candidates
    remaining = (x ^ guide) ^ change
    for _ in range(1, batch):
        if not remaining:
            break
        bit = remaining & -remaining
        change |= bit
        remaining ^= bit
    return x ^ change, guide, rows


def all_clauses(n):
    for width in range(1, min(n, 3) + 1):
        for variables in combinations(range(n), width):
            mask = sum(1 << i for i in variables)
            for signs in product(range(2), repeat=width):
                yield Clause(mask, sum(s << i for i, s in zip(variables, signs)))


def exhaust_feedback(n):
    # At each node allow *every* violated signed clause compatible with the
    # planted witness. This includes every oracle order for every subformula.
    cases = 0
    max_flips = 0
    for witness in range(1 << n):
        clauses = [c for c in all_clauses(n) if c.true_literals(witness).bit_count() % 2]
        @cache
        def visit(x, guide, rows, steps):
            rank = len(rows)
            assert steps + (x ^ guide).bit_count() <= rank*(rank+1)//2
            longest = steps
            for clause in clauses:
                if not clause.true_literals(x):
                    new_state = advance(x, guide, rows, clause)
                    assert new_state[0] ^ x in tuple(bits(clause.mask))
                    longest = max(longest, visit(*new_state, steps+1))
            return longest
        for x in range(1 << n):
            max_flips = max(max_flips, visit(x, x, (), 0))
        cases += visit.cache_info().currsize
        visit.cache_clear()
    return cases, max_flips


def separation_family(n):
    for i in range(n):
        yield Clause(1 << i, 1 << i)
        for j, k in combinations((j for j in range(n) if j != i), 2):
            yield Clause((1 << i) | (1 << j) | (1 << k), 1 << i)


def check_walk(n):
    clauses = list(separation_family(n))
    for x in range((1 << n) - 1):
        j = x.bit_count()
        bad = [c for c in clauses if not c.true_literals(x)]
        ternary = [c for c in bad if c.mask.bit_count() == 3]
        assert len(ternary) == (n-j)*comb(j, 2)
        assert len(bad) - len(ternary) == n-j
        assert all((c.mask & ~x).bit_count() == 1 for c in bad)
    # Exact rational first differences for uniformly sampled violated clauses.
    delta = Fraction(1)
    expectation = delta
    for j in range(2, n):
        count = comb(j, 2)
        p = Fraction(3 + count, 3*(1 + count))
        delta = (1 + (1-p)*delta) / p
        expectation += delta
    return expectation


def simplex_check(batch):
    # Binary [7,3,4] simplex code. An information set has masks 1, 2, 4.
    checks = []
    for i in (3, 5, 6, 7):
        low = i & -i
        mask = (1 << (i-1)) | (1 << (low-1)) | (1 << ((i ^ low)-1))
        checks.extend(c for c in all_clauses(7) if c.mask == mask
                      and (mask ^ c.positive).bit_count() % 2)
    words = [x for x in range(128) if all(c.true_literals(x) for c in checks)]
    assert len(words) == 8
    assert min((x ^ y).bit_count() for x, y in combinations(words, 2)) == 4
    info_mask = sum((1, 2, 8))
    moves = []
    public_moves = []
    for target in words:
        pins = [Clause(bit, target & bit) for bit in (1, 2, 8)]
        x = guide = 0
        rows = ()
        steps = 0
        while (bad := next((c for c in checks + pins if not c.true_literals(x)), None)):
            x, guide, rows = advance(x, guide, rows, bad, batch)
            steps += 1
            assert steps <= len(rows)*(len(rows)+1)//2
        assert x == target
        moves.append(steps)

        # A second strategy knows the public code. After a failed pin it
        # targets the codeword with that bit corrected and the suffix unchanged.
        # Only the oracle, below, uses the secret pins.
        x = guide = steps = 0
        while (bad := next((c for c in checks + pins if not c.true_literals(x)), None)):
            if bad.mask.bit_count() == 1:
                guide ^= next(w for w in words if (w & info_mask) == bad.mask)
            toward = x ^ guide
            candidates = bad.mask & toward
            assert candidates
            change = candidates & -candidates
            for bit in list(bits(toward ^ change))[:batch-1]:
                change |= bit
            x ^= change
            steps += 1
        public_moves.append(steps)
    optimal = Fraction(3*((4+batch-1)//batch), 2)
    assert Fraction(sum(public_moves), len(words)) == optimal
    mean = Fraction(sum(moves), len(words))
    assert mean >= Fraction(3*((4+batch-1)//batch), 2)
    return mean, optimal


if __name__ == "__main__":
    for size in range(1, 4):
        states, flips = exhaust_feedback(size)
        print(f"All legal feedback, n={size}: {states} states, maximum {flips} flips")
    for size in (3, 4, 6, 8):
        print(f"Uniform-clause exact mean, n={size}: {check_walk(size)}")
    for batch in (1, 2, 3, 7):
        generic, optimal = simplex_check(batch)
        print(f"Simplex, batch={batch}: learner {generic}, public-code optimum {optimal} rounds")
