"""Pure-stdlib zero-floating-point exact-Q primitives for Paper 40:
Brennan Dury (arXiv:2611.32976, Nov 24, 2026)
"Traversing hyperplane arrangements with an affine objective".

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

VecQ = List[Fraction]
# Affine form q(x) = a . x + b represented as (a, b)
AffFormQ = Tuple[VecQ, Fraction]


def format_rat(q: Fraction) -> str:
    """Canonical reduced rational string ('n' if denominator == 1 else 'n/d')."""
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def dot_q(u: Sequence[Fraction], v: Sequence[Fraction]) -> Fraction:
    return sum((a * b for a, b in zip(u, v)), Fraction(0, 1))


def eval_affine_q(form: AffFormQ, x: Sequence[Fraction]) -> Fraction:
    a, b = form
    return dot_q(a, x) + b


def sign_q(v: Fraction) -> int:
    if v > 0:
        return 1
    if v < 0:
        return -1
    return 0


def sign_vector_q(forms: Sequence[AffFormQ], x: Sequence[Fraction]) -> List[int]:
    """Exact sign vector sign_P(x) in {-1, 0, +1}^m."""
    return [sign_q(eval_affine_q(f, x)) for f in forms]


def sign_closure_contains(sig_e: Sequence[int], sig_f: Sequence[int]) -> bool:
    """Proposition 1(3): E subseteq cl(F) iff sign_E(q) in {0, sign_F(q)} for all q."""
    if len(sig_e) != len(sig_f):
        return False
    return all(se == 0 or se == sf for se, sf in zip(sig_e, sig_f))


def theorem2_target_sign_vector(
    sig_c: Sequence[int],
    layers: Sequence[Sequence[int]],
    alpha: Sequence[int],
) -> List[int]:
    """Exact Theorem 2 sign formula for target chamber b_FL(alpha):
      - q in layer H_j (1-indexed j in 1..r, stored at layers[j-1]): alpha[j-1] * sig_c[q]
      - q outside H(F, P): sig_c[q] unchanged.
    """
    m = len(sig_c)
    out = list(sig_c)
    for j_idx, layer in enumerate(layers):
        a_j = alpha[j_idx]
        for q_idx in layer:
            if not (0 <= q_idx < m):
                raise ValueError(f"Hyperplane index {q_idx} out of range")
            out[q_idx] = a_j * sig_c[q_idx]
    return out


def fig2_line_eval_q(n: int, x: Fraction) -> Fraction:
    """Exact evaluation of Section 2 Figure 2 line l_n(x) = 2^{-(n+1)} * (x - n - 2)."""
    return (x - Fraction(n + 2, 1)) / Fraction(1 << (n + 1), 1)


def fig2_point_q(k: int) -> Tuple[Fraction, Fraction]:
    """Exact Figure 2 boundary vertex p_k = (k, -2^{-k})."""
    return Fraction(k, 1), Fraction(-1, 1 << k)


def lex_lt_vec_q(a: Sequence[Fraction], b: Sequence[Fraction]) -> bool:
    """Exact lexicographic comparison a < b on equal-length rational tuples."""
    if len(a) != len(b):
        raise ValueError(f"Potential length mismatch: {len(a)} vs {len(b)}")
    for x, y in zip(a, b):
        if x < y:
            return True
        if x > y:
            return False
    return False


def rank_exact_q(rows: Sequence[Sequence[Fraction]]) -> int:
    """Exact Gaussian elimination rank over Q (zero floats)."""
    if not rows:
        return 0
    m = len(rows)
    n = len(rows[0])
    mat = [list(r) for r in rows]
    rank = 0
    for col in range(n):
        pivot = -1
        for r in range(rank, m):
            if mat[r][col] != 0:
                pivot = r
                break
        if pivot == -1:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        pv = mat[rank][col]
        for r in range(rank + 1, m):
            if mat[r][col] != 0:
                fac = mat[r][col] / pv
                for c in range(col, n):
                    mat[r][c] -= fac * mat[rank][c]
        rank += 1
        if rank == m:
            break
    return rank


def longest_same_level_paths_dag(
    nodes: Sequence[str],
    edges: Dict[str, List[str]],
    levels: Dict[str, Fraction],
) -> Tuple[bool, Dict[str, int]]:
    """Verify DAG acyclicity via Kahn's algorithm and compute exact longest directed
    walk length staying within the starting level lambda(c, omega) for every node."""
    node_set = set(nodes)
    indeg: Dict[str, int] = {u: 0 for u in nodes}
    for u in nodes:
        for v in edges.get(u, []):
            if v not in node_set:
                raise ValueError(f"Edge target {v!r} not in node set")
            indeg[v] += 1

    queue = [u for u in nodes if indeg[u] == 0]
    topo: List[str] = []
    idx = 0
    while idx < len(queue):
        u = queue[idx]
        idx += 1
        topo.append(u)
        for v in edges.get(u, []):
            indeg[v] -= 1
            if indeg[v] == 0:
                queue.append(v)

    if len(topo) != len(nodes):
        return False, {}

    # DP in reverse topological order: longest same-level walk length from u
    same_len: Dict[str, int] = {u: 0 for u in nodes}
    for u in reversed(topo):
        best = 0
        for v in edges.get(u, []):
            if levels[v] == levels[u]:
                cand = 1 + same_len[v]
                if cand > best:
                    best = cand
        same_len[u] = best
    return True, same_len
