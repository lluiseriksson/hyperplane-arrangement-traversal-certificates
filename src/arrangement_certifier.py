"""Zero-floating-point exact-Q certificate verifier: ARRANGEMENT-TRAVERSAL-CERT-1.0.
Audits all four geometric and algebraic pillars of
Brennan Dury (arXiv:2611.32976, Nov 24, 2026)
"Traversing hyperplane arrangements with an affine objective":
  - Mode 1: flag_sign_targets_theorem2_cert (Prop. 1 face calculus, exact codim rank & Thm. 2 2^r - 1 targets)
  - Mode 2: fig2_quasipolyhedral_counterexample_cert (Sec. 2 Fig. 2 non-attainment & compact hit)
  - Mode 3: frame_strategy_slice_potential_cert (Sec. 6 Lemma 17 full-rank slice update & Prop. 3 potential)
  - Mode 4: acyclic_chamber_dag_escape_cert (Sec. 3.2/6 chamber DAG, strict-complementarity KKT, exact Thm. 2 targets & Thm. 3 escape L)

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import itertools
import re
from fractions import Fraction
from typing import Any, Dict, List, Set, Tuple

from src.arrangement_exact import (
    AffFormQ,
    VecQ,
    dot_q,
    fig2_line_eval_q,
    fig2_point_q,
    format_rat,
    lex_lt_vec_q,
    longest_same_level_paths_dag,
    rank_exact_q,
    sign_closure_contains,
    sign_vector_q,
    theorem2_target_sign_vector,
)

SCHEMA_VERSION = "ARRANGEMENT-TRAVERSAL-CERT-1.0"
_CANON_INT_RE = re.compile(r"^(0|-?[1-9][0-9]*)$")
_CANON_FRAC_RE = re.compile(r"^-?[1-9][0-9]*/[1-9][0-9]*$")
MAX_RAT_STR_LEN = 1024
MAX_INT_BITS = 2048
MAX_ID_LEN = 128


class ArrangementCertificateError(ValueError):
    """Raised whenever an ARRANGEMENT-TRAVERSAL-CERT-1.0 certificate fails any invariant."""


def _assert_strict_json_types(obj: Any, path: str = "$") -> None:
    t = type(obj)
    if t is int:
        if obj.bit_length() > MAX_INT_BITS:
            raise ArrangementCertificateError(f"Integer bit-length > {MAX_INT_BITS} at {path}")
        return
    if t is str or t is bool:
        return
    if t is list:
        for i, v in enumerate(obj):
            _assert_strict_json_types(v, f"{path}[{i}]")
        return
    if t is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise ArrangementCertificateError(f"Non-string dict key at {path}")
            _assert_strict_json_types(v, f"{path}.{k}")
        return
    raise ArrangementCertificateError(f"Forbidden JSON type {t.__name__} at {path}")


def _parse_int(val: Any, name: str) -> int:
    if type(val) is not int:
        raise ArrangementCertificateError(f"{name} must be strict int, got {type(val).__name__}")
    if val.bit_length() > MAX_INT_BITS:
        raise ArrangementCertificateError(f"{name} integer too large")
    return val


def _parse_rat(val: Any, name: str) -> Fraction:
    if type(val) is int:
        if val.bit_length() > MAX_INT_BITS:
            raise ArrangementCertificateError(f"{name} integer too large")
        return Fraction(val, 1)
    if type(val) is str:
        if len(val) > MAX_RAT_STR_LEN:
            raise ArrangementCertificateError(f"{name} rational string too long")
        if _CANON_INT_RE.match(val):
            iv = int(val)
            if iv.bit_length() > MAX_INT_BITS:
                raise ArrangementCertificateError(f"{name} integer bit-length > {MAX_INT_BITS}")
            return Fraction(iv, 1)
        if _CANON_FRAC_RE.match(val):
            num_s, den_s = val.split("/")
            num, den = int(num_s), int(den_s)
            if num.bit_length() > MAX_INT_BITS or den.bit_length() > MAX_INT_BITS:
                raise ArrangementCertificateError(f"{name} rational bit-length > {MAX_INT_BITS}")
            if den < 2:
                raise ArrangementCertificateError(f"{name} denominator must be >= 2: {val!r}")
            q = Fraction(num, den)
            if q.numerator != num or q.denominator != den:
                raise ArrangementCertificateError(f"{name} unreduced fraction: {val!r}")
            return q
        raise ArrangementCertificateError(f"{name} non-canonical rational string: {val!r}")
    raise ArrangementCertificateError(f"{name} invalid type {type(val).__name__}")


def _parse_exact_keys(cert: Dict[str, Any], req: Set[str], mode: str) -> None:
    keys = set(cert.keys())
    if keys != req:
        raise ArrangementCertificateError(f"{mode} key mismatch: {sorted(keys ^ req)}")


def _parse_vec(raw: Any, dim: int, name: str) -> VecQ:
    if type(raw) is not list or len(raw) != dim:
        raise ArrangementCertificateError(f"{name} must have length {dim}")
    return [_parse_rat(raw[j], f"{name}[{j}]") for j in range(dim)]


def _parse_forms(raw: Any, dim: int) -> List[AffFormQ]:
    if type(raw) is not list or not (1 <= len(raw) <= 32):
        raise ArrangementCertificateError("hyperplanes must be non-empty list of length <= 32")
    forms: List[AffFormQ] = []
    for k, item in enumerate(raw):
        if type(item) is not dict or set(item.keys()) != {"normal", "offset"}:
            raise ArrangementCertificateError(f"hyperplanes[{k}] schema mismatch")
        a = _parse_vec(item["normal"], dim, f"hyperplanes[{k}].normal")
        if all(c == 0 for c in a):
            raise ArrangementCertificateError(f"hyperplanes[{k}] has zero normal vector")
        b = _parse_rat(item["offset"], f"hyperplanes[{k}].offset")
        forms.append((a, b))
    return forms


def _parse_sign_vec(raw: Any, m: int, name: str) -> List[int]:
    if type(raw) is not list or len(raw) != m:
        raise ArrangementCertificateError(f"{name} must have length {m}")
    out = []
    for j, v in enumerate(raw):
        iv = _parse_int(v, f"{name}[{j}]")
        if iv not in (-1, 0, 1):
            raise ArrangementCertificateError(f"{name}[{j}] must be in {{-1,0,1}}")
        out.append(iv)
    return out


# =============================================================================
# Mode 1: Proposition 1 Face Calculus, Exact Codimension Rank & Theorem 2 Targets
# =============================================================================


def _verify_mode1_flag_targets(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "dim",
        "codim_r",
        "hyperplanes",
        "flag_witness_points",
        "layer_hyperplanes",
        "target_witness_points",
        "claimed_source_signs",
        "claimed_base_signs",
        "claimed_target_count",
    }
    _parse_exact_keys(cert, req, "Mode 1")
    d = _parse_int(cert["dim"], "dim")
    r = _parse_int(cert["codim_r"], "codim_r")
    if not (1 <= d <= 6 and 1 <= r <= d and r <= 4):
        raise ArrangementCertificateError("Require 1 <= r <= dim <= 6 and r <= 4")
    forms = _parse_forms(cert["hyperplanes"], d)
    m = len(forms)

    raw_fw = cert["flag_witness_points"]
    if type(raw_fw) is not list or len(raw_fw) != r + 1:
        raise ArrangementCertificateError(f"flag_witness_points must have length r+1={r+1}")
    flag_pts = [_parse_vec(raw_fw[i], d, f"flag_witness_points[{i}]") for i in range(r + 1)]
    flag_sigs = [sign_vector_q(forms, pt) for pt in flag_pts]

    sig_c = flag_sigs[0]
    if any(s == 0 for s in sig_c):
        raise ArrangementCertificateError("flag_witness_points[0] is not in an open chamber (zero sign)")

    zero_sets: List[Set[int]] = []
    for i in range(r + 1):
        zs = {k for k, s in enumerate(flag_sigs[i]) if s == 0}
        # Exact codimension check: codim(F_i) == rank({a_k : k in H(F_i, P)}) == i!
        rk_i = rank_exact_q([forms[k][0] for k in sorted(zs)])
        if rk_i != i:
            raise ArrangementCertificateError(f"Flag level {i} has exact codimension rank {rk_i} != {i}")
        zero_sets.append(zs)

    for i in range(1, r + 1):
        if not sign_closure_contains(flag_sigs[i], flag_sigs[i - 1]):
            raise ArrangementCertificateError(f"Flag closure F_{i} subseteq cl(F_{i-1}) violated")
        if not (zero_sets[i - 1] < zero_sets[i]):
            raise ArrangementCertificateError(f"Zero-hyperplane set failed strict growth at level {i}")

    raw_layers = cert["layer_hyperplanes"]
    if type(raw_layers) is not list or len(raw_layers) != r:
        raise ArrangementCertificateError(f"layer_hyperplanes must have length r={r}")
    layers: List[List[int]] = []
    for i in range(r):
        if type(raw_layers[i]) is not list or not raw_layers[i]:
            raise ArrangementCertificateError(f"layer_hyperplanes[{i}] must be non-empty")
        lay = sorted(_parse_int(v, f"layer[{i}]") for v in raw_layers[i])
        if len(set(lay)) != len(lay):
            raise ArrangementCertificateError(f"Duplicate index in layer_hyperplanes[{i}]")
        exp_lay = sorted(zero_sets[i + 1] - zero_sets[i])
        if lay != exp_lay:
            raise ArrangementCertificateError(f"layer_hyperplanes[{i}] mismatch: got {lay}, exact {exp_lay}")
        layers.append(lay)

    raw_tw = cert["target_witness_points"]
    if type(raw_tw) is not dict:
        raise ArrangementCertificateError("target_witness_points must be dict keyed by alpha strings")
    expected_alphas = [a for a in itertools.product((1, -1), repeat=r) if any(v == -1 for v in a)]
    if len(raw_tw) != len(expected_alphas):
        raise ArrangementCertificateError(f"Expected {len(expected_alphas)} targets, got {len(raw_tw)}")

    seen_sigs: Set[Tuple[int, ...]] = {tuple(sig_c)}
    sig_base = flag_sigs[r]
    for alpha in expected_alphas:
        key = ",".join("+1" if v == 1 else "-1" for v in alpha)
        if key not in raw_tw:
            raise ArrangementCertificateError(f"Missing target witness for alpha={key}")
        pt = _parse_vec(raw_tw[key], d, f"target[{key}]")
        actual_sig = sign_vector_q(forms, pt)
        exp_sig = theorem2_target_sign_vector(sig_c, layers, alpha)
        if actual_sig != exp_sig:
            raise ArrangementCertificateError(f"Target witness {key} sign mismatch: got {actual_sig}, exp {exp_sig}")
        if not sign_closure_contains(sig_base, actual_sig):
            raise ArrangementCertificateError(f"Base face F not contained in target {key} closure")
        t_sig = tuple(actual_sig)
        if t_sig in seen_sigs:
            raise ArrangementCertificateError(f"Duplicate target chamber sign vector at {key}")
        seen_sigs.add(t_sig)

    if _parse_sign_vec(cert["claimed_source_signs"], m, "claimed_source_signs") != sig_c:
        raise ArrangementCertificateError("claimed_source_signs mismatch")
    if _parse_sign_vec(cert["claimed_base_signs"], m, "claimed_base_signs") != sig_base:
        raise ArrangementCertificateError("claimed_base_signs mismatch")
    if _parse_int(cert["claimed_target_count"], "claimed_target_count") != len(expected_alphas):
        raise ArrangementCertificateError("claimed_target_count mismatch")

    return {
        "verified": True,
        "mode": cert["mode"],
        "dim": d,
        "codim_r": r,
        "target_count": len(expected_alphas),
    }


# =============================================================================
# Mode 2: Section 2 Figure 2 Quasipolyhedral Non-Attainment Counterexample
# =============================================================================


def _verify_mode2_fig2_counterexample(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "max_index_N",
        "claimed_boundary_points",
        "claimed_origin_intercepts",
        "claimed_max_y_value",
        "claimed_sup_gap",
    }
    _parse_exact_keys(cert, req, "Mode 2")
    N = _parse_int(cert["max_index_N"], "max_index_N")
    if not (2 <= N <= 24):
        raise ArrangementCertificateError("Require 2 <= max_index_N <= 24")

    pts: List[Tuple[Fraction, Fraction]] = []
    for k in range(N + 1):
        pk = fig2_point_q(k)
        if fig2_line_eval_q(k, pk[0]) != pk[1]:
            raise ArrangementCertificateError(f"p_{k} does not lie on H_{k}")
        if k >= 1 and fig2_line_eval_q(k - 1, pk[0]) != pk[1]:
            raise ArrangementCertificateError(f"p_{k} does not lie on H_{k-1}")
        for n in range(N + 1):
            if pk[1] > fig2_line_eval_q(n, pk[0]):
                raise ArrangementCertificateError(f"Feasibility y(p_{k}) <= l_{n}(x(p_{k})) violated")
        pts.append(pk)

    intercepts: List[Fraction] = []
    for n in range(N + 1):
        y0 = fig2_line_eval_q(n, Fraction(0, 1))
        if not (Fraction(-1, 1) <= y0 < Fraction(0, 1)):
            raise ArrangementCertificateError(f"Origin intercept y0(H_{n})={y0} outside [-1, 0)")
        intercepts.append(y0)

    max_y = pts[-1][1]
    sup_gap = Fraction(0, 1) - max_y

    raw_pts = cert["claimed_boundary_points"]
    if type(raw_pts) is not list or len(raw_pts) != N + 1:
        raise ArrangementCertificateError("claimed_boundary_points length mismatch")
    for k in range(N + 1):
        if type(raw_pts[k]) is not list or len(raw_pts[k]) != 2:
            raise ArrangementCertificateError(f"claimed_boundary_points[{k}] invalid")
        if (_parse_rat(raw_pts[k][0], "x"), _parse_rat(raw_pts[k][1], "y")) != pts[k]:
            raise ArrangementCertificateError(f"claimed_boundary_points[{k}] mismatch")

    raw_int = cert["claimed_origin_intercepts"]
    if type(raw_int) is not list or len(raw_int) != N + 1:
        raise ArrangementCertificateError("claimed_origin_intercepts length mismatch")
    if [_parse_rat(raw_int[n], f"intercept[{n}]") for n in range(N + 1)] != intercepts:
        raise ArrangementCertificateError("claimed_origin_intercepts mismatch")

    if _parse_rat(cert["claimed_max_y_value"], "claimed_max_y_value") != max_y:
        raise ArrangementCertificateError("claimed_max_y_value mismatch")
    if _parse_rat(cert["claimed_sup_gap"], "claimed_sup_gap") != sup_gap:
        raise ArrangementCertificateError("claimed_sup_gap mismatch")

    return {
        "verified": True,
        "mode": cert["mode"],
        "max_index_N": N,
        "max_y": format_rat(max_y),
        "sup_gap": format_rat(sup_gap),
    }


# =============================================================================
# Mode 3: Section 6 Frame Strategy Full-Rank Slice Update (Lemma 17) & Potential
# =============================================================================


def _verify_mode3_frame_slice(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "dim",
        "eta_covector",
        "phi_covector",
        "source_rays",
        "target_rays",
        "source_lambda",
        "target_lambda",
        "source_opt_dim",
        "target_opt_dim",
        "claimed_source_slice_vertices",
        "claimed_source_max_phi",
        "claimed_source_argmax_idx",
        "claimed_next_eta_values",
        "claimed_target_max_phi",
        "claimed_potential_strict_increase",
    }
    _parse_exact_keys(cert, req, "Mode 3")
    d = _parse_int(cert["dim"], "dim")
    if not (2 <= d <= 6):
        raise ArrangementCertificateError("Require 2 <= dim <= 6")
    eta = _parse_vec(cert["eta_covector"], d, "eta_covector")
    phi = _parse_vec(cert["phi_covector"], d, "phi_covector")
    if all(v == 0 for v in eta) or all(v == 0 for v in phi):
        raise ArrangementCertificateError("Covectors eta and phi must be nonzero")

    raw_sr = cert["source_rays"]
    raw_tr = cert["target_rays"]
    if type(raw_sr) is not list or not (d <= len(raw_sr) <= 12):
        raise ArrangementCertificateError(f"source_rays must have length in [{d}, 12]")
    if type(raw_tr) is not list or not (d <= len(raw_tr) <= 12):
        raise ArrangementCertificateError(f"target_rays must have length in [{d}, 12]")
    src_rays = [_parse_vec(r, d, f"source_rays[{i}]") for i, r in enumerate(raw_sr)]
    tgt_rays = [_parse_vec(r, d, f"target_rays[{i}]") for i, r in enumerate(raw_tr)]

    # Full-dimensional chamber tangent cones require full rank d!
    if rank_exact_q(src_rays) != d:
        raise ArrangementCertificateError(f"source_rays does not have full rank {d}")
    if rank_exact_q(tgt_rays) != d:
        raise ArrangementCertificateError(f"target_rays does not have full rank {d}")

    src_verts: List[VecQ] = []
    src_phis: List[Fraction] = []
    for k, xi in enumerate(src_rays):
        ev = dot_q(eta, xi)
        if ev >= 0:
            raise ArrangementCertificateError(f"source_rays[{k}] violates eta(xi) < 0 (got {ev})")
        v = [c / (-ev) for c in xi]
        if dot_q(eta, v) != Fraction(-1, 1):
            raise ArrangementCertificateError("Slice normalization failed")
        src_verts.append(v)
        src_phis.append(dot_q(phi, v))

    src_vert_set = {tuple(v) for v in src_verts}
    if len(src_vert_set) != len(src_verts):
        raise ArrangementCertificateError("Duplicate or proportional rays in source_rays")

    src_max = max(src_phis)
    max_indices = [k for k, pv in enumerate(src_phis) if pv == src_max]
    if len(max_indices) != 1:
        raise ArrangementCertificateError("Frame covector phi is not admissible (tied maximizers on source slice)")
    p_idx = max_indices[0]
    p_vert = src_verts[p_idx]

    next_eta_vals: List[Fraction] = []
    for k, q_vert in enumerate(src_verts):
        if k == p_idx:
            continue
        diff = [q_vert[j] - p_vert[j] for j in range(d)]
        if dot_q(eta, diff) != Fraction(0, 1):
            raise ArrangementCertificateError("Slice edge q - p not in ker(eta)")
        val = dot_q(phi, diff)
        if val != src_phis[k] - src_max or val >= 0:
            raise ArrangementCertificateError(f"Lemma 17 negativity failed at vertex {k}: {val}")
        next_eta_vals.append(val)

    tgt_verts: List[VecQ] = []
    tgt_phis: List[Fraction] = []
    for k, xi in enumerate(tgt_rays):
        ev = dot_q(eta, xi)
        if ev >= 0:
            raise ArrangementCertificateError(f"target_rays[{k}] violates eta(xi) < 0 (got {ev})")
        v = [c / (-ev) for c in xi]
        tgt_verts.append(v)
        tgt_phis.append(dot_q(phi, v))
    tgt_vert_set = {tuple(v) for v in tgt_verts}
    if len(tgt_vert_set) != len(tgt_verts):
        raise ArrangementCertificateError("Duplicate or proportional rays in target_rays")
    if tgt_vert_set == src_vert_set:
        raise ArrangementCertificateError("Target cone slice is identical to source cone slice")
    tgt_max = max(tgt_phis)
    if sum(1 for pv in tgt_phis if pv == tgt_max) != 1:
        raise ArrangementCertificateError("Frame covector phi is not admissible on target slice")

    lam_s = _parse_rat(cert["source_lambda"], "source_lambda")
    lam_t = _parse_rat(cert["target_lambda"], "target_lambda")
    dim_s = _parse_int(cert["source_opt_dim"], "source_opt_dim")
    dim_t = _parse_int(cert["target_opt_dim"], "target_opt_dim")
    if not (0 <= dim_s < d) or not (0 <= dim_t < d):
        raise ArrangementCertificateError(f"Optimal face dimensions ({dim_s}, {dim_t}) out of [0, {d - 1}]")
    if lam_t < lam_s:
        raise ArrangementCertificateError("Lemma 4 violated: target_lambda < source_lambda")
    if lam_t == lam_s and dim_t < dim_s:
        raise ArrangementCertificateError("Optimal face dimension cannot decrease at equal lambda")

    pot_s = [lam_s, Fraction(dim_s, 1), src_max]
    pot_t = [lam_t, Fraction(dim_t, 1), tgt_max]
    if not lex_lt_vec_q(pot_s, pot_t):
        raise ArrangementCertificateError(f"Proposition 3 violated: potential did not strictly increase ({pot_s} vs {pot_t})")

    raw_sv = cert["claimed_source_slice_vertices"]
    if type(raw_sv) is not list or len(raw_sv) != len(src_verts):
        raise ArrangementCertificateError("claimed_source_slice_vertices length mismatch")
    for k in range(len(src_verts)):
        if _parse_vec(raw_sv[k], d, f"claimed_vert[{k}]") != src_verts[k]:
            raise ArrangementCertificateError(f"claimed_source_slice_vertices[{k}] mismatch")
    if _parse_rat(cert["claimed_source_max_phi"], "claimed_source_max_phi") != src_max:
        raise ArrangementCertificateError("claimed_source_max_phi mismatch")
    if _parse_int(cert["claimed_source_argmax_idx"], "claimed_source_argmax_idx") != p_idx:
        raise ArrangementCertificateError("claimed_source_argmax_idx mismatch")
    raw_ne = cert["claimed_next_eta_values"]
    if type(raw_ne) is not list or [_parse_rat(x, "next_eta") for x in raw_ne] != next_eta_vals:
        raise ArrangementCertificateError("claimed_next_eta_values mismatch")
    if _parse_rat(cert["claimed_target_max_phi"], "claimed_target_max_phi") != tgt_max:
        raise ArrangementCertificateError("claimed_target_max_phi mismatch")
    if cert["claimed_potential_strict_increase"] is not True:
        raise ArrangementCertificateError("claimed_potential_strict_increase must be true")

    return {
        "verified": True,
        "mode": cert["mode"],
        "source_max_phi": format_rat(src_max),
        "target_max_phi": format_rat(tgt_max),
        "argmax_idx": p_idx,
    }


# =============================================================================
# Mode 4: Complete Acyclic Chamber DAG, Strict-Complementarity KKT & Exact Thm. 2 Targets
# =============================================================================


def _verify_mode4_chamber_dag(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "dim",
        "objective_c",
        "hyperplanes",
        "chambers",
        "claimed_is_acyclic",
        "claimed_max_same_level_walk",
        "claimed_uniform_escape_L",
    }
    _parse_exact_keys(cert, req, "Mode 4")
    d = _parse_int(cert["dim"], "dim")
    if not (1 <= d <= 4):
        raise ArrangementCertificateError("Require 1 <= dim <= 4")
    obj_c = _parse_vec(cert["objective_c"], d, "objective_c")
    if all(v == 0 for v in obj_c):
        raise ArrangementCertificateError("objective_c must be nonconstant")
    forms = _parse_forms(cert["hyperplanes"], d)
    m = len(forms)

    raw_ch = cert["chambers"]
    if type(raw_ch) is not list or not (2 <= len(raw_ch) <= 32):
        raise ArrangementCertificateError("chambers must have length in [2, 32]")

    ch_req = {
        "id",
        "interior_point",
        "is_bounded",
        "optimal_point",
        "dual_multipliers",
        "flag_layers",
        "optimal_value",
        "potential",
        "outgoing_targets",
    }
    ch_ids: List[str] = []
    ch_sigs: Dict[str, List[int]] = {}
    sig_to_id: Dict[Tuple[int, ...], str] = {}
    ch_bounded: Dict[str, bool] = {}
    ch_opt_sig: Dict[str, List[int]] = {}
    ch_opt_dim: Dict[str, int] = {}
    ch_flag_layers: Dict[str, List[List[int]]] = {}
    ch_lam: Dict[str, Fraction] = {}
    ch_pot: Dict[str, List[Fraction]] = {}
    ch_edges: Dict[str, List[str]] = {}

    for idx, ch in enumerate(raw_ch):
        if type(ch) is not dict or set(ch.keys()) != ch_req:
            raise ArrangementCertificateError(f"chambers[{idx}] schema mismatch")
        cid = ch["id"]
        if type(cid) is not str or not (1 <= len(cid) <= 64) or cid in ch_sigs:
            raise ArrangementCertificateError(f"Duplicate or invalid chamber id {cid!r}")
        ch_ids.append(cid)
        ipt = _parse_vec(ch["interior_point"], d, f"{cid}.interior_point")
        sig = sign_vector_q(forms, ipt)
        if any(s == 0 for s in sig):
            raise ArrangementCertificateError(f"Chamber {cid} interior_point lies on a hyperplane")
        t_sig = tuple(sig)
        if t_sig in sig_to_id:
            raise ArrangementCertificateError(f"Duplicate chamber sign vector at {cid}")
        sig_to_id[t_sig] = cid
        ch_sigs[cid] = sig

        is_b = ch["is_bounded"]
        if type(is_b) is not bool:
            raise ArrangementCertificateError(f"{cid}.is_bounded must be bool")
        ch_bounded[cid] = is_b

        raw_out = ch["outgoing_targets"]
        if type(raw_out) is not list or any(type(t) is not str for t in raw_out):
            raise ArrangementCertificateError(f"{cid}.outgoing_targets must be list of strings")
        if len(set(raw_out)) != len(raw_out):
            raise ArrangementCertificateError(f"{cid}.outgoing_targets has duplicates")
        ch_edges[cid] = list(raw_out)

        if is_b:
            x_star = _parse_vec(ch["optimal_point"], d, f"{cid}.optimal_point")
            opt_sig = sign_vector_q(forms, x_star)
            if not sign_closure_contains(opt_sig, sig):
                raise ArrangementCertificateError(f"{cid}.optimal_point is not in chamber closure")
            raw_y = ch["dual_multipliers"]
            if type(raw_y) is not list or len(raw_y) != m:
                raise ArrangementCertificateError(f"{cid}.dual_multipliers must have length {m}")
            ys = [_parse_rat(raw_y[k], f"{cid}.y[{k}]") for k in range(m)]
            if any(y < 0 for y in ys):
                raise ArrangementCertificateError(f"{cid} has negative dual multiplier")
            # STRICT COMPLEMENTARITY: y_k > 0 iff opt_sig[k] == 0!
            # Proves EVERY optimal point x in F(c) vanishes on all k with opt_sig[k] == 0,
            # hence x_star in relint(F(c)) and opt_sig == sign_{F(c)} EXACTLY!
            for k in range(m):
                if opt_sig[k] == 0 and ys[k] <= 0:
                    raise ArrangementCertificateError(
                        f"{cid} fails strict complementarity on active hyperplane {k} (boundary x* rejected)"
                    )
                if opt_sig[k] != 0 and ys[k] != 0:
                    raise ArrangementCertificateError(
                        f"{cid} violates complementary slackness on inactive hyperplane {k}"
                    )
            for j in range(d):
                kkt_j = obj_c[j] + sum((ys[k] * Fraction(sig[k], 1) * forms[k][0][j] for k in range(m)), Fraction(0, 1))
                if kkt_j != Fraction(0, 1):
                    raise ArrangementCertificateError(f"{cid} fails LP dual KKT stationarity in coord {j}: {kkt_j}")

            active_set = {k for k in range(m) if opt_sig[k] == 0}
            codim_r = rank_exact_q([forms[k][0] for k in sorted(active_set)])
            if not (1 <= codim_r <= d):
                raise ArrangementCertificateError(f"{cid} optimal face has invalid codimension {codim_r}")
            opt_dim = d - codim_r
            ch_opt_sig[cid] = opt_sig
            ch_opt_dim[cid] = opt_dim

            # Validate flag_layers partitioning active_set into codim_r nonempty layers with cumulative rank i!
            raw_fl = ch["flag_layers"]
            if type(raw_fl) is not list or len(raw_fl) != codim_r:
                raise ArrangementCertificateError(f"{cid}.flag_layers must have length codim_r={codim_r}")
            layers: List[List[int]] = []
            seen_fl: Set[int] = set()
            for li, lay_raw in enumerate(raw_fl):
                if type(lay_raw) is not list or not lay_raw:
                    raise ArrangementCertificateError(f"{cid}.flag_layers[{li}] must be non-empty")
                lay = sorted(_parse_int(v, f"{cid}.flag_layers[{li}]") for v in lay_raw)
                if len(set(lay)) != len(lay) or any(k not in active_set or k in seen_fl for k in lay):
                    raise ArrangementCertificateError(f"{cid}.flag_layers[{li}] invalid partition of H(F(c))")
                seen_fl.update(lay)
                if rank_exact_q([forms[k][0] for k in sorted(seen_fl)]) != li + 1:
                    raise ArrangementCertificateError(f"{cid}.flag_layers cumulative rank != {li + 1}")
                layers.append(lay)
            if seen_fl != active_set:
                raise ArrangementCertificateError(f"{cid}.flag_layers does not cover all of H(F(c))")
            ch_flag_layers[cid] = layers

            exact_lam = dot_q(obj_c, x_star)
            if _parse_rat(ch["optimal_value"], f"{cid}.optimal_value") != exact_lam:
                raise ArrangementCertificateError(f"{cid}.optimal_value mismatch: exact={exact_lam}")
            ch_lam[cid] = exact_lam

            raw_p = ch["potential"]
            if type(raw_p) is not list or len(raw_p) != 3:
                raise ArrangementCertificateError(f"{cid}.potential must be 3-tuple [lambda, dim_F, tie_score]")
            pot = [_parse_rat(v, f"{cid}.potential") for v in raw_p]
            if pot[0] != exact_lam:
                raise ArrangementCertificateError(f"{cid}.potential[0] must equal optimal_value")
            if pot[1] != Fraction(opt_dim, 1):
                raise ArrangementCertificateError(f"{cid}.potential[1] must equal exact dim(F(c))={opt_dim}")
            ch_pot[cid] = pot
        else:
            # Unbounded chamber: enforce strict canonical zero/empty fields (no unchecked garbage!)
            if raw_out:
                raise ArrangementCertificateError(f"Unbounded chamber {cid} must have no outgoing targets")
            if ch["dual_multipliers"] != ["0"] * m:
                raise ArrangementCertificateError(f"Unbounded chamber {cid} dual_multipliers must be all '0'")
            if ch["flag_layers"] != []:
                raise ArrangementCertificateError(f"Unbounded chamber {cid} flag_layers must be []")
            if ch["potential"] != ["INF"]:
                raise ArrangementCertificateError(f"Unbounded chamber {cid} potential must be ['INF']")
            ray = _parse_vec(ch["optimal_point"], d, f"{cid}.recession_ray")
            for k in range(m):
                if Fraction(sig[k], 1) * dot_q(forms[k][0], ray) < Fraction(0, 1):
                    raise ArrangementCertificateError(f"Unbounded chamber {cid} recession ray leaves chamber on hyperplane {k}")
            if dot_q(obj_c, ray) <= Fraction(0, 1):
                raise ArrangementCertificateError(f"Unbounded chamber {cid} recession ray does not increase objective")
            if ch["optimal_value"] != "INF":
                raise ArrangementCertificateError(f"Unbounded chamber {cid} optimal_value must be 'INF'")

    # Verify EVERY bounded chamber's outgoing_targets equals the EXACT set of 2^r - 1 Theorem 2 targets!
    for cid in ch_ids:
        if not ch_bounded[cid]:
            continue
        layers = ch_flag_layers[cid]
        r = len(layers)
        sig_c = ch_sigs[cid]
        opt_sig = ch_opt_sig[cid]
        expected_target_ids: Set[str] = set()
        for alpha in itertools.product((1, -1), repeat=r):
            if all(v == 1 for v in alpha):
                continue
            t_sig = tuple(theorem2_target_sign_vector(sig_c, layers, alpha))
            if t_sig not in sig_to_id:
                raise ArrangementCertificateError(
                    f"Chamber {cid} Theorem 2 target sign {list(t_sig)} missing from chamber set"
                )
            expected_target_ids.add(sig_to_id[t_sig])
        if len(expected_target_ids) != (1 << r) - 1:
            raise ArrangementCertificateError(f"Chamber {cid} failed 2^r - 1 distinct targets")
        if set(ch_edges[cid]) != expected_target_ids:
            raise ArrangementCertificateError(
                f"Chamber {cid} outgoing_targets mismatch with exact Theorem 2 targets: "
                f"got {sorted(ch_edges[cid])}, exp {sorted(expected_target_ids)}"
            )
        for tid in ch_edges[cid]:
            # True optimal face F(c) subseteq cl(b) (certified because opt_sig == sign_{F(c)}!)
            if not sign_closure_contains(opt_sig, ch_sigs[tid]):
                raise ArrangementCertificateError(f"Edge {cid}->{tid} violates F(c) subseteq cl(b)")
            if ch_bounded[tid]:
                if ch_lam[tid] < ch_lam[cid]:
                    raise ArrangementCertificateError(f"Edge {cid}->{tid} decreases optimal value")
                if ch_lam[tid] == ch_lam[cid] and ch_opt_dim[tid] < ch_opt_dim[cid]:
                    raise ArrangementCertificateError(f"Edge {cid}->{tid} decreases dim(F) at equal lambda")
                if not lex_lt_vec_q(ch_pot[cid], ch_pot[tid]):
                    raise ArrangementCertificateError(f"Edge {cid}->{tid} fails strict potential increase")

    bounded_ids = [cid for cid in ch_ids if ch_bounded[cid]]
    if not bounded_ids:
        raise ArrangementCertificateError("Chamber DAG must contain at least one bounded chamber")
    inf_sentinel = max(ch_lam.values()) + Fraction(1, 1)
    levels = {cid: (ch_lam[cid] if ch_bounded[cid] else inf_sentinel) for cid in ch_ids}
    is_dag, same_lens = longest_same_level_paths_dag(ch_ids, ch_edges, levels)
    if not is_dag:
        raise ArrangementCertificateError("Chamber digraph contains a directed cycle")
    max_same = max(same_lens[cid] for cid in bounded_ids)
    escape_L = max_same + 1

    if cert["claimed_is_acyclic"] is not True:
        raise ArrangementCertificateError("claimed_is_acyclic must be true")
    if _parse_int(cert["claimed_max_same_level_walk"], "claimed_max_same_level_walk") != max_same:
        raise ArrangementCertificateError(f"claimed_max_same_level_walk mismatch: exact={max_same}")
    if _parse_int(cert["claimed_uniform_escape_L"], "claimed_uniform_escape_L") != escape_L:
        raise ArrangementCertificateError(f"claimed_uniform_escape_L mismatch: exact={escape_L}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "num_chambers": len(ch_ids),
        "num_bounded": len(bounded_ids),
        "max_same_level_walk": max_same,
        "uniform_escape_L": escape_L,
    }


def verify_arrangement_certificate_exact(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Top-level zero-float entry point for ARRANGEMENT-TRAVERSAL-CERT-1.0."""
    if type(cert) is not dict:
        raise ArrangementCertificateError("Certificate root must be a JSON object")
    _assert_strict_json_types(cert)
    if cert.get("schema") != SCHEMA_VERSION:
        raise ArrangementCertificateError(f"Unsupported schema: {cert.get('schema')!r}")
    cid = cert.get("cert_id")
    if type(cid) is not str or not (1 <= len(cid) <= MAX_ID_LEN):
        raise ArrangementCertificateError(f"cert_id must be string of length in [1, {MAX_ID_LEN}]")
    mode = cert.get("mode")
    if mode == "flag_sign_targets_theorem2_cert":
        return _verify_mode1_flag_targets(cert)
    if mode == "fig2_quasipolyhedral_counterexample_cert":
        return _verify_mode2_fig2_counterexample(cert)
    if mode == "frame_strategy_slice_potential_cert":
        return _verify_mode3_frame_slice(cert)
    if mode == "acyclic_chamber_dag_escape_cert":
        return _verify_mode4_chamber_dag(cert)
    raise ArrangementCertificateError(f"Unknown verification mode: {mode!r}")
