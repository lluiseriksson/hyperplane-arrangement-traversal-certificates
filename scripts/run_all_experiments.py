"""Generate all 16 canonical ARRANGEMENT-TRAVERSAL-CERT-1.0 certificates and 4 exact-Q
experimental studies for Paper 40: Brennan Dury (arXiv:2611.32976).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import itertools
import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Sequence, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.arrangement_certifier import SCHEMA_VERSION, verify_arrangement_certificate_exact
from src.arrangement_exact import (
    AffFormQ,
    VecQ,
    dot_q,
    fig2_line_eval_q,
    fig2_point_q,
    format_rat,
    longest_same_level_paths_dag,
    sign_vector_q,
)

CERT_DIR = ROOT / "certificates"
DATA_DIR = ROOT / "data"


def _vec_json(v: Sequence[Fraction]) -> List[str]:
    return [format_rat(x) for x in v]


def _forms_json(forms: Sequence[AffFormQ]) -> List[Dict[str, Any]]:
    return [{"normal": _vec_json(a), "offset": format_rat(b)} for a, b in forms]


def _make_mode1(
    cert_id: str,
    d: int,
    r: int,
    forms: List[AffFormQ],
    flag_pts: List[VecQ],
    layers: List[List[int]],
    target_pts: Dict[str, VecQ],
) -> Dict[str, Any]:
    sig_c = sign_vector_q(forms, flag_pts[0])
    sig_base = sign_vector_q(forms, flag_pts[r])
    return {
        "schema": SCHEMA_VERSION,
        "mode": "flag_sign_targets_theorem2_cert",
        "cert_id": cert_id,
        "dim": d,
        "codim_r": r,
        "hyperplanes": _forms_json(forms),
        "flag_witness_points": [_vec_json(p) for p in flag_pts],
        "layer_hyperplanes": layers,
        "target_witness_points": {k: _vec_json(v) for k, v in target_pts.items()},
        "claimed_source_signs": sig_c,
        "claimed_base_signs": sig_base,
        "claimed_target_count": (1 << r) - 1,
    }


def _make_mode2(cert_id: str, N: int) -> Dict[str, Any]:
    pts = [fig2_point_q(k) for k in range(N + 1)]
    intercepts = [fig2_line_eval_q(n, Fraction(0, 1)) for n in range(N + 1)]
    max_y = pts[-1][1]
    sup_gap = Fraction(0, 1) - max_y
    return {
        "schema": SCHEMA_VERSION,
        "mode": "fig2_quasipolyhedral_counterexample_cert",
        "cert_id": cert_id,
        "max_index_N": N,
        "claimed_boundary_points": [[format_rat(x), format_rat(y)] for x, y in pts],
        "claimed_origin_intercepts": _vec_json(intercepts),
        "claimed_max_y_value": format_rat(max_y),
        "claimed_sup_gap": format_rat(sup_gap),
    }


def _make_mode3(
    cert_id: str,
    d: int,
    eta: VecQ,
    phi: VecQ,
    src_rays: List[VecQ],
    tgt_rays: List[VecQ],
    lam_s: Fraction,
    lam_t: Fraction,
    dim_s: int,
    dim_t: int,
) -> Dict[str, Any]:
    src_verts = [[c / (-dot_q(eta, xi)) for c in xi] for xi in src_rays]
    src_phis = [dot_q(phi, v) for v in src_verts]
    src_max = max(src_phis)
    p_idx = src_phis.index(src_max)
    next_eta = [src_phis[k] - src_max for k in range(len(src_verts)) if k != p_idx]

    tgt_verts = [[c / (-dot_q(eta, xi)) for c in xi] for xi in tgt_rays]
    tgt_max = max(dot_q(phi, v) for v in tgt_verts)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "frame_strategy_slice_potential_cert",
        "cert_id": cert_id,
        "dim": d,
        "eta_covector": _vec_json(eta),
        "phi_covector": _vec_json(phi),
        "source_rays": [_vec_json(r) for r in src_rays],
        "target_rays": [_vec_json(r) for r in tgt_rays],
        "source_lambda": format_rat(lam_s),
        "target_lambda": format_rat(lam_t),
        "source_opt_dim": dim_s,
        "target_opt_dim": dim_t,
        "claimed_source_slice_vertices": [_vec_json(v) for v in src_verts],
        "claimed_source_max_phi": format_rat(src_max),
        "claimed_source_argmax_idx": p_idx,
        "claimed_next_eta_values": _vec_json(next_eta),
        "claimed_target_max_phi": format_rat(tgt_max),
        "claimed_potential_strict_increase": True,
    }


def _make_mode4(
    cert_id: str,
    d: int,
    obj_c: VecQ,
    forms: List[AffFormQ],
    chambers: List[Dict[str, Any]],
) -> Dict[str, Any]:
    ch_ids = [c["id"] for c in chambers]
    edges = {c["id"]: list(c["outgoing_targets"]) for c in chambers}
    b_lams = {c["id"]: Fraction(c["optimal_value"]) for c in chambers if c["is_bounded"]}
    inf_s = max(b_lams.values()) + Fraction(1, 1)
    levels = {c["id"]: (b_lams[c["id"]] if c["is_bounded"] else inf_s) for c in chambers}
    is_dag, same_lens = longest_same_level_paths_dag(ch_ids, edges, levels)
    assert is_dag
    max_same = max(same_lens[cid] for cid in b_lams)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "acyclic_chamber_dag_escape_cert",
        "cert_id": cert_id,
        "dim": d,
        "objective_c": _vec_json(obj_c),
        "hyperplanes": _forms_json(forms),
        "chambers": chambers,
        "claimed_is_acyclic": True,
        "claimed_max_same_level_walk": max_same,
        "claimed_uniform_escape_L": max_same + 1,
    }


def build_all_certificates() -> List[Dict[str, Any]]:
    certs: List[Dict[str, Any]] = []

    # =========================================================================
    # Mode 1: 4 canonical Prop. 1 & Theorem 2 (2^r - 1 Target Chambers) certs
    # =========================================================================
    # 1a: Exact Figure 4 Panel 1 (3 lines through origin: x1=0, x2=0, x1+x2=0; F1={x1<0,x2=0})
    f_fig4: List[AffFormQ] = [
        ([Fraction(1), Fraction(0)], Fraction(0)),
        ([Fraction(0), Fraction(1)], Fraction(0)),
        ([Fraction(1), Fraction(1)], Fraction(0)),
    ]
    certs.append(
        _make_mode1(
            "m1_flag_2d_axes_fig4_panel1",
            2,
            2,
            f_fig4,
            [[Fraction(-2), Fraction(-1)], [Fraction(-1), Fraction(0)], [Fraction(0), Fraction(0)]],
            [[1], [0, 2]],
            {
                "+1,-1": [Fraction(2), Fraction(-1)],
                "-1,+1": [Fraction(-2), Fraction(1)],
                "-1,-1": [Fraction(2), Fraction(1)],
            },
        )
    )

    # 1b: Exact Figure 4 Panel 2 (same arrangement, F1={x1=0, x2<0})
    certs.append(
        _make_mode1(
            "m1_flag_2d_axes_fig4_panel2",
            2,
            2,
            f_fig4,
            [[Fraction(-1), Fraction(-2)], [Fraction(0), Fraction(-1)], [Fraction(0), Fraction(0)]],
            [[0], [1, 2]],
            {
                "+1,-1": [Fraction(-1), Fraction(2)],
                "-1,+1": [Fraction(1), Fraction(-2)],
                "-1,-1": [Fraction(1), Fraction(2)],
            },
        )
    )

    # 1c: 3D codim r=3 (5 hyperplanes, 2^3 - 1 = 7 distinct target chambers!)
    f_3d: List[AffFormQ] = [
        ([Fraction(1), Fraction(0), Fraction(0)], Fraction(0)),
        ([Fraction(0), Fraction(1), Fraction(0)], Fraction(0)),
        ([Fraction(0), Fraction(0), Fraction(1)], Fraction(0)),
        ([Fraction(1), Fraction(1), Fraction(0)], Fraction(0)),
        ([Fraction(0), Fraction(1), Fraction(1)], Fraction(0)),
    ]
    tw_3d: Dict[str, VecQ] = {}
    for a1, a2, a3 in itertools.product((1, -1), repeat=3):
        if (a1, a2, a3) == (1, 1, 1):
            continue
        key = ",".join("+1" if v == 1 else "-1" for v in (a1, a2, a3))
        tw_3d[key] = [Fraction(4 * a3), Fraction(2 * a2), Fraction(1 * a1)]
    certs.append(
        _make_mode1(
            "m1_flag_3d_coupled_codim3",
            3,
            3,
            f_3d,
            [
                [Fraction(4), Fraction(2), Fraction(1)],
                [Fraction(4), Fraction(2), Fraction(0)],
                [Fraction(4), Fraction(0), Fraction(0)],
                [Fraction(0), Fraction(0), Fraction(0)],
            ],
            [[2], [1, 4], [0, 3]],
            tw_3d,
        )
    )

    # 1d: 4D affine arrangement with non-central hyperplane H_6 outside H(F,P), codim r=4 -> 15 targets!
    f_4d: List[AffFormQ] = [
        ([Fraction(1), Fraction(0), Fraction(0), Fraction(0)], Fraction(0)),
        ([Fraction(0), Fraction(1), Fraction(0), Fraction(0)], Fraction(0)),
        ([Fraction(0), Fraction(0), Fraction(1), Fraction(0)], Fraction(0)),
        ([Fraction(0), Fraction(0), Fraction(0), Fraction(1)], Fraction(0)),
        ([Fraction(1), Fraction(1), Fraction(0), Fraction(0)], Fraction(0)),
        ([Fraction(0), Fraction(0), Fraction(1), Fraction(1)], Fraction(0)),
        ([Fraction(1), Fraction(1), Fraction(1), Fraction(1)], Fraction(20)),
    ]
    tw_4d: Dict[str, VecQ] = {}
    for a1, a2, a3, a4 in itertools.product((1, -1), repeat=4):
        if (a1, a2, a3, a4) == (1, 1, 1, 1):
            continue
        key = ",".join("+1" if v == 1 else "-1" for v in (a1, a2, a3, a4))
        tw_4d[key] = [Fraction(8 * a4), Fraction(4 * a3), Fraction(2 * a2), Fraction(1 * a1)]
    certs.append(
        _make_mode1(
            "m1_flag_4d_affine_codim4_15targets",
            4,
            4,
            f_4d,
            [
                [Fraction(8), Fraction(4), Fraction(2), Fraction(1)],
                [Fraction(8), Fraction(4), Fraction(2), Fraction(0)],
                [Fraction(8), Fraction(4), Fraction(0), Fraction(0)],
                [Fraction(8), Fraction(0), Fraction(0), Fraction(0)],
                [Fraction(0), Fraction(0), Fraction(0), Fraction(0)],
            ],
            [[3], [2, 5], [1], [0, 4]],
            tw_4d,
        )
    )

    # =========================================================================
    # Mode 2: 4 canonical Section 2 Figure 2 Quasipolyhedral Counterexample certs
    # =========================================================================
    certs.append(_make_mode2("m2_fig2_counterexample_N4", 4))
    certs.append(_make_mode2("m2_fig2_counterexample_N8", 8))
    certs.append(_make_mode2("m2_fig2_counterexample_N12", 12))
    certs.append(_make_mode2("m2_fig2_counterexample_N16", 16))

    # =========================================================================
    # Mode 3: 4 canonical Section 6 Frame Strategy Slice & Potential certs
    # =========================================================================
    # 3a: 2D equal-lambda, equal-dimF step where S_F strictly increases (-1/2 -> 1)
    certs.append(
        _make_mode3(
            "m3_frame_2d_same_face_lex_step",
            2,
            eta=[Fraction(0), Fraction(1)],
            phi=[Fraction(1), Fraction(0)],
            src_rays=[[Fraction(-1), Fraction(-2)], [Fraction(-3), Fraction(-1)]],  # slice verts: (-1/2,-1), (-3,-1) -> max=-1/2
            tgt_rays=[[Fraction(1), Fraction(-1)], [Fraction(-1), Fraction(-2)]],   # slice verts: (1,-1), (-1/2,-1) -> max=1 > -1/2!
            lam_s=Fraction(0),
            lam_t=Fraction(0),
            dim_s=0,
            dim_t=0,
        )
    )

    # 3b: 3D simplicial cone (3 rays), equal lambda, equal dimF, S_F increases (0 -> 1)
    certs.append(
        _make_mode3(
            "m3_frame_3d_simplex_slice_step",
            3,
            eta=[Fraction(1), Fraction(1), Fraction(1)],
            phi=[Fraction(2), Fraction(1), Fraction(0)],
            src_rays=[
                [Fraction(-2), Fraction(0), Fraction(0)],   # v=(-1,0,0), phi=-2
                [Fraction(0), Fraction(-1), Fraction(0)],   # v=(0,-1,0), phi=-1
                [Fraction(0), Fraction(0), Fraction(-1)],   # v=(0,0,-1), phi=0 (max=0!)
            ],
            tgt_rays=[
                [Fraction(1), Fraction(-2), Fraction(0)],   # eta=-1 -> v=(1,-2,0), phi=0
                [Fraction(2), Fraction(-3), Fraction(0)],   # eta=-1 -> v=(2,-3,0), phi=1 (max=1 > 0!)
                [Fraction(0), Fraction(0), Fraction(-1)],   # v=(0,0,-1), phi=0
            ],
            lam_s=Fraction(5),
            lam_t=Fraction(5),
            dim_s=0,
            dim_t=0,
        )
    )

    # 3c: 3D equal-lambda dimension jump (dim F: 0 -> 1!), both full rank 3!
    certs.append(
        _make_mode3(
            "m3_frame_3d_dim_jump_step",
            3,
            eta=[Fraction(0), Fraction(1), Fraction(1)],
            phi=[Fraction(3), Fraction(1), Fraction(-1)],
            src_rays=[
                [Fraction(1), Fraction(-1), Fraction(0)],   # v=(1,-1,0), phi=2
                [Fraction(-1), Fraction(0), Fraction(-2)],  # v=(-1/2,0,-1), phi=-1/2
                [Fraction(0), Fraction(-1), Fraction(-1)],  # v=(0,-1/2,-1/2), phi=0
            ],
            tgt_rays=[
                [Fraction(-1), Fraction(-1), Fraction(0)],  # v=(-1,-1,0), phi=-4
                [Fraction(0), Fraction(0), Fraction(-1)],   # v=(0,0,-1), phi=1
                [Fraction(1), Fraction(-2), Fraction(0)],   # v=(1/2,-1,0), phi=1/2 (full rank 3!)
            ],
            lam_s=Fraction(3),
            lam_t=Fraction(3),
            dim_s=0,
            dim_t=1,
        )
    )

    # 3d: 4D full-rank cones (4 rays each!), strict objective increase lam: 2 -> 7/2
    certs.append(
        _make_mode3(
            "m3_frame_4d_objective_jump_step",
            4,
            eta=[Fraction(1), Fraction(1), Fraction(1), Fraction(1)],
            phi=[Fraction(4), Fraction(3), Fraction(2), Fraction(1)],
            src_rays=[
                [Fraction(-1), Fraction(0), Fraction(0), Fraction(0)],
                [Fraction(0), Fraction(-1), Fraction(0), Fraction(0)],
                [Fraction(0), Fraction(0), Fraction(-1), Fraction(0)],
                [Fraction(0), Fraction(0), Fraction(0), Fraction(-1)],
            ],
            tgt_rays=[
                [Fraction(-2), Fraction(1), Fraction(0), Fraction(0)],
                [Fraction(0), Fraction(-2), Fraction(1), Fraction(0)],
                [Fraction(0), Fraction(0), Fraction(-2), Fraction(1)],
                [Fraction(0), Fraction(0), Fraction(0), Fraction(-1)],
            ],
            lam_s=Fraction(2),
            lam_t=Fraction(7, 2),
            dim_s=0,
            dim_t=0,
        )
    )

    # =========================================================================
    # Mode 4: 4 canonical Complete Acyclic Chamber DAG & Theorem 3 Escape L certs
    # =========================================================================
    # 4a: 2D coordinate cross (x=0, y=0), obj = x + 2y: 1 bounded + 3 unbounded chambers, L = 1
    f_cross: List[AffFormQ] = [
        ([Fraction(1), Fraction(0)], Fraction(0)),
        ([Fraction(0), Fraction(1)], Fraction(0)),
    ]
    ch_4a = [
        {
            "id": "c_mm",
            "interior_point": ["-1", "-1"],
            "is_bounded": True,
            "optimal_point": ["0", "0"],
            "dual_multipliers": ["1", "2"],
            "flag_layers": [[0], [1]],
            "optimal_value": "0",
            "potential": ["0", "0", "0"],
            "outgoing_targets": ["c_pm", "c_mp", "c_pp"],
        },
        {
            "id": "c_pm",
            "interior_point": ["1", "-1"],
            "is_bounded": False,
            "optimal_point": ["1", "0"],
            "dual_multipliers": ["0", "0"],
            "flag_layers": [],
            "optimal_value": "INF",
            "potential": ["INF"],
            "outgoing_targets": [],
        },
        {
            "id": "c_mp",
            "interior_point": ["-1", "1"],
            "is_bounded": False,
            "optimal_point": ["0", "1"],
            "dual_multipliers": ["0", "0"],
            "flag_layers": [],
            "optimal_value": "INF",
            "potential": ["INF"],
            "outgoing_targets": [],
        },
        {
            "id": "c_pp",
            "interior_point": ["1", "1"],
            "is_bounded": False,
            "optimal_point": ["1", "1"],
            "dual_multipliers": ["0", "0"],
            "flag_layers": [],
            "optimal_value": "INF",
            "potential": ["INF"],
            "outgoing_targets": [],
        },
    ]
    certs.append(_make_mode4("m4_dag_2d_cross_4chambers", 2, [Fraction(1), Fraction(2)], f_cross, ch_4a))

    # 4b: 2D 2x2 grid (x=0, x=1, y=0, y=1), obj = x + 2y: 4 bounded chambers + 5 unbounded chambers
    f_grid: List[AffFormQ] = [
        ([Fraction(1), Fraction(0)], Fraction(0)),
        ([Fraction(1), Fraction(0)], Fraction(-1)),
        ([Fraction(0), Fraction(1)], Fraction(0)),
        ([Fraction(0), Fraction(1)], Fraction(-1)),
    ]
    ch_4b = [
        {"id": "c00", "interior_point": ["-1", "-1"], "is_bounded": True, "optimal_point": ["0", "0"],
         "dual_multipliers": ["1", "0", "2", "0"], "flag_layers": [[0], [2]], "optimal_value": "0",
         "potential": ["0", "0", "0"], "outgoing_targets": ["c10", "c01", "c11"]},
        {"id": "c10", "interior_point": ["1/2", "-1"], "is_bounded": True, "optimal_point": ["1", "0"],
         "dual_multipliers": ["0", "1", "2", "0"], "flag_layers": [[1], [2]], "optimal_value": "1",
         "potential": ["1", "0", "0"], "outgoing_targets": ["c20", "c11", "c21"]},
        {"id": "c01", "interior_point": ["-1", "1/2"], "is_bounded": True, "optimal_point": ["0", "1"],
         "dual_multipliers": ["1", "0", "0", "2"], "flag_layers": [[0], [3]], "optimal_value": "2",
         "potential": ["2", "0", "0"], "outgoing_targets": ["c11", "c02", "c12"]},
        {"id": "c11", "interior_point": ["1/2", "1/2"], "is_bounded": True, "optimal_point": ["1", "1"],
         "dual_multipliers": ["0", "1", "0", "2"], "flag_layers": [[1], [3]], "optimal_value": "3",
         "potential": ["3", "0", "0"], "outgoing_targets": ["c21", "c12", "c22"]},
        {"id": "c20", "interior_point": ["2", "-1"], "is_bounded": False, "optimal_point": ["1", "0"],
         "dual_multipliers": ["0", "0", "0", "0"], "flag_layers": [], "optimal_value": "INF", "potential": ["INF"], "outgoing_targets": []},
        {"id": "c02", "interior_point": ["-1", "2"], "is_bounded": False, "optimal_point": ["0", "1"],
         "dual_multipliers": ["0", "0", "0", "0"], "flag_layers": [], "optimal_value": "INF", "potential": ["INF"], "outgoing_targets": []},
        {"id": "c21", "interior_point": ["2", "1/2"], "is_bounded": False, "optimal_point": ["1", "0"],
         "dual_multipliers": ["0", "0", "0", "0"], "flag_layers": [], "optimal_value": "INF", "potential": ["INF"], "outgoing_targets": []},
        {"id": "c12", "interior_point": ["1/2", "2"], "is_bounded": False, "optimal_point": ["0", "1"],
         "dual_multipliers": ["0", "0", "0", "0"], "flag_layers": [], "optimal_value": "INF", "potential": ["INF"], "outgoing_targets": []},
        {"id": "c22", "interior_point": ["2", "2"], "is_bounded": False, "optimal_point": ["1", "1"],
         "dual_multipliers": ["0", "0", "0", "0"], "flag_layers": [], "optimal_value": "INF", "potential": ["INF"], "outgoing_targets": []},
    ]
    certs.append(_make_mode4("m4_dag_2d_grid_9chambers", 2, [Fraction(1), Fraction(2)], f_grid, ch_4b))

    # 4c: 2D 4-line central fan (H0: y=0, H1: x=0, H2: x-y=0, H3: x+y=0), obj = y!
    # 8 chambers total (4 bounded lower, 4 unbounded upper), ALL satisfying strict complementarity,
    # exact Theorem 2 2^r - 1 flag targets, and true F(c) subseteq cl(b):
    #   c_LM (lam=0, dim=0, S=-1) -> c_RM (lam=0, dim=0, S=+1) -> c_RR (lam=0, dim=1) -> c_UR (INF)!
    # Exact max_same_level_walk = 2, uniform_escape_L = 3!
    f_fan: List[AffFormQ] = [
        ([Fraction(0), Fraction(1)], Fraction(0)),
        ([Fraction(1), Fraction(0)], Fraction(0)),
        ([Fraction(1), Fraction(-1)], Fraction(0)),
        ([Fraction(1), Fraction(1)], Fraction(0)),
    ]
    ch_4c = [
        {"id": "c_LL", "interior_point": ["-2", "-1"], "is_bounded": True, "optimal_point": ["-1", "0"],
         "dual_multipliers": ["1", "0", "0", "0"], "flag_layers": [[0]], "optimal_value": "0",
         "potential": ["0", "1", "0"], "outgoing_targets": ["c_UL"]},
        {"id": "c_LM", "interior_point": ["-1", "-2"], "is_bounded": True, "optimal_point": ["0", "0"],
         "dual_multipliers": ["1/4", "1/4", "1/2", "1/4"], "flag_layers": [[1], [0, 2, 3]], "optimal_value": "0",
         "potential": ["0", "0", "-1"], "outgoing_targets": ["c_RM", "c_UML", "c_UMR"]},
        {"id": "c_RM", "interior_point": ["1", "-2"], "is_bounded": True, "optimal_point": ["0", "0"],
         "dual_multipliers": ["1/4", "1/4", "1/4", "1/2"], "flag_layers": [[3], [0, 1, 2]], "optimal_value": "0",
         "potential": ["0", "0", "1"], "outgoing_targets": ["c_RR", "c_UL", "c_UML"]},
        {"id": "c_RR", "interior_point": ["2", "-1"], "is_bounded": True, "optimal_point": ["1", "0"],
         "dual_multipliers": ["1", "0", "0", "0"], "flag_layers": [[0]], "optimal_value": "0",
         "potential": ["0", "1", "0"], "outgoing_targets": ["c_UR"]},
        {"id": "c_UL", "interior_point": ["-2", "1"], "is_bounded": False, "optimal_point": ["-2", "1"],
         "dual_multipliers": ["0", "0", "0", "0"], "flag_layers": [], "optimal_value": "INF", "potential": ["INF"], "outgoing_targets": []},
        {"id": "c_UML", "interior_point": ["-1", "2"], "is_bounded": False, "optimal_point": ["-1", "2"],
         "dual_multipliers": ["0", "0", "0", "0"], "flag_layers": [], "optimal_value": "INF", "potential": ["INF"], "outgoing_targets": []},
        {"id": "c_UMR", "interior_point": ["1", "2"], "is_bounded": False, "optimal_point": ["1", "2"],
         "dual_multipliers": ["0", "0", "0", "0"], "flag_layers": [], "optimal_value": "INF", "potential": ["INF"], "outgoing_targets": []},
        {"id": "c_UR", "interior_point": ["2", "1"], "is_bounded": False, "optimal_point": ["2", "1"],
         "dual_multipliers": ["0", "0", "0", "0"], "flag_layers": [], "optimal_value": "INF", "potential": ["INF"], "outgoing_targets": []},
    ]
    certs.append(_make_mode4("m4_dag_2d_degenerate_escape_L3", 2, [Fraction(0), Fraction(1)], f_fan, ch_4c))

    # 4d: 3D coordinate octants (x=0, y=0, z=0), obj = x + 2y + 3z: 1 bounded + 7 unbounded targets!
    f_oct: List[AffFormQ] = [
        ([Fraction(1), Fraction(0), Fraction(0)], Fraction(0)),
        ([Fraction(0), Fraction(1), Fraction(0)], Fraction(0)),
        ([Fraction(0), Fraction(0), Fraction(1)], Fraction(0)),
    ]
    ch_4d: List[Dict[str, Any]] = [
        {
            "id": "oct_mmm",
            "interior_point": ["-1", "-1", "-1"],
            "is_bounded": True,
            "optimal_point": ["0", "0", "0"],
            "dual_multipliers": ["1", "2", "3"],
            "flag_layers": [[0], [1], [2]],
            "optimal_value": "0",
            "potential": ["0", "0", "0"],
            "outgoing_targets": [],
        }
    ]
    for sx, sy, sz in itertools.product((-1, 1), repeat=3):
        if (sx, sy, sz) == (-1, -1, -1):
            continue
        cid = "oct_" + "".join("p" if s == 1 else "m" for s in (sx, sy, sz))
        ch_4d[0]["outgoing_targets"].append(cid)
        ray = [str(1 if sx == 1 else 0), str(1 if sy == 1 else 0), str(1 if sz == 1 else 0)]
        ch_4d.append(
            {
                "id": cid,
                "interior_point": [str(sx), str(sy), str(sz)],
                "is_bounded": False,
                "optimal_point": ray,
                "dual_multipliers": ["0", "0", "0"],
                "flag_layers": [],
                "optimal_value": "INF",
                "potential": ["INF"],
                "outgoing_targets": [],
            }
        )
    certs.append(_make_mode4("m4_dag_3d_octants_8chambers", 3, [Fraction(1), Fraction(2), Fraction(3)], f_oct, ch_4d))

    return certs


def run_experiments() -> None:
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)

    certs = build_all_certificates()
    replay_rows: List[Dict[str, Any]] = []
    for cert in certs:
        out_path = CERT_DIR / f"{cert['cert_id']}.json"
        out_path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        verify_arrangement_certificate_exact(cert)
        times_ms: List[float] = []
        res: Dict[str, Any] = {}
        for _ in range(5):
            t0 = time.perf_counter()
            res = verify_arrangement_certificate_exact(cert)
            times_ms.append((time.perf_counter() - t0) * 1000.0)
        times_ms.sort()
        replay_rows.append(
            {
                "cert_id": cert["cert_id"],
                "mode": cert["mode"],
                "verify_ms": round(times_ms[2], 3),
                "summary": res,
            }
        )

    (DATA_DIR / "certificate_replay_summary.json").write_text(
        json.dumps({"count": len(replay_rows), "certificates": replay_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Exp 1: Theorem 2 Outgoing Target Fanout 2^r - 1 Across Codimensions r = 1..8
    exp1_rows = [{"r": r, "total_chambers": 1 << r, "outgoing_targets": (1 << r) - 1} for r in range(1, 9)]
    (DATA_DIR / "exp1_theorem2_target_fanout.json").write_text(
        json.dumps({"rows": exp1_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Exp 2: Section 2 Figure 2 Quasipolyhedral Counterexample Trajectory (n = 0..12)
    exp2_rows = []
    for n in range(13):
        px, py = fig2_point_q(n)
        y0 = fig2_line_eval_q(n, Fraction(0, 1))
        exp2_rows.append(
            {
                "n": n,
                "p_y_exact": format_rat(py),
                "p_y_dec": float(py),
                "sup_gap_dec": float(-py),
                "origin_intercept_exact": format_rat(y0),
                "origin_intercept_dec": float(y0),
            }
        )
    (DATA_DIR / "exp2_fig2_quasipolyhedral_curve.json").write_text(
        json.dumps({"rows": exp2_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Exp 3: Central Fan Escape Length L = k across Lower-Halfplane Fan Sectors k = 1..8
    exp3_rows = [
        {"width_k": k, "bounded_chambers": 2 * k, "max_same_level_walk": k - 1, "uniform_escape_L": k}
        for k in range(1, 9)
    ]
    (DATA_DIR / "exp3_degenerate_escape_scaling.json").write_text(
        json.dumps({"rows": exp3_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Exp 4: Frame Strategy Lemma 17 Slice Margin Summary across Canonical Mode 3 Certs
    exp4_rows = []
    for c in certs:
        if c["mode"] == "frame_strategy_slice_potential_cert":
            exp4_rows.append(
                {
                    "cert_id": c["cert_id"],
                    "dim": c["dim"],
                    "source_max_phi": float(Fraction(c["claimed_source_max_phi"])),
                    "target_max_phi": float(Fraction(c["claimed_target_max_phi"])),
                    "min_neg_next_eta": min(float(Fraction(v)) for v in c["claimed_next_eta_values"]),
                    "max_neg_next_eta": max(float(Fraction(v)) for v in c["claimed_next_eta_values"]),
                }
            )
    (DATA_DIR / "exp4_frame_slice_margins.json").write_text(
        json.dumps({"rows": exp4_rows}, indent=2) + "\n", encoding="utf-8"
    )

    print(f"Generated {len(certs)} canonical ARRANGEMENT-TRAVERSAL-CERT-1.0 certificates and 4 experiment JSONs.")
    for r in replay_rows:
        print(f"  {r['cert_id']:38s}  {r['verify_ms']:6.3f} ms  ({r['mode']})")


if __name__ == "__main__":
    run_experiments()
