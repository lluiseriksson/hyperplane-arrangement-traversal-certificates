"""Comprehensive pytest & 66-attack live adversarial red-team suite for Paper 40:
ARRANGEMENT-TRAVERSAL-CERT-1.0 (Brennan Dury, arXiv:2611.32976).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import copy
import json
import sys
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.arrangement_certifier import ArrangementCertificateError, verify_arrangement_certificate_exact

CERT_DIR = ROOT / "certificates"


def _load(name: str) -> Dict[str, Any]:
    return json.loads((CERT_DIR / f"{name}.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_verify() -> None:
    paths = sorted(CERT_DIR.glob("*.json"))
    assert len(paths) == 16, f"Expected 16 certificates, found {len(paths)}"
    for p in paths:
        res = verify_arrangement_certificate_exact(json.loads(p.read_text(encoding="utf-8")))
        assert res["verified"] is True


def _mut(base: Dict[str, Any], fn: Callable[[Dict[str, Any]], None]) -> Dict[str, Any]:
    c = copy.deepcopy(base)
    fn(c)
    return c


def build_66_adversarial_attacks() -> List[Tuple[str, Any]]:
    m1 = _load("m1_flag_2d_axes_fig4_panel1")
    m2 = _load("m2_fig2_counterexample_N4")
    m3 = _load("m3_frame_3d_simplex_slice_step")
    m4 = _load("m4_dag_2d_degenerate_escape_L3")

    attacks: List[Tuple[str, Any]] = [
        # --- Global Schema / Type / Rational Hardening (12 attacks) ---
        ("g01_non_dict_root", [1, 2, 3]),
        ("g02_wrong_schema", _mut(m1, lambda c: c.__setitem__("schema", "ARRANGEMENT-TRAVERSAL-CERT-2.0"))),
        ("g03_empty_cert_id", _mut(m1, lambda c: c.__setitem__("cert_id", ""))),
        ("g04_unknown_mode", _mut(m1, lambda c: c.__setitem__("mode", "bogus"))),
        ("g05_float_leak", _mut(m3, lambda c: c["eta_covector"].__setitem__(0, 1.0))),
        ("g06_none_injection", _mut(m1, lambda c: c.__setitem__("dim", None))),
        ("g07_bool_as_int", _mut(m2, lambda c: c.__setitem__("max_index_N", True))),
        ("g08_unreduced_fraction", _mut(m2, lambda c: c.__setitem__("claimed_sup_gap", "2/32"))),
        ("g09_den_one_fraction", _mut(m1, lambda c: c["flag_witness_points"][0].__setitem__(0, "-2/1"))),
        ("g10_neg_zero_rat", _mut(m1, lambda c: c["flag_witness_points"][2].__setitem__(0, "-0"))),
        ("g11_oversized_rat_str", _mut(m2, lambda c: c.__setitem__("claimed_sup_gap", "1/" + "9" * 1200))),
        ("g12_huge_int_bitlen", _mut(m2, lambda c: c.__setitem__("max_index_N", 1 << 3000))),
        # --- Mode 1: Prop. 1 Face Calculus, Exact Codim Rank & Thm. 2 Targets (13 attacks) ---
        ("m1_01_extra_key", _mut(m1, lambda c: c.__setitem__("extra", 1))),
        ("m1_02_zero_normal_hyperplane", _mut(m1, lambda c: c["hyperplanes"][0].__setitem__("normal", ["0", "0"]))),
        ("m1_03_source_on_hyperplane", _mut(m1, lambda c: c["flag_witness_points"].__setitem__(0, ["-1", "0"]))),
        ("m1_04_flag_closure_broken", _mut(m1, lambda c: c["flag_witness_points"].__setitem__(1, ["1", "0"]))),
        ("m1_05_non_strict_flag_layer", _mut(m1, lambda c: c["flag_witness_points"].__setitem__(1, ["-2", "-1"]))),
        ("m1_06_wrong_layer_partition", _mut(m1, lambda c: c.__setitem__("layer_hyperplanes", [[0], [1, 2]]))),
        ("m1_07_missing_target_alpha", _mut(m1, lambda c: c["target_witness_points"].pop("-1,-1"))),
        ("m1_08_wrong_target_witness_sign", _mut(m1, lambda c: c["target_witness_points"].__setitem__("-1,-1", ["-2", "-1"]))),
        ("m1_09_target_on_hyperplane", _mut(m1, lambda c: c["target_witness_points"].__setitem__("-1,-1", ["0", "1"]))),
        ("m1_10_wrong_source_signs", _mut(m1, lambda c: c.__setitem__("claimed_source_signs", [1, 1, 1]))),
        ("m1_11_wrong_base_signs", _mut(m1, lambda c: c.__setitem__("claimed_base_signs", [-1, 0, 0]))),
        ("m1_12_wrong_target_count", _mut(m1, lambda c: c.__setitem__("claimed_target_count", 4))),
        ("m1_13_codim_rank_jump_bypass", _mut(m1, lambda c: (
            c.__setitem__("codim_r", 1),
            c.__setitem__("flag_witness_points", [["-2", "-1"], ["0", "0"]]),
            c.__setitem__("layer_hyperplanes", [[0, 1, 2]]),
            c.__setitem__("target_witness_points", {"-1": ["2", "1"]}),
            c.__setitem__("claimed_target_count", 1),
        ))),
        # --- Mode 2: Sec. 2 Figure 2 Quasipolyhedral Counterexample (12 attacks) ---
        ("m2_01_extra_key", _mut(m2, lambda c: c.__setitem__("extra", 1))),
        ("m2_02_N_too_small", _mut(m2, lambda c: c.__setitem__("max_index_N", 1))),
        ("m2_03_N_too_large", _mut(m2, lambda c: c.__setitem__("max_index_N", 30))),
        ("m2_04_pts_len_mismatch", _mut(m2, lambda c: c["claimed_boundary_points"].pop())),
        ("m2_05_wrong_p0_y", _mut(m2, lambda c: c["claimed_boundary_points"][0].__setitem__(1, "-1/2"))),
        ("m2_06_wrong_pN_y", _mut(m2, lambda c: c["claimed_boundary_points"][4].__setitem__(1, "0"))),
        ("m2_07_wrong_p2_x", _mut(m2, lambda c: c["claimed_boundary_points"][2].__setitem__(0, "3"))),
        ("m2_08_intercepts_len_mismatch", _mut(m2, lambda c: c["claimed_origin_intercepts"].pop())),
        ("m2_09_wrong_intercept_0", _mut(m2, lambda c: c["claimed_origin_intercepts"].__setitem__(0, "-1/2"))),
        ("m2_10_wrong_intercept_N", _mut(m2, lambda c: c["claimed_origin_intercepts"].__setitem__(4, "0"))),
        ("m2_11_wrong_max_y", _mut(m2, lambda c: c.__setitem__("claimed_max_y_value", "0"))),
        ("m2_12_wrong_sup_gap", _mut(m2, lambda c: c.__setitem__("claimed_sup_gap", "1/8"))),
        # --- Mode 3: Sec. 6 Frame Strategy Full-Rank Slice & Potential (14 attacks) ---
        ("m3_01_extra_key", _mut(m3, lambda c: c.__setitem__("extra", 1))),
        ("m3_02_zero_eta", _mut(m3, lambda c: c.__setitem__("eta_covector", ["0", "0", "0"]))),
        ("m3_03_positive_eta_ray", _mut(m3, lambda c: c["source_rays"].__setitem__(0, ["2", "0", "0"]))),
        ("m3_04_inadmissible_tie_source", _mut(m3, lambda c: c.__setitem__("phi_covector", ["0", "0", "0"]))),
        ("m3_05_inadmissible_tie_two_max", _mut(m3, lambda c: c["source_rays"].__setitem__(1, ["0", "0", "-2"]))),
        ("m3_06_lemma4_lambda_decrease", _mut(m3, lambda c: c.__setitem__("target_lambda", "4"))),
        ("m3_07_dim_decrease_same_lambda", _mut(m3, lambda c: c.__setitem__("target_opt_dim", -1))),
        ("m3_08_potential_not_increasing", _mut(m3, lambda c: (
            c.__setitem__("target_rays", copy.deepcopy(c["source_rays"])),
            c.__setitem__("claimed_target_max_phi", c["claimed_source_max_phi"]),
        ))),
        ("m3_09_wrong_slice_vert", _mut(m3, lambda c: c["claimed_source_slice_vertices"][0].__setitem__(0, "1"))),
        ("m3_10_wrong_argmax_idx", _mut(m3, lambda c: c.__setitem__("claimed_source_argmax_idx", 0))),
        ("m3_11_wrong_next_eta", _mut(m3, lambda c: c["claimed_next_eta_values"].__setitem__(0, "0"))),
        ("m3_12_strict_inc_false", _mut(m3, lambda c: c.__setitem__("claimed_potential_strict_increase", False))),
        ("m3_13_opt_dim_out_of_range", _mut(m3, lambda c: (
            c.__setitem__("source_opt_dim", -100),
            c.__setitem__("target_opt_dim", 999),
        ))),
        ("m3_14_rank_deficient_target_cone", _mut(m3, lambda c: c["target_rays"].__setitem__(2, ["2", "-4", "0"]))),
        # --- Mode 4: Acyclic Chamber DAG, Strict Complementarity & Exact Thm. 2 Targets (15 attacks) ---
        ("m4_01_extra_key", _mut(m4, lambda c: c.__setitem__("extra", 1))),
        ("m4_02_zero_objective", _mut(m4, lambda c: c.__setitem__("objective_c", ["0", "0"]))),
        ("m4_03_interior_on_hyperplane", _mut(m4, lambda c: c["chambers"][0].__setitem__("interior_point", ["-1", "0"]))),
        ("m4_04_duplicate_chamber_sig", _mut(m4, lambda c: c["chambers"][1].__setitem__("interior_point", ["-4", "-2"]))),
        ("m4_05_kkt_dual_stationarity_broken", _mut(m4, lambda c: c["chambers"][0].__setitem__("dual_multipliers", ["2", "0", "0", "0"]))),
        ("m4_06_negative_dual_multiplier", _mut(m4, lambda c: c["chambers"][0].__setitem__("dual_multipliers", ["-1", "0", "0", "0"]))),
        ("m4_07_comp_slackness_violated", _mut(m4, lambda c: c["chambers"][0].__setitem__("dual_multipliers", ["1", "1", "0", "0"]))),
        ("m4_08_bad_recession_ray", _mut(m4, lambda c: c["chambers"][4].__setitem__("optimal_point", ["-2", "-1"]))),
        ("m4_09_boundary_opt_strict_comp_fail", _mut(m4, lambda c: c["chambers"][0].__setitem__("optimal_point", ["0", "0"]))),
        ("m4_10_cycle_or_potential_drop", _mut(m4, lambda c: c["chambers"][2].__setitem__("potential", ["0", "0", "-2"]))),
        ("m4_11_wrong_max_same_walk", _mut(m4, lambda c: c.__setitem__("claimed_max_same_level_walk", 1))),
        ("m4_12_wrong_escape_L", _mut(m4, lambda c: c.__setitem__("claimed_uniform_escape_L", 2))),
        ("m4_13_dropped_thm2_target_edge", _mut(m4, lambda c: c["chambers"][1]["outgoing_targets"].pop())),
        ("m4_14_forged_dim_in_potential", _mut(m4, lambda c: c["chambers"][1]["potential"].__setitem__(1, "1"))),
        ("m4_15_unbounded_garbage_fields", _mut(m4, lambda c: c["chambers"][4].__setitem__("dual_multipliers", ["9", "9", "9", "9"]))),
    ]
    assert len(attacks) == 66
    return attacks


def test_66_live_adversarial_attacks_rejected() -> None:
    attacks = build_66_adversarial_attacks()
    rejected = 0
    for name, payload in attacks:
        try:
            verify_arrangement_certificate_exact(payload)
        except ArrangementCertificateError:
            rejected += 1
        else:
            raise AssertionError(f"Adversarial attack {name!r} was NOT rejected!")
    assert rejected == 66


def test_exact_no_float_source_audit() -> None:
    for rel in ["src/arrangement_exact.py", "src/arrangement_certifier.py"]:
        src = (ROOT / rel).read_text(encoding="utf-8")
        assert "float(" not in src, f"float() found in {rel}"
        assert "math." not in src, f"math. found in {rel}"
        assert "numpy" not in src, f"numpy found in {rel}"
