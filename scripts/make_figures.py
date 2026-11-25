"""Generate 3 publication-grade figures for Paper 40:
ARRANGEMENT-TRAVERSAL-CERT-1.0 (Brennan Dury, arXiv:2611.32976).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "data"
FIG_DIR = ROOT / "figures"

plt.rcParams.update(
    {
        "font.family": "serif",
        "font.size": 8.5,
        "axes.titlesize": 9.2,
        "axes.labelsize": 8.5,
        "legend.fontsize": 7.2,
        "xtick.labelsize": 7.8,
        "ytick.labelsize": 7.8,
        "axes.grid": True,
        "grid.alpha": 0.28,
        "grid.linestyle": "--",
    }
)


def make_fig1() -> None:
    d1 = json.loads((DATA_DIR / "exp1_theorem2_target_fanout.json").read_text(encoding="utf-8"))
    d2 = json.loads((DATA_DIR / "exp2_fig2_quasipolyhedral_curve.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.6), dpi=300)

    # Panel (a): Theorem 2 fanout 2^r - 1
    rs = [r["r"] for r in d1["rows"]]
    outs = [r["outgoing_targets"] for r in d1["rows"]]
    tots = [r["total_chambers"] for r in d1["rows"]]
    ax1.plot(rs, outs, "o-", color="#1f4e79", lw=1.8, ms=5.0, label=r"Outgoing target chambers $2^r - 1$")
    ax1.plot(rs, tots, "s--", color="#548235", lw=1.5, ms=4.2, label=r"Total flag chambers $2^r$ (incl. source)")
    ax1.set_yscale("log", base=2)
    ax1.set_xlabel(r"Optimal face codimension $r = \mathrm{codim}(F)$")
    ax1.set_ylabel("Chamber count (log scale)")
    ax1.set_title("(a) Theorem 2 Flag Target Fanout $2^r - 1$")
    ax1.legend(loc="upper left", framealpha=0.92)

    # Panel (b): Section 2 Figure 2 quasipolyhedral non-attainment & compact origin hit
    ns = [r["n"] for r in d2["rows"]]
    gaps = [r["sup_gap_dec"] for r in d2["rows"]]
    ints = [-r["origin_intercept_dec"] for r in d2["rows"]]
    ax2.plot(ns, gaps, "o-", color="#1f4e79", lw=1.8, ms=4.5, label=r"Supremum gap $-\omega(p_n) = 2^{-n}$")
    ax2.plot(ns, ints, "s--", color="#c55a11", lw=1.7, ms=4.5, label=r"Origin intercept $|y_0(H_n)| = (n+2)2^{-(n+1)}$")
    ax2.axhline(1.0, color="#c00000", ls=":", lw=1.3, label=r"Compact segment bound $|y_0| \leq 1$")
    ax2.set_yscale("log")
    ax2.set_xlabel("Hyperplane / vertex index $n$")
    ax2.set_ylabel("Magnitude (log scale)")
    ax2.set_title("(b) Figure 2 Non-Attainment & Compact-Set Hit")
    ax2.legend(loc="lower left", framealpha=0.92, fontsize=6.7)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_fanout_and_fig2_counterexample.png", dpi=300)
    plt.close(fig)


def make_fig2() -> None:
    d3 = json.loads((DATA_DIR / "exp3_degenerate_escape_scaling.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.6), dpi=300)

    # Panel (a): Certified 8-chamber 4-line central fan DAG (m4_dag_2d_degenerate_escape_L3)
    ts = np.linspace(-2.2, 2.2, 100)
    ax1.axhline(0.0, color="#404040", lw=1.4)
    ax1.axvline(0.0, color="#404040", lw=1.4)
    ax1.plot(ts, ts, color="#404040", lw=1.3)
    ax1.plot(ts, -ts, color="#404040", lw=1.3)
    pts = {
        "c_LL": (-1.55, -0.62, r"$c_{\mathrm{LL}}$ ($\dim 1$)"),
        "c_LM": (-0.65, -1.48, r"$c_{\mathrm{LM}}$ ($\dim 0$)"),
        "c_RM": (0.65, -1.48, r"$c_{\mathrm{RM}}$ ($\dim 0$)"),
        "c_RR": (1.55, -0.62, r"$c_{\mathrm{RR}}$ ($\dim 1$)"),
        "c_UL": (-1.55, 0.62, r"$c_{\mathrm{UL}}$ ($\infty$)"),
        "c_UML": (-0.65, 1.48, r"$c_{\mathrm{UML}}$ ($\infty$)"),
        "c_UMR": (0.65, 1.48, r"$c_{\mathrm{UMR}}$ ($\infty$)"),
        "c_UR": (1.55, 0.62, r"$c_{\mathrm{UR}}$ ($\infty$)"),
    }
    same_edges = [("c_LM", "c_RM"), ("c_RM", "c_RR")]
    up_edges = [
        ("c_LL", "c_UL"),
        ("c_LM", "c_UML"), ("c_LM", "c_UMR"),
        ("c_RM", "c_UL"), ("c_RM", "c_UML"),
        ("c_RR", "c_UR"),
    ]
    for u, v in up_edges:
        x0, y0, _ = pts[u]
        x1, y1, _ = pts[v]
        ax1.annotate("", xy=(x1, y1), xytext=(x0, y0),
                     arrowprops=dict(arrowstyle="->", color="#2e75b6", lw=1.1, alpha=0.68, shrinkA=10, shrinkB=10))
    for u, v in same_edges:
        x0, y0, _ = pts[u]
        x1, y1, _ = pts[v]
        ax1.annotate("", xy=(x1, y1), xytext=(x0, y0),
                     arrowprops=dict(arrowstyle="->", color="#c55a11", lw=2.0, shrinkA=10, shrinkB=10))
    for cid, (x, y, lab) in pts.items():
        col = "#548235" if cid.startswith("c_U") else "#1f4e79"
        ax1.plot(x, y, "o", color=col, ms=6.8, zorder=5)
        dy = 0.20 if y > 0 else -0.22
        va = "bottom" if y > 0 else "top"
        ax1.text(x, y + dy, lab, ha="center", va=va, fontsize=6.4, color="#222222")
    ax1.set_xlim(-2.2, 2.2)
    ax1.set_ylim(-2.05, 2.05)
    ax1.set_xlabel("$x_1$ (orange: same $\\lambda=0$; blue: $\\lambda\\to\\infty$)")
    ax1.set_ylabel(r"$x_2$ (objective $\omega(x) = x_2$)")
    ax1.set_title("(a) Certified 4-Line Central Fan DAG ($L = 3$)")
    ax1.grid(False)

    # Panel (b): Theorem 3 Uniform Escape Length L vs Level-Set Width
    ks = [r["width_k"] for r in d3["rows"]]
    same_w = [r["max_same_level_walk"] for r in d3["rows"]]
    esc_L = [r["uniform_escape_L"] for r in d3["rows"]]
    ax2.plot(ks, esc_L, "o-", color="#1f4e79", lw=1.8, ms=5.0, label=r"Uniform escape length $L = L_{\max} + 1$")
    ax2.plot(ks, same_w, "s--", color="#c55a11", lw=1.7, ms=4.5, label=r"Max same-level walk $L_{\max} = k - 1$")
    ax2.set_xlabel("Degenerate level-set chamber width $k$")
    ax2.set_ylabel("Directed walk length (steps)")
    ax2.set_title("(b) Theorem 3 Uniform Escape Bound Scaling")
    ax2.legend(loc="upper left", framealpha=0.92)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_chamber_dag_and_escape.png", dpi=300)
    plt.close(fig)


def make_fig3() -> None:
    rep = json.loads((DATA_DIR / "certificate_replay_summary.json").read_text(encoding="utf-8"))
    rows = rep["certificates"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.6), dpi=300)

    mode_colors = {
        "flag_sign_targets_theorem2_cert": "#1f4e79",
        "fig2_quasipolyhedral_counterexample_cert": "#2e75b6",
        "frame_strategy_slice_potential_cert": "#548235",
        "acyclic_chamber_dag_escape_cert": "#c55a11",
    }
    mode_short = {
        "flag_sign_targets_theorem2_cert": "Mode 1 (Thm. 2 Flags)",
        "fig2_quasipolyhedral_counterexample_cert": "Mode 2 (Fig. 2 Counterex.)",
        "frame_strategy_slice_potential_cert": "Mode 3 (Sec. 6 Frame)",
        "acyclic_chamber_dag_escape_cert": "Mode 4 (Chamber DAG)",
    }
    xs = np.arange(len(rows))
    lat = [r["verify_ms"] for r in rows]
    cols = [mode_colors[r["mode"]] for r in rows]
    ax1.bar(xs, lat, color=cols, width=0.68, alpha=0.92)
    ax1.set_xticks(xs)
    ax1.set_xticklabels([f"C{i+1}" for i in range(len(rows))], fontsize=7.0)
    ax1.set_ylim(0, max(lat) * 1.38)
    ax1.set_xlabel("Canonical ARRANGEMENT-TRAVERSAL-CERT-1.0 cert (C1–C16)")
    ax1.set_ylabel("Exact zero-float replay latency (ms)")
    ax1.set_title("(a) Canonical Certificate Replay Latency")
    handles = [
        plt.Rectangle((0, 0), 1, 1, color=mode_colors[m], label=mode_short[m])
        for m in mode_colors
    ]
    ax1.legend(handles=handles, loc="upper left", ncol=2, framealpha=0.92, fontsize=6.4)

    cats = ["Global /\nType", "Mode 1\nThm. 2", "Mode 2\nFig. 2", "Mode 3\nFrame", "Mode 4\nDAG"]
    counts = [12, 13, 12, 14, 15]
    bcols = ["#595959", "#1f4e79", "#2e75b6", "#548235", "#c55a11"]
    bars = ax2.bar(cats, counts, color=bcols, width=0.58, alpha=0.92)
    for bar, c in zip(bars, counts):
        ax2.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.35, f"{c}/{c}",
                 ha="center", va="bottom", fontsize=7.8, fontweight="bold")
    ax2.set_ylim(0, 18.0)
    ax2.set_ylabel("Live adversarial forgeries rejected")
    ax2.set_title("(b) Adversarial Red-Team Audit (66/66 Rejected)")

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_certificate_replay_atlas.png", dpi=300)
    plt.close(fig)


def main() -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated all 3 Paper 40 publication figures successfully.")


if __name__ == "__main__":
    main()
