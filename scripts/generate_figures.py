"""
Generate 3 publication-grade 300-DPI figures for Paper 104:
  1. fig1_lp_gap_and_support_dominance.png:
     (a) Bit-precision log2(1/epsilon_Gamma) comparison on CHPS matching-tree games (q=2, q=10):
         CHPS raw product B vs our LCM-Hadamard sharp bound (log-log savings across r=2..10);
     (b) Two-player support dominance K = 1 + d1(d1+1) + d2(d2+1) vs kappa_d = (d1+1)(d2+1)
         showing exact 2x asymptotic saving along the balanced diagonal d1 = d2.
  2. fig2_bary_optimality_and_ternary_space.png:
     (a) b-ary matching-tree node overhead f(b) = b + 2 + 2/(b-1) showing unique integer minimum
         f(b) = 6 at b in {2, 3} (proving 1/36 sharpness in Corollary 20);
     (b) Pure-strategy space log10(|Sigma_i|/r) at matched node count 6m + r^2 + r - 3:
         ternary (b=3, 3^{(m-1)/2}) exponentially below binary (b=2, 2^{m-1}).
  3. fig3_hardness_tree_sharpening.png:
     (a) Dimension-based PPAD-hardness matching tree m_d*(r) vs CHPS 8r^3 (exact >=8x reduction);
     (b) Node-based PPAD-hardness matching tree m_V*(r) vs CHPS 8r^4 (exact >=32x reduction for r>=5).
"""

from __future__ import annotations

import math
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent.parent
FIG_DIR = ROOT.joinpath("paper", "figures")
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "font.size": 9.5,
    "axes.titlesize": 10.5,
    "axes.titleweight": "bold",
    "axes.labelsize": 9.5,
    "legend.fontsize": 7.9,
    "xtick.labelsize": 8.5,
    "ytick.labelsize": 8.5,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "figure.dpi": 300,
})


def make_fig1() -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.6, 4.15))

    # Panel (a): Bit-precision required log2(1/eps) on Gamma_2(P, Q, k) for q=10 vs r=2..10
    rs = np.arange(2, 11)
    bits_chps_q2, bits_sharp_q2 = [], []
    bits_chps_q10, bits_sharp_q10 = [], []
    for r in rs:
        m = 2 ** math.ceil(math.log2(r * r * (r - 1) + 1))
        kd = (m + r - 1) ** 2
        for q, l_c, l_s in ((2, bits_chps_q2, bits_sharp_q2), (10, bits_chps_q10, bits_sharp_q10)):
            log2_B = 1.0 + 2 * (r ** 2) * math.log2(q)
            log2_D = 1.0 + math.log2(q)
            l_c.append(1.0 + (kd + 1) * (math.log2(kd + 1) + log2_B))
            l_s.append(1.0 + 0.5 * math.log2(kd) + 0.5 * kd * math.log2(kd + 1) + kd * log2_D)

    ax1.semilogy(rs, bits_chps_q10, "--o", color="#c62828", lw=1.9, ms=4.5, label="CHPS Lemma 14 ($q=10$, raw product $B$)")
    ax1.semilogy(rs, bits_sharp_q10, "-s", color="#2e7d32", lw=2.1, ms=4.5, label="Sharp LCM\u2013Hadamard ($q=10$, $D_{\\max}=2q$)")
    ax1.semilogy(rs, bits_chps_q2, ":^", color="#ef6c00", lw=1.7, ms=4.2, label="CHPS Lemma 14 ($q=2$)")
    ax1.semilogy(rs, bits_sharp_q2, "-.d", color="#1565c0", lw=1.8, ms=4.0, label="Sharp LCM\u2013Hadamard ($q=2$)")
    ratio_r8 = bits_chps_q10[6] / bits_sharp_q10[6]
    ax1.annotate(f"$r=8, q=10$:\n${ratio_r8:.1f}\\times$ fewer bits", xy=(8, bits_sharp_q10[6]), xytext=(6.0, 2.2e4),
                 arrowprops=dict(arrowstyle="->", color="#1b5e20", lw=1.1),
                 fontsize=7.9, color="#1b5e20", fontweight="bold")
    ax1.set_xlim(1.8, 10.2)
    ax1.set_ylim(2e2, 2e9)
    ax1.set_xlabel("Source bimatrix size $r$")
    ax1.set_ylabel("Required oracle precision $\\log_2(1/\\epsilon_\\Gamma)$ (bits)")
    ax1.set_title("(a) Exponential LP-Gap Bit-Precision Savings")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.93, fontsize=7.4)
    ax1.grid(alpha=0.22)

    # Panel (b): Two-player support ratio K / kappa_d along balanced diagonal d1 = d2 = d
    ds = np.logspace(0, 3, 300)
    K_bal = 1.0 + 2.0 * ds * (ds + 1.0)
    kd_bal = (ds + 1.0) ** 2
    ax2.semilogx(ds, K_bal / kd_bal, "-", color="#1565c0", lw=2.3, label="Balanced $d_1 = d_2 = d$: $K / \\kappa_d$")
    # Asymmetric d2 = 2*d1
    K_asy = 1.0 + ds * (ds + 1.0) + (2 * ds) * (2 * ds + 1.0)
    kd_asy = (ds + 1.0) * (2 * ds + 1.0)
    ax2.semilogx(ds, K_asy / kd_asy, "--", color="#6a1b9a", lw=2.0, label="Asymmetric $d_2 = 2 d_1$: $K / \\kappa_d \\to 2.5$")
    ax2.axhline(2.0, color="#2e7d32", ls=":", lw=1.4, label="Balanced asymptotic saving ($2.0\\times$)")
    ax2.axhline(1.0, color="k", ls="-", lw=0.9, alpha=0.5)
    ax2.set_xlim(1, 1000)
    ax2.set_ylim(1.0, 2.75)
    ax2.set_xlabel("Sequence-form dimension $d_1$ (log scale)")
    ax2.set_ylabel("Support ratio $K / \\kappa_d$")
    ax2.set_title("(b) Two-Player Support Dominance ($K$ vs $\\kappa_d$)")
    ax2.legend(loc="lower right", frameon=True, framealpha=0.93, fontsize=7.8)
    ax2.grid(alpha=0.22)

    fig.subplots_adjust(left=0.07, right=0.98, bottom=0.14, top=0.90, wspace=0.28)
    fig.savefig(FIG_DIR.joinpath("fig1_lp_gap_and_support_dominance.png"), dpi=300, bbox_inches="tight")
    plt.close(fig)


def make_fig2() -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.6, 4.15))

    # Panel (a): b-ary node overhead f(b) = b + 2 + 2/(b-1)
    bs = np.arange(2, 13)
    fb = bs + 2.0 + 2.0 / (bs - 1.0)
    b_cont = np.linspace(1.6, 12.4, 300)
    f_cont = b_cont + 2.0 + 2.0 / (b_cont - 1.0)

    ax1.plot(b_cont, f_cont, "-", color="#90a4ae", lw=1.4, label="Continuous $f(b) = b + 2 + \\frac{2}{b-1}$")
    ax1.scatter(bs[2:], fb[2:], color="#c62828", s=55, zorder=5, label="Suboptimal $b \\geq 4$ ($f(b) > 6$)")
    ax1.scatter([2, 3], [6.0, 6.0], color="#2e7d32", marker="*", s=145, zorder=7, label="Unique integer optima $b \\in \\{2, 3\\}$ ($f=6$)")
    ax1.axhline(6.0, color="#2e7d32", ls="--", lw=1.2)
    ax1.annotate("Sharp $1/36$ constant:\n$f(2)=f(3)=6$ exactly", xy=(3, 6.0), xytext=(6.2, 6.55),
                 arrowprops=dict(arrowstyle="->", color="#1b5e20", lw=1.1),
                 fontsize=8.0, color="#1b5e20", fontweight="bold")
    ax1.set_xlim(1.5, 12.5)
    ax1.set_ylim(5.2, 15.0)
    ax1.set_xticks(bs)
    ax1.set_xlabel("Matching-tree branching factor $b$")
    ax1.set_ylabel("Nodes per matching label $f(b) = |V_b|/m$")
    ax1.set_title("(a) Exact Optimality of Binary & Ternary Trees")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.93, fontsize=7.6)
    ax1.grid(alpha=0.22)

    # Panel (b): Pure-strategy space log10(|Sigma_i|/r) at matched node count 6m + r^2 + r - 3
    m_grid = np.linspace(3, 250, 300)
    log10_bin = (m_grid - 1.0) * math.log10(2.0)
    log10_tern = 0.5 * (m_grid - 1.0) * math.log10(3.0)

    ax2.plot(m_grid, log10_bin, "--", color="#c62828", lw=2.1, label="Binary $b=2$: $2^{m-1}$ ($\\log_{10} = 0.301(m-1)$)")
    ax2.plot(m_grid, log10_tern, "-", color="#2e7d32", lw=2.3, label="Ternary $b=3$: $3^{(m-1)/2}$ ($\\log_{10} = 0.239(m-1)$)")
    ax2.fill_between(m_grid, log10_tern, log10_bin, color="#e8f5e9", alpha=0.55)
    ax2.scatter([243], [121 * math.log10(3.0)], color="#1b5e20", s=55, zorder=6)
    ax2.annotate("$m=243$ (identical $|V|$):\n$10^{15.1}\\times$ fewer pure plans!",
                 xy=(243, 121 * math.log10(3.0)), xytext=(118, 12),
                 arrowprops=dict(arrowstyle="->", color="#1b5e20", lw=1.1),
                 fontsize=8.0, color="#1b5e20", fontweight="bold",
                 bbox=dict(boxstyle="round,pad=0.25", fc="#f1f8e9", ec="#2e7d32", lw=0.8))
    ax2.set_xlim(0, 260)
    ax2.set_ylim(0, 82)
    ax2.set_xlabel("Number of matching labels $m$ (matched $|V| = 6m + r^2 + r - 3$)")
    ax2.set_ylabel("Pure-strategy space $\\log_{10}(|\\Sigma_i| / r)$")
    ax2.set_title("(b) Ternary Exponential Strategy-Space Reduction")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.93, fontsize=7.6)
    ax2.grid(alpha=0.22)

    fig.subplots_adjust(left=0.07, right=0.98, bottom=0.14, top=0.90, wspace=0.28)
    fig.savefig(FIG_DIR.joinpath("fig2_bary_optimality_and_ternary_space.png"), dpi=300, bbox_inches="tight")
    plt.close(fig)


def make_fig3() -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.6, 4.15))

    # Panel (a): Dimension-based hardness tree size m_d*(r) vs CHPS 8r^3
    rs_d = np.array([2, 3, 4, 5, 8, 10, 16, 32, 64])
    m_chps_d = np.array([2 ** math.ceil(math.log2(8 * r ** 3)) for r in rs_d], dtype=float)
    m_sharp2_d = np.array([2 ** math.ceil(math.log2(r * r * (r - 1) + 1)) for r in rs_d], dtype=float)
    m_sharp3_d = np.array([3 ** math.ceil(math.log(r * r * (r - 1) + 1, 3)) for r in rs_d], dtype=float)

    ax1.loglog(rs_d, m_chps_d, "--o", color="#c62828", lw=2.0, ms=4.8, label="CHPS Sec. 4.5 ($m = 2^{\\lceil\\log_2(8r^3)\\rceil}$)")
    ax1.loglog(rs_d, m_sharp2_d, "-s", color="#2e7d32", lw=2.1, ms=4.8, label="Sharp binary $m_d^*(r)$ ($\\geq 8\\times$ smaller)")
    ax1.loglog(rs_d, m_sharp3_d, ":^", color="#1565c0", lw=1.8, ms=4.5, label="Sharp ternary $m_{d,3}^*(r)$")
    ax1.annotate("Exact $\\geq 8\\times$ tree-size\nreduction ($\\forall r \\geq 2$)",
                 xy=(16, m_sharp2_d[6]), xytext=(14, 1.2e2),
                 arrowprops=dict(arrowstyle="->", color="#1b5e20", lw=1.1),
                 fontsize=8.0, color="#1b5e20", fontweight="bold")
    ax1.set_xlim(1.7, 78)
    ax1.set_ylim(2, 1e7)
    ax1.set_xticks([2, 4, 8, 16, 32, 64])
    ax1.get_xaxis().set_major_formatter(plt.ScalarFormatter())
    ax1.minorticks_off()
    ax1.set_xlabel("Source bimatrix size $r$ (log scale)")
    ax1.set_ylabel("Matching-tree size $m$ (log scale)")
    ax1.set_title("(a) Dimension-Based Hardness ($\\geq 8\\times$ Sharper)")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.93, fontsize=7.6)
    ax1.grid(alpha=0.22)

    # Panel (b): Node-based hardness tree size m_V*(r) vs CHPS 8r^4 (r >= 5)
    rs_v = np.array([5, 6, 8, 10, 16, 32, 64])
    m_chps_v = np.array([2 ** math.ceil(math.log2(8 * r ** 4)) for r in rs_v], dtype=float)
    m_sharp2_v = np.array([2 ** math.ceil(math.log2((r * r * (r * r + r - 3)) // 6 + 1)) for r in rs_v], dtype=float)

    ax2.loglog(rs_v, m_chps_v, "--o", color="#c62828", lw=2.0, ms=4.8, label="CHPS Sec. 4.5 ($m = 2^{\\lceil\\log_2(8r^4)\\rceil}$)")
    ax2.loglog(rs_v, m_sharp2_v, "-s", color="#2e7d32", lw=2.2, ms=4.8, label="Sharp binary $m_V^*(r)$ ($32\\times$ to $64\\times$ smaller)")
    ax2.fill_between(rs_v, m_sharp2_v, m_chps_v, color="#e8f5e9", alpha=0.55)
    ratio_r10 = int(round(m_chps_v[3] / m_sharp2_v[3]))
    ratio_r64 = int(round(m_chps_v[-1] / m_sharp2_v[-1]))
    ax2.annotate(f"$r=10$: ${ratio_r10}\\times$ smaller\n($r=64$: ${ratio_r64}\\times$ smaller)",
                 xy=(10, m_sharp2_v[3]), xytext=(17, 1.5e3),
                 arrowprops=dict(arrowstyle="->", color="#1b5e20", lw=1.1),
                 fontsize=8.0, color="#1b5e20", fontweight="bold")
    ax2.set_xlim(4.4, 78)
    ax2.set_ylim(50, 5e8)
    ax2.set_xticks([5, 8, 16, 32, 64])
    ax2.get_xaxis().set_major_formatter(plt.ScalarFormatter())
    ax2.minorticks_off()
    ax2.set_xlabel("Source bimatrix size $r \\geq 5$ (log scale)")
    ax2.set_ylabel("Matching-tree size $m$ (log scale)")
    ax2.set_title("(b) Node-Based Hardness ($32\\times$ to $64\\times$ Sharper)")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.93, fontsize=7.6)
    ax2.grid(alpha=0.22)

    fig.subplots_adjust(left=0.07, right=0.98, bottom=0.14, top=0.90, wspace=0.28)
    fig.savefig(FIG_DIR.joinpath("fig3_hardness_tree_sharpening.png"), dpi=300, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated all 3 300-DPI figures for Paper 104 in", FIG_DIR)
