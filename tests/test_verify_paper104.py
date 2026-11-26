"""
Adversarial & certificate-integrity test suite for Paper 104 (57 tests):
  - Hadamard active-support LP-gap dominance & bit-complexity savings
  - Optimal b-ary matching tree invariants (b in {2,3}), 1/36 sharpness, ternary strategy space
  - 8x dimension-based & >=32x node-based PPAD-hardness tree-size sharpening
  - Exact m^2-support NFCE dichotomy (Matching Pennies on Gamma_2, G_{1/3} on Gamma_3 vs Gamma_2)
  - 25+ live adversarial mutation tests ensuring forged equilibria/parameters are strictly rejected
  - On-disk SHA-256 certificate and MANIFEST integrity verification
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from pathlib import Path
import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT.joinpath("verification")))

import verify_paper104 as v  # noqa: E402


# ---------------------------------------------------------------------------
# 1. Core theorem verification tests
# ---------------------------------------------------------------------------

def test_ast_zero_float_audit_passes():
    res = v.ast_zero_float_audit(ROOT.joinpath("verification", "verify_paper104.py"))
    assert res["passed"] is True
    assert res["violations"] == []


@pytest.mark.parametrize("s,K,Dm,B", [(1, 1, 1, 1), (3, 5, 2, 16), (10, 20, 6, 3600), (25, 25, 4, 4096)])
def test_hadamard_lp_gap_dominates_chps(s, K, Dm, B):
    res = v.verify_hadamard_lp_gap(s, K, Dm, B)
    assert res["strictly_sharper"] is True
    assert res["bit_saving_guaranteed"] >= 1


@pytest.mark.parametrize("b", [2, 3])
def test_bary_overhead_optimal_at_2_and_3(b):
    inv = v.bary_matching_game_invariants(b, 2, 5)
    assert inv["overhead_f_b"] == [6, 1]
    assert inv["V"] == 6 * inv["m"] + 5 * 5 + 5 - 3
    assert inv["d1"] == inv["m"] + 5 - 2


@pytest.mark.parametrize("b", [4, 5, 6, 10])
def test_bary_overhead_strictly_suboptimal_for_b_ge_4(b):
    inv = v.bary_matching_game_invariants(b, 2, 5)
    assert Fraction(*inv["overhead_f_b"]) > Fraction(6, 1)
    assert inv["d1"] == inv["m"] + 5 - 2  # still invariant of b!


def test_ternary_exponentially_smaller_pure_strategy_space():
    for k in range(1, 6):
        m = v.i_pow(3, k)
        t = (m - 1) // 2
        assert v.i_pow(3, t) < v.i_pow(4, t)


def test_dim_hardness_8x_reduction():
    for r in (2, 3, 5, 10, 20):
        m_chps = v.i_pow(2, v.ceil_log_base(8 * v.i_pow(r, 3), 2))
        m_sharp = v.i_pow(2, v.ceil_log_base(r * r * (r - 1) + 1, 2))
        assert m_chps >= 8 * m_sharp
        _, ln_hi = v.ln_one_plus_q_bracket(Fraction(r - 1, m_sharp), 24)
        assert ln_hi < Fraction(1, r * r)


def test_node_hardness_32x_reduction():
    for r in (5, 7, 10, 20):
        m_chps = v.i_pow(2, v.ceil_log_base(8 * v.i_pow(r, 4), 2))
        m_min = (r * r * (r * r + r - 3)) // 6 + 1
        m_sharp = v.i_pow(2, v.ceil_log_base(m_min, 2))
        assert m_chps >= 32 * m_sharp
        _, ln_hi = v.ln_one_plus_q_bracket(Fraction(r * r + r - 3, 6 * m_sharp), 24)
        assert ln_hi < Fraction(1, r * r)


def test_exact_m2_nfce_matching_pennies_binary():
    P = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 1)]]
    Q = [[Fraction(0, 1), Fraction(1, 1)], [Fraction(1, 1), Fraction(0, 1)]]
    supp = [((x1, x1), (x2, x2), Fraction(1, 4)) for x1 in (0, 1) for x2 in (0, 1)]
    res = v.verify_exact_nfce_on_gamma_b(P, Q, 2, 1, supp)
    assert res["exact_nfce"] is True
    assert res["equals_m_squared"] is True
    assert res["max_regret"] == [0, 1]


def test_exact_m2_nfce_asymmetric_third_ternary():
    P = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 2)]]
    Q = [[Fraction(0, 1), Fraction(1, 2)], [Fraction(1, 1), Fraction(0, 1)]]
    y1 = [0, 0, 1]
    y2 = [0, 1, 1]
    supp = [((y1[x1], x1), (y2[x2], x2), Fraction(1, 9)) for x1 in range(3) for x2 in range(3)]
    res = v.verify_exact_nfce_on_gamma_b(P, Q, 3, 1, supp)
    assert res["exact_nfce"] is True
    assert res["support_size"] == 9
    assert res["equals_m_squared"] is True


def test_three_never_divides_power_of_two():
    for k in range(0, 40):
        assert v.i_pow(2, k) % 3 != 0


@pytest.mark.parametrize("r", [2, 3, 4])
def test_corollary20_strictly_negative_below_r5(r):
    assert r * r - 5 * r + 3 < 0


@pytest.mark.parametrize("r", [5, 6, 7, 10, 20, 50, 100])
def test_corollary20_nonnegative_for_r_ge_5(r):
    assert r * r - 5 * r + 3 >= 3


def test_two_player_support_gap_positive():
    for d1 in range(1, 12):
        for d2 in range(1, 12):
            K = 1 + d1 * (d1 + 1) + d2 * (d2 + 1)
            kd = (d1 + 1) * (d2 + 1)
            assert K > kd
            assert 2 * (K - kd) >= d1 * d1 + d2 * d2


# ---------------------------------------------------------------------------
# 2. Live adversarial mutation / forgery rejection tests
# ---------------------------------------------------------------------------

def test_adv_reject_bad_lp_gap_order():
    with pytest.raises(ValueError):
        v.verify_hadamard_lp_gap(6, 5, 2, 4)  # s > K
    with pytest.raises(ValueError):
        v.verify_hadamard_lp_gap(3, 5, 10, 4)  # D_max > B
    with pytest.raises(ValueError):
        v.verify_hadamard_lp_gap(0, 5, 1, 1)  # s = 0


def test_adv_reject_invalid_bary_params():
    with pytest.raises(ValueError):
        v.bary_matching_game_invariants(1, 2, 3)  # b < 2
    with pytest.raises(ValueError):
        v.bary_matching_game_invariants(2, 0, 3)  # k < 1
    with pytest.raises(ValueError):
        v.bary_matching_game_invariants(2, 2, 1)  # r < 2


def test_adv_reject_nonuniform_matching_weights():
    P = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 1)]]
    Q = [[Fraction(0, 1), Fraction(1, 1)], [Fraction(1, 1), Fraction(0, 1)]]
    # Perturb weights so X2|tau1 is not uniform
    supp = [
        ((0, 0), (0, 0), Fraction(3, 10)),
        ((0, 0), (1, 1), Fraction(2, 10)),
        ((1, 1), (0, 0), Fraction(2, 10)),
        ((1, 1), (1, 1), Fraction(3, 10)),
    ]
    with pytest.raises(ValueError, match="uniform"):
        v.verify_exact_nfce_on_gamma_b(P, Q, 2, 1, supp)


def test_adv_reject_wrong_branch_G_marginal_on_G_third():
    # Use wrong marginal (1/3, 2/3) for Player 1 instead of (2/3, 1/3) on ternary G_{1/3}
    P = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 2)]]
    Q = [[Fraction(0, 1), Fraction(1, 2)], [Fraction(1, 1), Fraction(0, 1)]]
    y1_bad = [0, 1, 1]  # marginal (1/3, 2/3) -> Player 2 has positive regret!
    y2 = [0, 1, 1]
    supp = [((y1_bad[x1], x1), (y2[x2], x2), Fraction(1, 9)) for x1 in range(3) for x2 in range(3)]
    with pytest.raises(ValueError, match="Player 2 positive regret"):
        v.verify_exact_nfce_on_gamma_b(P, Q, 3, 1, supp)


def test_adv_reject_wrong_player1_marginal_on_G_third():
    P = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 2)]]
    Q = [[Fraction(0, 1), Fraction(1, 2)], [Fraction(1, 1), Fraction(0, 1)]]
    y1 = [0, 0, 1]
    y2_bad = [0, 0, 1]  # marginal (2/3, 1/3) -> Player 1 has positive regret!
    supp = [((y1[x1], x1), (y2_bad[x2], x2), Fraction(1, 9)) for x1 in range(3) for x2 in range(3)]
    with pytest.raises(ValueError, match="Player 1 positive regret"):
        v.verify_exact_nfce_on_gamma_b(P, Q, 3, 1, supp)


def test_adv_reject_binary_m2_attempt_on_G_third():
    # Exhaustively test ALL 2^2 * 2^2 = 16 uniform 2x2 assignments on binary Gamma_2(G_{1/3}, k=1):
    # EVERY single one MUST fail exact NFCE because unique Nash has denominator 3!
    P = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 2)]]
    Q = [[Fraction(0, 1), Fraction(1, 2)], [Fraction(1, 1), Fraction(0, 1)]]
    for a0 in (0, 1):
        for a1 in (0, 1):
            for b0 in (0, 1):
                for b1 in (0, 1):
                    y1 = [a0, a1]
                    y2 = [b0, b1]
                    supp = [((y1[x1], x1), (y2[x2], x2), Fraction(1, 4)) for x1 in (0, 1) for x2 in (0, 1)]
                    with pytest.raises(ValueError, match="positive regret"):
                        v.verify_exact_nfce_on_gamma_b(P, Q, 2, 1, supp)


def test_adv_reject_unnormalized_weights():
    P = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 1)]]
    Q = [[Fraction(0, 1), Fraction(1, 1)], [Fraction(1, 1), Fraction(0, 1)]]
    supp = [((x1, x1), (x2, x2), Fraction(1, 5)) for x1 in (0, 1) for x2 in (0, 1)]
    with pytest.raises(ValueError, match="sum to 1"):
        v.verify_exact_nfce_on_gamma_b(P, Q, 2, 1, supp)


def test_adv_reject_duplicate_profile():
    P = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 1)]]
    Q = [[Fraction(0, 1), Fraction(1, 1)], [Fraction(1, 1), Fraction(0, 1)]]
    supp = [((0, 0), (0, 0), Fraction(1, 2)), ((0, 0), (0, 0), Fraction(1, 2))]
    with pytest.raises(ValueError, match="Duplicate"):
        v.verify_exact_nfce_on_gamma_b(P, Q, 2, 1, supp)


def test_adv_reject_zero_or_negative_weight():
    P = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 1)]]
    Q = [[Fraction(0, 1), Fraction(1, 1)], [Fraction(1, 1), Fraction(0, 1)]]
    supp = [((0, 0), (0, 0), Fraction(0, 1)), ((1, 1), (1, 1), Fraction(1, 1))]
    with pytest.raises(ValueError, match="strictly positive"):
        v.verify_exact_nfce_on_gamma_b(P, Q, 2, 1, supp)


def test_adv_reject_out_of_range_ln_and_exp():
    with pytest.raises(ValueError):
        v.ln_one_plus_q_bracket(Fraction(0, 1))
    with pytest.raises(ValueError):
        v.ln_one_plus_q_bracket(Fraction(1, 1))
    with pytest.raises(ValueError):
        v.exp_small_q_bracket(Fraction(0, 1))
    with pytest.raises(ValueError):
        v.exp_small_q_bracket(Fraction(3, 4))


def test_adv_reject_bool_strict_int():
    assert v.is_strict_int(True) is False
    with pytest.raises(ValueError):
        v.i_pow(True, 2)  # type: ignore[arg-type]


def test_adv_ast_catches_float_div_pow_numpy_string_frac(tmp_path):
    bad = tmp_path / "bad.py"
    bad.write_text("import numpy\nfrom fractions import Fraction\nx = 1.5 / 2 ** 3\ny = Fraction('0.5')\n", encoding="utf-8")
    res = v.ast_zero_float_audit(bad)
    assert res["passed"] is False
    assert len(res["violations"]) >= 5


# ---------------------------------------------------------------------------
# 3. On-disk SHA-256 certificate & MANIFEST integrity tests (16 certs)
# ---------------------------------------------------------------------------

def test_manifest_exists_and_has_16_certs():
    mpath = ROOT.joinpath("certificates", "MANIFEST.json")
    assert mpath.exists()
    manifest = json.loads(mpath.read_text(encoding="utf-8"))
    assert manifest["protocol"] == v.PROTOCOL
    assert manifest["certificate_count"] == 16
    assert len(manifest["certificates"]) == 16
    body = {
        "protocol": manifest["protocol"],
        "certificate_count": manifest["certificate_count"],
        "certificates": manifest["certificates"],
    }
    assert v.canonical_sha256(body) == manifest["manifest_sha256"]


@pytest.mark.parametrize("idx", list(range(1, 17)))
def test_on_disk_certificate_sha256_integrity(idx):
    cid = f"C{idx:02d}"
    cpath = ROOT.joinpath("certificates", f"{cid}.json")
    assert cpath.exists()
    rec = json.loads(cpath.read_text(encoding="utf-8"))
    assert rec["protocol"] == v.PROTOCOL
    assert rec["cert_id"] == cid
    body = {
        "protocol": rec["protocol"],
        "cert_id": rec["cert_id"],
        "title": rec["title"],
        "data": rec["data"],
    }
    assert v.canonical_sha256(body) == rec["sha256"]
    manifest = json.loads(ROOT.joinpath("certificates", "MANIFEST.json").read_text(encoding="utf-8"))
    by_id = {c["cert_id"]: c["sha256"] for c in manifest["certificates"]}
    assert by_id[cid] == rec["sha256"]
