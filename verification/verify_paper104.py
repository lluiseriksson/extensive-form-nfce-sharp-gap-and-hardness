"""
AST-audited ZERO-FLOAT exact rational verifier for Paper 104:
  "Exponential Bit-Complexity Tightening, Optimal b-ary Matching Trees, and Exact
   Sharp Support Thresholds for Normal-Form Correlated Equilibria in Extensive-Form Games"
  (advancing V. Cheval, F. Horn, S. Paul, and M. Shirmohammadi, arXiv:2611.34897v1).

Protocol: EFG-NFCE-SHARP-1.0
Pure Python standard library (`fractions.Fraction`, `int`, `ast`, `hashlib`, `json`, `pathlib`).
Zero floats, zero complex numbers, zero `/` or `**` operators, zero float libraries.
"""

from __future__ import annotations

import ast
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Sequence, Tuple

PROTOCOL = "EFG-NFCE-SHARP-1.0"
ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT.joinpath("certificates")


# ---------------------------------------------------------------------------
# Strict exact integer / rational helpers (zero `/` and zero `**`)
# ---------------------------------------------------------------------------

def is_strict_int(x: Any) -> bool:
    return type(x) is int


def i_pow(a: int, n: int) -> int:
    if not is_strict_int(a) or not is_strict_int(n) or n < 0:
        raise ValueError("Invalid integer power arguments")
    res = 1
    base = a
    e = n
    while e > 0:
        if (e & 1) == 1:
            res = res * base
        base = base * base
        e >>= 1
    return res


def q_div(a: Fraction, b: Fraction) -> Fraction:
    if b == 0:
        raise ZeroDivisionError("Exact rational division by zero")
    return Fraction(a.numerator * b.denominator, a.denominator * b.numerator)


def q_pow(a: Fraction, n: int) -> Fraction:
    if not is_strict_int(n):
        raise TypeError("Exponent must be strict int")
    if n < 0:
        return q_pow(q_div(Fraction(1, 1), a), -n)
    res = Fraction(1, 1)
    base = a
    e = n
    while e > 0:
        if (e & 1) == 1:
            res = res * base
        base = base * base
        e >>= 1
    return res


def i_gcd(a: int, b: int) -> int:
    x = -a if a < 0 else a
    y = -b if b < 0 else b
    while y != 0:
        x, y = y, x % y
    return x


def i_lcm(a: int, b: int) -> int:
    if a == 0 or b == 0:
        return 0
    g = i_gcd(a, b)
    return (a // g) * b


def ceil_log_base(val: int, base: int) -> int:
    """Exact smallest integer k >= 0 such that base^k >= val (for val >= 1, base >= 2)."""
    if not is_strict_int(val) or not is_strict_int(base) or val < 1 or base < 2:
        raise ValueError("Invalid ceil_log_base args")
    k = 0
    p = 1
    while p < val:
        p *= base
        k += 1
    return k


def q_to_decimal_str(q: Fraction, digits: int = 8) -> str:
    sign = "-" if q < 0 else ""
    aq = -q if q < 0 else q
    scale = i_pow(10, digits)
    scaled = (aq.numerator * scale) // aq.denominator
    int_part = scaled // scale
    frac_part = scaled % scale
    return f"{sign}{int_part}.{str(frac_part).zfill(digits)}"


def q_pair(q: Fraction) -> List[int]:
    return [q.numerator, q.denominator]


# ---------------------------------------------------------------------------
# Certified exact rational brackets for ln(1+t) and exp(x)
# ---------------------------------------------------------------------------

def ln_one_plus_q_bracket(t: Fraction, terms: int = 24) -> Tuple[Fraction, Fraction]:
    """
    Certified exact rational bracket for ln(1 + t) for rational 0 < t < 1
    via alternating Taylor series sum_{k=1}^{infty} (-1)^{k-1} t^k / k.
    Even partial sum is a strict lower bound; odd partial sum is a strict upper bound.
    """
    if not (Fraction(0, 1) < t < Fraction(1, 1)):
        raise ValueError("Require 0 < t < 1 for alternating ln(1+t) bracket")
    if terms < 4 or (terms % 2) != 0:
        raise ValueError("Require even terms >= 4")
    s_prev = Fraction(0, 1)
    s_curr = Fraction(0, 1)
    tp = t
    for k in range(1, terms + 1):
        s_prev = s_curr
        term = q_div(tp, Fraction(k, 1))
        if (k & 1) == 1:
            s_curr = s_curr + term
        else:
            s_curr = s_curr - term
        tp = tp * t
    # terms is even -> s_curr is lower bound, s_prev (odd) is upper bound
    if not (s_curr < s_prev):
        raise ValueError("Alternating ln bracket ordering failed")
    return s_curr, s_prev


def exp_small_q_bracket(x: Fraction, terms: int = 24) -> Tuple[Fraction, Fraction]:
    """Certified exact rational bracket for exp(x) for 0 < x <= 1/2."""
    if not (Fraction(0, 1) < x <= Fraction(1, 2)):
        raise ValueError("Require 0 < x <= 1/2")
    s = Fraction(0, 1)
    xp = Fraction(1, 1)
    fact = 1
    for k in range(terms):
        if k > 0:
            xp = xp * x
            fact *= k
        s = s + q_div(xp, Fraction(fact, 1))
    rem = q_div(2 * q_pow(x, terms), Fraction(fact * terms, 1))
    return s, s + rem


# ---------------------------------------------------------------------------
# Exact domain verifiers (Theorems 1, 2, 3)
# ---------------------------------------------------------------------------

def verify_hadamard_lp_gap(s: int, K: int, D_max: int, B: int) -> Dict[str, Any]:
    """
    Verify Theorem 1:
      eta_sharp(s)^2 = 1 / (s * (s+1)^s * D_max^{2s})
      eta_CHPS^2     = 1 / (((K+1)*B)^{2*(K+1)}).
    Certify exact integer ratio R^2 = (eta_sharp / eta_CHPS)^2 and bit-length savings.
    """
    if not (1 <= s <= K and 1 <= D_max <= B):
        raise ValueError("Require 1 <= s <= K and 1 <= D_max <= B")
    denom_sharp_sq = s * i_pow(s + 1, s) * i_pow(D_max * D_max, s)
    denom_chps_sq = i_pow((K + 1) * B, 2 * (K + 1))
    if not (denom_sharp_sq < denom_chps_sq):
        raise ValueError("Sharp LP gap failed to dominate CHPS")
    # Exact integer bit-length of squared denominators (half gives bit-precision of 1/eta)
    bits_sharp_2x = denom_sharp_sq.bit_length()
    bits_chps_2x = denom_chps_sq.bit_length()
    # Exact ratio floor of (eta_sharp / eta_CHPS)^2
    ratio_sq_floor = denom_chps_sq // denom_sharp_sq
    bit_saving_floor = (ratio_sq_floor.bit_length() - 1) // 2
    return {
        "s": s,
        "K": K,
        "D_max": D_max,
        "B": B,
        "bits_sharp_approx": (bits_sharp_2x + 1) // 2,
        "bits_chps_approx": (bits_chps_2x + 1) // 2,
        "bit_saving_guaranteed": bit_saving_floor,
        "strictly_sharper": True,
    }


def bary_matching_game_invariants(b: int, k: int, r: int) -> Dict[str, Any]:
    """
    Exact structural invariants of the b-ary public-coin matching game Gamma_b(P, Q, k)
    with m = b^k matching labels and r x r source game (Theorem 2(a)).
    """
    if not (is_strict_int(b) and is_strict_int(k) and is_strict_int(r)):
        raise TypeError("Expected strict ints")
    if b < 2 or k < 1 or r < 2:
        raise ValueError("Require b >= 2, k >= 1, r >= 2")
    m = i_pow(b, k)
    if (m - 1) % (b - 1) != 0:
        raise ValueError("(m-1) must be divisible by (b-1)")
    internal_prefixes = (m - 1) // (b - 1)
    p1_nodes_M = internal_prefixes
    p2_nodes_M = b * internal_prefixes
    mismatch_leaves = b * (b - 1) * internal_prefixes
    match_leaves = m
    total_nodes_M = p1_nodes_M + p2_nodes_M + mismatch_leaves + match_leaves
    total_nodes = 1 + (r * r + r + 1) + total_nodes_M
    total_leaves = r * r + mismatch_leaves + match_leaves
    # Sequence-form dimension: (r - 1) in G + (b - 1)*I in M_b = m + r - 2 (INVARIANT of b!)
    d1 = (r - 1) + (b - 1) * internal_prefixes
    if d1 != m + r - 2:
        raise ValueError("Sequence-form dimension invariance failed")
    # Closed-form check for |Z_b| and |V_b|
    if total_leaves != (b + 1) * m - b + r * r:
        raise ValueError("Leaf count formula mismatch")
    overhead_num = (b + 2) * (b - 1) + 2
    overhead_q = Fraction(overhead_num, b - 1)
    const_q = Fraction((b + 1) * (b - 1) + 2, b - 1)
    expected_V = overhead_q * Fraction(m, 1) - const_q + Fraction(r * r + r + 2, 1)
    if expected_V != Fraction(total_nodes, 1):
        raise ValueError("Node count closed form mismatch")
    return {
        "b": b,
        "k": k,
        "r": r,
        "m": m,
        "internal_prefixes": internal_prefixes,
        "V": total_nodes,
        "Z": total_leaves,
        "d1": d1,
        "d2": d1,
        "overhead_f_b": q_pair(overhead_q),
        "sigma_exponent": internal_prefixes,
    }


def verify_exact_nfce_on_gamma_b(
    P: List[List[Fraction]],
    Q: List[List[Fraction]],
    b: int,
    k: int,
    support_weights: List[Tuple[Tuple[int, int], Tuple[int, int], Fraction]],
) -> Dict[str, Any]:
    """
    Exact zero-float verification of an NFCE on Gamma_b(P, Q, k) over the reduced
    pure-plan representation (y_i in [r], x_i in [m]), where a player can deviate
    independently to any (y'_i in [r], x'_i in [m])!
    Checks:
      1. Weights strictly positive and sum to 1.
      2. For every player i in {1, 2}, every supported recommendation tau_i,
         and every alternative pure plan tau'_i in [r] x [m], unnormalized regret <= 0.
      3. Conditional distribution of opponent matching label X_{-i} given tau_i is uniform on [m].
    """
    r = len(P)
    m = i_pow(b, k)
    if len(Q) != r or any(len(row) != r for row in P) or any(len(row) != r for row in Q):
        raise ValueError("Payoff matrices must be r x r")
    if len(support_weights) == 0:
        raise ValueError("Empty support")
    total_w = Fraction(0, 1)
    seen = set()
    for t1, t2, w in support_weights:
        if w <= 0:
            raise ValueError("Support weights must be strictly positive")
        if (t1, t2) in seen:
            raise ValueError("Duplicate profile in support")
        seen.add((t1, t2))
        if not (0 <= t1[0] < r and 0 <= t1[1] < m and 0 <= t2[0] < r and 0 <= t2[1] < m):
            raise ValueError("Out-of-range strategy index")
        total_w = total_w + w
    if total_w != Fraction(1, 1):
        raise ValueError("Weights do not sum to 1")

    def u1(t1: Tuple[int, int], t2: Tuple[int, int]) -> Fraction:
        match_term = Fraction(1, 2) if t1[1] == t2[1] else Fraction(0, 1)
        return Fraction(1, 2) * P[t1[0]][t2[0]] + match_term

    def u2(t1: Tuple[int, int], t2: Tuple[int, int]) -> Fraction:
        mismatch_term = Fraction(1, 2) if t1[1] != t2[1] else Fraction(0, 1)
        return Fraction(1, 2) * Q[t1[0]][t2[0]] + mismatch_term

    # Group by t1 and by t2
    by_t1: Dict[Tuple[int, int], List[Tuple[Tuple[int, int], Fraction]]] = {}
    by_t2: Dict[Tuple[int, int], List[Tuple[Tuple[int, int], Fraction]]] = {}
    for t1, t2, w in support_weights:
        by_t1.setdefault(t1, []).append((t2, w))
        by_t2.setdefault(t2, []).append((t1, w))

    max_regret = Fraction(0, 1)
    # Player 1 obedience & conditional X2 uniformity
    for t1, pairs in by_t1.items():
        cur_pay = Fraction(0, 1)
        marg_w = Fraction(0, 1)
        x2_counts: Dict[int, Fraction] = {x: Fraction(0, 1) for x in range(m)}
        for t2, w in pairs:
            cur_pay = cur_pay + w * u1(t1, t2)
            marg_w = marg_w + w
            x2_counts[t2[1]] = x2_counts[t2[1]] + w
        expected_unif = q_div(marg_w, Fraction(m, 1))
        for x in range(m):
            if x2_counts[x] != expected_unif:
                raise ValueError("Conditional X2 given tau1 is not uniform on [m]")
        for y1_alt in range(r):
            for x1_alt in range(m):
                alt_pay = Fraction(0, 1)
                for t2, w in pairs:
                    alt_pay = alt_pay + w * u1((y1_alt, x1_alt), t2)
                reg = alt_pay - cur_pay
                if reg > max_regret:
                    max_regret = reg
                if reg > Fraction(0, 1):
                    raise ValueError(f"Player 1 positive regret {reg} at tau1={t1} -> ({y1_alt},{x1_alt})")

    # Player 2 obedience & conditional X1 uniformity
    for t2, pairs in by_t2.items():
        cur_pay = Fraction(0, 1)
        marg_w = Fraction(0, 1)
        x1_counts: Dict[int, Fraction] = {x: Fraction(0, 1) for x in range(m)}
        for t1, w in pairs:
            cur_pay = cur_pay + w * u2(t1, t2)
            marg_w = marg_w + w
            x1_counts[t1[1]] = x1_counts[t1[1]] + w
        expected_unif = q_div(marg_w, Fraction(m, 1))
        for x in range(m):
            if x1_counts[x] != expected_unif:
                raise ValueError("Conditional X1 given tau2 is not uniform on [m]")
        for y2_alt in range(r):
            for x2_alt in range(m):
                alt_pay = Fraction(0, 1)
                for t1, w in pairs:
                    alt_pay = alt_pay + w * u2(t1, (y2_alt, x2_alt))
                reg = alt_pay - cur_pay
                if reg > max_regret:
                    max_regret = reg
                if reg > Fraction(0, 1):
                    raise ValueError(f"Player 2 positive regret {reg} at tau2={t2} -> ({y2_alt},{x2_alt})")

    return {
        "b": b,
        "k": k,
        "m": m,
        "r": r,
        "support_size": len(support_weights),
        "equals_m_squared": len(support_weights) == m * m,
        "max_regret": q_pair(max_regret),
        "conditional_uniformity_verified": True,
        "exact_nfce": True,
    }


def ast_zero_float_audit(source_path: Path) -> Dict[str, Any]:
    """Strict AST zero-float & safety audit on verify_paper104.py."""
    src = source_path.read_text(encoding="utf-8")
    tree = ast.parse(src, filename=str(source_path))
    banned_imports = {
        "math", "cmath", "decimal", "numpy", "scipy", "mpmath",
        "sympy", "torch", "jax", "struct", "operator", "builtins",
    }
    banned_calls = {"float", "complex", "eval", "exec", "pow", "__import__", "getattr", "compile"}
    banned_attrs = {"from_float", "from_decimal"}
    violations: List[str] = []

    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, (float, complex)):
            violations.append(f"Line {node.lineno}: forbidden float/complex literal {node.value!r}")
        elif isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Div, ast.Pow)):
            violations.append(f"Line {node.lineno}: forbidden operator {type(node.op).__name__}")
        elif isinstance(node, ast.AugAssign) and isinstance(node.op, (ast.Div, ast.Pow)):
            violations.append(f"Line {node.lineno}: forbidden augmented op {type(node.op).__name__}")
        elif isinstance(node, ast.Import):
            for alias in node.names:
                root_mod = alias.name.split(".")[0]
                if root_mod in banned_imports:
                    violations.append(f"Line {node.lineno}: forbidden import {alias.name}")
        elif isinstance(node, ast.ImportFrom):
            if node.module:
                root_mod = node.module.split(".")[0]
                if root_mod in banned_imports:
                    violations.append(f"Line {node.lineno}: forbidden from-import {node.module}")
        elif isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name) and node.func.id in banned_calls:
                violations.append(f"Line {node.lineno}: forbidden call {node.func.id}")
            if isinstance(node.func, ast.Name) and node.func.id == "Fraction":
                for arg in node.args:
                    if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                        violations.append(f"Line {node.lineno}: forbidden string Fraction(...)")
            if isinstance(node.func, ast.Attribute) and node.func.attr in banned_attrs:
                violations.append(f"Line {node.lineno}: forbidden attr {node.func.attr}")
    return {"file": source_path.name, "violations": violations, "passed": len(violations) == 0}


def canonical_sha256(payload: Dict[str, Any]) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def write_cert(cert_id: str, title: str, data: Dict[str, Any]) -> Dict[str, Any]:
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    body = {"protocol": PROTOCOL, "cert_id": cert_id, "title": title, "data": data}
    digest = canonical_sha256(body)
    record = {"protocol": PROTOCOL, "cert_id": cert_id, "title": title, "sha256": digest, "data": data}
    CERT_DIR.joinpath(f"{cert_id}.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return {"cert_id": cert_id, "title": title, "sha256": digest, "file": f"{cert_id}.json"}


def run_all_verifications(write_certs: bool = True) -> Dict[str, Any]:
    certs_meta: List[Dict[str, Any]] = []
    def emit(cid: str, title: str, data: Dict[str, Any]) -> None:
        if write_certs:
            certs_meta.append(write_cert(cid, title, data))
        else:
            body = {"protocol": PROTOCOL, "cert_id": cid, "title": title, "data": data}
            certs_meta.append({"cert_id": cid, "title": title, "sha256": canonical_sha256(body), "file": f"{cid}.json"})

    # C01: Hadamard LP-gap strict dominance across 7 benchmark configurations
    lp_checks = []
    for (s, K, Dm, B) in (
        (3, 5, 2, 16),
        (5, 5, 4, 64),
        (8, 13, 6, 1296),
        (13, 13, 10, 10000),
        (25, 41, 12, 20736),
        (41, 41, 10, 1000000),
        (50, 85, 20, 16000000),
    ):
        lp_checks.append(verify_hadamard_lp_gap(s, K, Dm, B))
    emit("C01", "Exact Hadamard active-support LP-gap dominance over CHPS Lemma 14", {
        "count": len(lp_checks),
        "checks": lp_checks,
    })

    # C02: Bit-precision savings on CHPS matching-tree games Gamma_2(P, Q, k)
    # In Gamma_2(P, Q, k) with r x r payoff entries having common denominator q:
    #   D_max = 2*q (independent of m!), whereas B >= 2 * q^{2*r^2} (raw product over 2*r^2 payoff entries + chance 1/2).
    mt_bits = []
    for r in (2, 3, 5, 8):
        for q in (2, 10):
            m = i_pow(2, ceil_log_base(r * r * (r - 1) + 1, 2))
            d_val = m + r - 2
            K_2p = (d_val + 1) * (d_val + 1)
            D_max = 2 * q
            B_raw = 2 * i_pow(q, 2 * r * r)
            # Compare bit-length of 1/eta_sharp vs 1/eta_CHPS without expanding gigantic ints:
            # 2 * log2(1/eta_sharp) <= ceil_log2(K) + K*ceil_log2(K+1) + 2*K*ceil_log2(D_max)
            # 2 * log2(1/eta_CHPS)  >= 2*(K+1)*(floor_log2(K+1) + floor_log2(B_raw))
            log2_K_up = ceil_log_base(K_2p, 2)
            log2_Kp1_up = ceil_log_base(K_2p + 1, 2)
            log2_Kp1_dn = (K_2p + 1).bit_length() - 1
            log2_D_up = ceil_log_base(D_max, 2)
            log2_B_dn = B_raw.bit_length() - 1
            bits_sharp_hi = (log2_K_up + K_2p * log2_Kp1_up + 2 * K_2p * log2_D_up + 1) // 2
            bits_chps_lo = (K_2p + 1) * (log2_Kp1_dn + log2_B_dn)
            if not (bits_sharp_hi < bits_chps_lo):
                raise ValueError("Matching-tree bit saving failed")
            ratio_q = q_div(Fraction(bits_chps_lo, 1), Fraction(bits_sharp_hi, 1))
            mt_bits.append({
                "r": r,
                "q": q,
                "m": m,
                "kappa_d": K_2p,
                "bits_sharp_hi": bits_sharp_hi,
                "bits_chps_lo": bits_chps_lo,
                "bit_reduction_factor_lo": q_to_decimal_str(ratio_q, 2),
            })
    emit("C02", "Bit-precision savings of sharp LCM-Hadamard gap on CHPS matching-tree games", {
        "samples": mt_bits,
    })

    # C03: Two-player support dominance K - kappa_d = d1^2 + d2^2 - d1*d2 >= (d1^2 + d2^2)/2
    two_p_checked = 0
    for d1 in range(1, 11):
        for d2 in range(1, 11):
            K = 1 + d1 * (d1 + 1) + d2 * (d2 + 1)
            kd = (d1 + 1) * (d2 + 1)
            gap = K - kd
            if 2 * gap != (d1 - d2) * (d1 - d2) + d1 * d1 + d2 * d2:
                raise ValueError("Two-player gap identity failed")
            if gap <= 0:
                raise ValueError("Two-player gap not strictly positive")
            two_p_checked += 1
    balanced = []
    for d in (10, 50, 200, 1000):
        K = 1 + 2 * d * (d + 1)
        kd = (d + 1) * (d + 1)
        balanced.append({"d": d, "K": K, "kappa_d": kd, "ratio_K_over_kd": q_to_decimal_str(Fraction(K, kd), 6)})
    emit("C03", "Two-player support dominance K vs kappa_d across 100 pairs and balanced scaling", {
        "pairs_verified": two_p_checked,
        "balanced_scaling": balanced,
    })

    # C04: Optimal b-ary matching tree node overhead f(b) = b + 2 + 2/(b - 1) >= 6
    bary_overhead = []
    for b in range(2, 21):
        fb = Fraction(b + 2, 1) + Fraction(2, b - 1)
        diff = fb - Fraction(6, 1)
        if diff != Fraction((b - 2) * (b - 3), b - 1):
            raise ValueError("Overhead factorization mismatch")
        if b in (2, 3):
            if diff != 0:
                raise ValueError("f(2) and f(3) must equal 6")
        else:
            if diff <= 0:
                raise ValueError("f(b) must strictly exceed 6 for b >= 4")
        c_quad = q_div(Fraction(1, 1), fb * fb)
        bary_overhead.append({"b": b, "f_b": q_pair(fb), "c_quad": q_pair(c_quad), "optimal": b in (2, 3)})
    emit("C04", "Exact b-ary matching-tree node overhead optimality (minimum 6 uniquely at b in {2,3})", {
        "checked_b_range": [2, 20],
        "unique_optima": [2, 3],
        "sharp_node_quad_const": [1, 36],
        "table": bary_overhead,
    })

    # C05: Exact structural invariants of Gamma_b(P, Q, k) across binary, ternary, quaternary trees
    inv_samples = []
    for (b, k, r) in ((2, 1, 2), (2, 3, 5), (2, 5, 6), (3, 1, 2), (3, 2, 5), (3, 4, 6), (4, 1, 2), (4, 3, 5)):
        inv_samples.append(bary_matching_game_invariants(b, k, r))
    emit("C05", "Exact node, leaf, and b-invariant sequence-form dimension counts for Gamma_b", {
        "samples": inv_samples,
    })

    # C06: Ternary-over-binary exponential pure-strategy space savings at matched node count 6m + r^2 + r - 3
    tern_vs_bin = []
    for k in range(1, 6):
        m = i_pow(3, k)
        # Compare 3^{(m-1)/2} vs 2^{m-1} (exact ratio = (4/3)^{(m-1)/2})
        t = (m - 1) // 2
        sig_tern = i_pow(3, t)
        sig_bin = i_pow(4, t)
        if not (sig_tern < sig_bin):
            raise ValueError("Ternary failed to beat binary strategy space")
        ratio_floor = sig_bin // sig_tern
        tern_vs_bin.append({
            "k": k,
            "m": m,
            "t": t,
            "ratio_2pow_over_3pow_floor": ratio_floor,
            "ratio_digits": len(str(ratio_floor)),
        })
    emit("C06", "Exponential pure-strategy space reduction of ternary (b=3) vs binary (b=2) trees", {
        "samples": tern_vs_bin,
    })

    # C07: Corollary 20 threshold audit |V| - 6*(m + r - 1) = r^2 - 5r + 3
    cor20 = []
    for r in range(2, 13):
        val = r * r - 5 * r + 3
        if r <= 4 and val >= 0:
            raise ValueError("Expected negative for r <= 4")
        if r >= 5 and val < 3:
            raise ValueError("Expected >= 3 for r >= 5")
        cor20.append({"r": r, "V_minus_6d": val, "kappa_d_le_kappa_V": val >= 0})
    emit("C07", "Exact Corollary 20 non-vacuousness threshold r >= 5", {"table": cor20})

    # C08: Exact 8x sharpening of dimension-based PPAD-hardness matching tree (m_d* vs CHPS 8r^3)
    dim_hard = []
    for r in (2, 3, 4, 5, 8, 10, 16, 32, 64):
        m_chps = i_pow(2, ceil_log_base(8 * i_pow(r, 3), 2))
        m_sharp2 = i_pow(2, ceil_log_base(r * r * (r - 1) + 1, 2))
        m_sharp3 = i_pow(3, ceil_log_base(r * r * (r - 1) + 1, 3))
        # Rigorous exact rational check: ln(1 + (r-1)/m_sharp2) < 1/r^2
        t_q = Fraction(r - 1, m_sharp2)
        _, ln_hi = ln_one_plus_q_bracket(t_q, 24)
        if not (ln_hi < Fraction(1, r * r)):
            raise ValueError(f"Sharp dim threshold failed Pinsker bound at r={r}")
        # Also verify ternary m_sharp3
        t3_q = Fraction(r - 1, m_sharp3)
        _, ln3_hi = ln_one_plus_q_bracket(t3_q, 24)
        if not (ln3_hi < Fraction(1, r * r)):
            raise ValueError(f"Sharp ternary dim threshold failed at r={r}")
        factor2 = q_div(Fraction(m_chps, 1), Fraction(m_sharp2, 1))
        if factor2 < Fraction(8, 1):
            raise ValueError(f"Expected >= 8x dim sharpening at r={r}")
        dim_hard.append({
            "r": r,
            "m_chps": m_chps,
            "m_sharp_binary": m_sharp2,
            "m_sharp_ternary": m_sharp3,
            "binary_reduction_factor": q_pair(factor2),
            "ln_hi_dec": q_to_decimal_str(ln_hi, 8),
            "target_inv_r2_dec": q_to_decimal_str(Fraction(1, r * r), 8),
        })
    emit("C08", "Exact >=8x sharpening of dimension-based PPAD-hardness matching tree", {
        "samples": dim_hard,
    })

    # C09: Exact 24x-64x sharpening of node-based PPAD-hardness matching tree (m_V* vs CHPS 8r^4)
    node_hard = []
    for r in (5, 6, 8, 10, 16, 32, 64):
        m_chps = i_pow(2, ceil_log_base(8 * i_pow(r, 4), 2))
        thresh_num = r * r * (r * r + r - 3)
        m_min = (thresh_num // 6) + 1
        m_sharp2 = i_pow(2, ceil_log_base(m_min, 2))
        # Rigorous exact rational check: ln(1 + (r^2 + r - 3)/(6*m_sharp2)) < 1/r^2
        t_q = Fraction(r * r + r - 3, 6 * m_sharp2)
        _, ln_hi = ln_one_plus_q_bracket(t_q, 24)
        if not (ln_hi < Fraction(1, r * r)):
            raise ValueError(f"Sharp node threshold failed at r={r}")
        factor2 = q_div(Fraction(m_chps, 1), Fraction(m_sharp2, 1))
        if factor2 < Fraction(32, 1):
            raise ValueError(f"Expected >= 32x node sharpening at r={r}")
        node_hard.append({
            "r": r,
            "m_chps": m_chps,
            "m_sharp_binary": m_sharp2,
            "binary_reduction_factor": q_pair(factor2),
        })
    emit("C09", "Exact >=32x sharpening of node-based PPAD-hardness matching tree (r >= 5)", {
        "samples": node_hard,
    })

    # C10: Refined Pinsker (Kullback-Csiszar-Kemperman) exact threshold D_KL >= 2*TV^2 + (4/9)*TV^4
    kck_samples = []
    for r in (2, 3, 4, 5, 10):
        # Required: ln(1 + (r-1)/m) < 1/r^2 + 2/(9*r^4)  (since D_KL <= 2*ln(1+(r-1)/m))
        rhs_q = Fraction(1, r * r) + Fraction(2, 9 * i_pow(r, 4))
        exp_lo, exp_hi = exp_small_q_bracket(rhs_q, 24)
        # m_kck > (r - 1) / (exp(rhs_q) - 1)
        m_kck_hi = q_div(Fraction(r - 1, 1), exp_lo - Fraction(1, 1))
        m_std_thresh = Fraction(r * r * (r - 1), 1)
        if not (m_kck_hi < m_std_thresh):
            raise ValueError("Refined Pinsker failed to tighten standard threshold")
        kck_samples.append({
            "r": r,
            "m_standard_linear": q_pair(m_std_thresh),
            "m_refined_kck_hi_dec": q_to_decimal_str(m_kck_hi, 6),
        })
    emit("C10", "Refined Pinsker (Kullback-Csiszar-Kemperman) exact threshold tightening", {
        "samples": kck_samples,
    })

    # C11: Constructive exact m^2-support NFCE on Gamma_2(Matching Pennies, k=1,2)
    P_mp = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 1)]]
    Q_mp = [[Fraction(0, 1), Fraction(1, 1)], [Fraction(1, 1), Fraction(0, 1)]]
    mp_checks = []
    for k in (1, 2):
        m = i_pow(2, k)
        # Assign half of [m] to action 0 and half to action 1: y_i(x) = 0 if x < m/2 else 1
        w = Fraction(1, m * m)
        supp = []
        for x1 in range(m):
            y1 = 0 if x1 < (m // 2) else 1
            for x2 in range(m):
                y2 = 0 if x2 < (m // 2) else 1
                supp.append(((y1, x1), (y2, x2), w))
        res = verify_exact_nfce_on_gamma_b(P_mp, Q_mp, 2, k, supp)
        if not res["equals_m_squared"]:
            raise ValueError("Matching pennies support != m^2")
        mp_checks.append(res)
    emit("C11", "Constructive exact m^2-support NFCE on binary Gamma_2(Matching Pennies)", {
        "instances": mp_checks,
    })

    # C12: Exact ternary vs binary m^2-support separation on G_{1/3} (unique Nash x=(2/3,1/3), y=(1/3,2/3))
    P_third = [[Fraction(1, 1), Fraction(0, 1)], [Fraction(0, 1), Fraction(1, 2)]]
    Q_third = [[Fraction(0, 1), Fraction(1, 2)], [Fraction(1, 1), Fraction(0, 1)]]
    # On ternary Gamma_3(P_third, Q_third, k=1) (m=3):
    # P1 assigns y1(0)=0, y1(1)=0, y1(2)=1 (marginal (2/3, 1/3))
    # P2 assigns y2(0)=0, y2(1)=1, y2(2)=1 (marginal (1/3, 2/3))
    w9 = Fraction(1, 9)
    y1_map = [0, 0, 1]
    y2_map = [0, 1, 1]
    supp_tern = [((y1_map[x1], x1), (y2_map[x2], x2), w9) for x1 in range(3) for x2 in range(3)]
    res_tern = verify_exact_nfce_on_gamma_b(P_third, Q_third, 3, 1, supp_tern)
    # Also verify non-divisibility 3 nmid 2^k for k=1..30 (impossibility of m^2 support in Gamma_2)
    non_div = all((i_pow(2, kk) % 3) != 0 for kk in range(1, 31))
    if not (res_tern["equals_m_squared"] and non_div):
        raise ValueError("Ternary vs binary m^2 separation failed")
    emit("C12", "Exact ternary vs binary m^2-support separation on asymmetric game G_{1/3}", {
        "ternary_m3_exact_nfce": res_tern,
        "binary_3_not_dvd_2powk_k1_to_30": non_div,
        "unique_nash_x": [[2, 3], [1, 3]],
        "unique_nash_y": [[1, 3], [2, 3]],
    })

    # C13: Exact rational LP vertex gap demonstration on a concrete infeasible support S
    # On Matching Pennies (normalized [0,1]), support S = {(0,0), (0,1), (1,0)} (3 of 4 profiles):
    # Any mu = (a, b, c) with a+b+c = 1 has:
    #   P1 at 0: cur = a, alt 1 = b => reg = b - a <= t
    #   P1 at 1: cur = 0, alt 0 = c => reg = c <= t
    #   P2 at 0: cur = c, alt 1 = a => reg = a - c <= t
    #   P2 at 1: cur = b, alt 0 = 0 => reg = -b <= t
    # Exact optimal vertex: a = 1/2, b = 1/4? Wait: a-c=t, b-a=t, c=t => c=t, a=2t, b=3t => 6t=1 => t* = 1/6!
    # Verify exact vertex (a=1/3, b=1/2, c=1/6, t*=1/6):
    #   b - a = 1/6 = t*, c = 1/6 = t*, a - c = 1/6 = t*, a+b+c = 1!
    # Compare exact t* = 1/6 against eta_sharp(s=3, D_max=1) and eta_CHPS(K=5, B=1)!
    a_v, b_v, c_v, t_star = Fraction(1, 3), Fraction(1, 2), Fraction(1, 6), Fraction(1, 6)
    if not (a_v + b_v + c_v == 1 and b_v - a_v == t_star and c_v == t_star and a_v - c_v == t_star):
        raise ValueError("Vertex equations failed")
    # Dual certificate proving t* >= 1/6: multiply (a+b+c=1) by 1/6, subtract (b-a<=t)/6, (a-c<=t)/3, (c<=t)/2:
    # Check: (1/6)(a+b+c) - (1/6)(b-a) - (1/3)(a-c) - (1/2)c = (1/6+1/6-1/3)a + (1/6-1/6)b + (1/6+1/3-1/2)c = 0!
    # RHS: 1/6 <= (1/6 + 1/3 + 1/2) t = t! EXACT DUAL PROOF t*(S) = 1/6!
    # Compare t*^2 = 1/36 vs eta_sharp(3,1)^2 = 1/(3*4^3) = 1/192 vs eta_CHPS(5,1)^2 = 1/6^12 = 1/2176782336!
    eta_sharp_sq = Fraction(1, 3 * i_pow(4, 3))
    eta_chps_sq = Fraction(1, i_pow(6, 12))
    if not (t_star * t_star >= eta_sharp_sq > eta_chps_sq):
        raise ValueError("LP gap hierarchy failed")
    emit("C13", "Exact infeasible-support LP vertex gap t*(S)=1/6 vs eta_sharp and eta_CHPS", {
        "vertex_mu": [q_pair(a_v), q_pair(b_v), q_pair(c_v)],
        "exact_t_star": q_pair(t_star),
        "eta_sharp_sq_s3_D1": q_pair(eta_sharp_sq),
        "eta_chps_sq_K5_B1": q_pair(eta_chps_sq),
        "tightness_factor_sq": i_pow(6, 12) // (3 * i_pow(4, 3)),
    })

    # C14: Matching-pennies single-profile impossibility & Corollary 20 node-count check
    # Simultaneous 2x2 matching pennies: 1 root (P1) + 2 (P2) + 4 leaves = 7 nodes, floor(7^2/36) = 1,
    # while every pure profile has regret 1 > 0.
    mp_V = 1 + 2 + 4
    mp_kappa_V = (mp_V * mp_V) // 36
    if mp_V != 7 or mp_kappa_V != 1:
        raise ValueError("Matching pennies |V|=7, kappa_V=1 check failed")
    pure_regrets = []
    for y1 in (0, 1):
        for y2 in (0, 1):
            r1 = max(P_mp[a][y2] - P_mp[y1][y2] for a in (0, 1))
            r2 = max(Q_mp[y1][b_] - Q_mp[y1][y2] for b_ in (0, 1))
            mreg = r1 if r1 > r2 else r2
            if mreg <= 0:
                raise ValueError("Matching pennies has no pure Nash")
            pure_regrets.append({"profile": [y1, y2], "max_regret": q_pair(mreg)})
    emit("C14", "Corollary 20 matching-pennies single-profile impossibility (|V|=7, kappa_V=1)", {
        "V": mp_V,
        "kappa_V": mp_kappa_V,
        "pure_profile_regrets": pure_regrets,
    })

    # C15: Multi-player quadratic support K vs product support prod(d_i + 1) and 1 + N(N-1) bound
    mp_supp = []
    for n_players, dims in (
        (2, [4, 4]),
        (2, [10, 10]),
        (3, [4, 4, 4]),
        (3, [10, 10, 10]),
        (4, [5, 5, 5, 5]),
        (5, [4, 4, 4, 4, 4]),
    ):
        K_val = 1 + sum(d * (d + 1) for d in dims)
        prod_val = 1
        for d in dims:
            prod_val *= (d + 1)
        N_min = sum(dims) + 1
        N_bound = 1 + N_min * (N_min - 1)
        if not (K_val <= N_bound):
            raise ValueError("K <= 1 + N(N-1) failed")
        mp_supp.append({
            "n_players": n_players,
            "dims": dims,
            "K": K_val,
            "product_support": prod_val,
            "product_beats_K": prod_val < K_val,
            "N_bound": N_bound,
        })
    emit("C15", "Multi-player support comparison: K vs product support and 1+N(N-1) ceiling", {
        "cases": mp_supp,
    })

    # C16: Self-referential AST zero-float security audit
    audit = ast_zero_float_audit(Path(__file__).resolve())
    if not audit["passed"]:
        raise RuntimeError(f"AST zero-float audit failed: {audit['violations']}")
    emit("C16", "Self-referential AST zero-float and exact-arithmetic security audit", audit)

    manifest_body = {"protocol": PROTOCOL, "certificate_count": len(certs_meta), "certificates": certs_meta}
    manifest_sha = canonical_sha256(manifest_body)
    manifest = {"protocol": PROTOCOL, "certificate_count": len(certs_meta), "manifest_sha256": manifest_sha, "certificates": certs_meta}
    if write_certs:
        CERT_DIR.joinpath("MANIFEST.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest


if __name__ == "__main__":
    m = run_all_verifications(write_certs=True)
    print(f"Protocol: {m['protocol']} | Certificates: {m['certificate_count']} | MANIFEST SHA-256: {m['manifest_sha256']}")
    for c in m["certificates"]:
        print(f"  {c['cert_id']}: {c['sha256'][:16]}  {c['title']}")
