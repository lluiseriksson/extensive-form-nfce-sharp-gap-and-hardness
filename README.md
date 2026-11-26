# Exponential Bit-Complexity Tightening, Optimal $b$-ary Matching Trees, and Exact Sharp Support Thresholds for Normal-Form Correlated Equilibria in Extensive-Form Games

**Author:** Lluis Eriksson  
**Target Preprint:** V. Cheval, F. Horn, S. Paul, and M. Shirmohammadi, *Computing Normal-Form Correlated Equilibria in Extensive-Form Games is in PPAD* ([arXiv:2611.34897v1](https://arxiv.org/abs/2611.34897))  
**Licenses:** MIT (code, Lean 4 formalization, tests, certificates) / CC-BY-4.0 (manuscript & figures)  
**AI Disclosure:** Authored by Lluis Eriksson with AI-assisted formal verification, exact-arithmetic software generation, and mathematical drafting (Google Antigravity).

## Main Results

1. **Theorem 1 — Active-Support LCM–Hadamard LP-Gap Tightening & Two-Player Support Dominance:**
   - Tightens the uniform rational LP reweighting gap (Lemma 14 / Theorem 6) from $((K+1)B)^{-(K+1)}$ to $(\sqrt{K}(K+1)^{K/2}D_{\max}^K)^{-1}$, saving more than $\frac{K}{2}\log_2(K+1) + K\log_2(B/D_{\max})$ bits of weak-Nash oracle precision ($>30\times$ fewer bits on matching-tree instances at $r=8, q=10$).
   - Proves exact two-player support dominance $K - \kappa_d = d_1^2 + d_2^2 - d_1 d_2 \ge \frac{1}{2}(d_1^2+d_2^2)$ ($2\times$ reduction along $d_1=d_2$).
2. **Theorem 2 — Optimal $b$-ary Matching Trees & Sharp $1/36$ Node-Quadratic Constant:**
   - Proves sequence-form dimensions $d_1 = d_2 = m + r - 2$ are invariant of branching factor $b \ge 2$ while node overhead $f(b) = b + 2 + \frac{2}{b-1} = 6 + \frac{(b-2)(b-3)}{b-1}$ achieves its unique integer minimum $6$ if and only if $b \in \{2, 3\}$.
   - Certifies sharpness of Corollary 20's $1/36$ constant across all $b$-ary trees, while ternary trees ($b=3$) match $|V| = 6m+r^2+r-3$ with exponentially smaller pure-strategy space $r \cdot 3^{(m-1)/2} \ll r \cdot 2^{m-1}$ ($>10^{15}\times$ smaller at $m=243$).
3. **Theorem 3 — $8\times$–$64\times$ Hardness Tree-Size Reduction & Exact $m^2$-Support Dichotomy:**
   - Cuts PPAD-hardness matching trees by $\ge 8\times$ (dimension-based: $m > r^2(r-1)$ vs $8r^3$) and $32\times$–$64\times$ (node-based: $m > r^2(r^2+r-3)/6$ vs $8r^4$), with refined Kullback–Csiszár–Kemperman Pinsker tightening.
   - Proves an exact minimum-support dichotomy: $|\operatorname{supp}(\mu)| = m^2$ is attainable in $\Gamma_b(P,Q,k)$ if and only if $(P,Q)$ has an exact Nash equilibrium with probabilities in $\frac{1}{m}\mathbb{Z}$, separating ternary ($b=3$) from binary ($b=2$) trees on the asymmetric game $G_{1/3}$.

## Reproducibility

```bash
cd lean && lake build
python verification/verify_paper104.py
pytest -q tests/test_verify_paper104.py
python scripts/generate_figures.py
cd paper && pdflatex -halt-on-error main.tex && pdflatex -halt-on-error main.tex
```
