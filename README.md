# An Improved Lower Bound for the 4-Uniform Hypergraph Ramsey Number: $R(6, 6; 4) \ge 621$

**Author**: Katsutoshi Hashimoto (Independent Researcher, Japan — `ramuza0113@gmail.com` · [ORCID: `0009-0009-8292-5085`](https://orcid.org/0009-0009-8292-5085))  
**Date**: November 23, 2026  
**Preprint / Note**: [`paper/main.pdf`](paper/main.pdf) ([`paper/main.tex`](paper/main.tex))  
**Main Theorem**: $R(6, 6; 4) \ge 621$ (explicit $\mathrm{PSL}(2, 619)$-invariant 2-coloring $F_{620}$ on $620$ points, $\mathbb{P}^1(\mathbb{F}_{619})$)

---

## 1. Historical Context & Improvement Over Known Bounds

Let $R(k, l; t)$ denote the smallest integer $N$ such that every 2-coloring of the $t$-subsets of an $N$-element set contains either a $k$-subset with all $\binom{k}{t}$ subsets of color $0$, or an $l$-subset with all $\binom{l}{t}$ subsets of color $1$.

For the diagonal 4-uniform Ramsey number $R(6, 6; 4)$, the published lower bounds progressed as follows:

| Source | Year / Date | Lower Bound | Order $n$ | Automorphism Group |
| :--- | :--- | :---: | :---: | :--- |
| Radziszowski (*Dynamic Survey DS1*, Rev. #18) | Apr 24, 2026 | $133$ | $132$ | Classical / Recursive |
| Kerem Özdemir (Zenodo `10.5281/zenodo.17456614`) | Oct 2026 | $317$ | $316$ | $\mathrm{PGL}(2, 317)$ / Projective |
| Christian Lysenstøen (`arXiv:2611.25143v1`) | Nov 18, 2026 | $601$ | $600$ | $\mathrm{PGL}(2, 599)$ ($E_{600}$, $100$ classes) |
| **This Witness ($F_{620}$)** | **Nov 23, 2026** | **$621$** | **$620$** | **$\mathrm{PSL}(2, 619)$ ($130$ narrow classes)** |

### Key Mathematical Insight
In `arXiv:2611.25143v1`, Lysenstøen searched $\mathrm{PGL}(2, q)$-invariant colorings for $R(6, 6; 4)$ and skipped from $q = 599$ to $q = 701$, while only applying the index-2 subgroup $\mathrm{PSL}(2, q)$ ($q \equiv 3 \pmod 4$) to $R(5, 6; 4)$ ($q = 199$).

Because $619$ is prime and $619 \equiv 3 \pmod 4$:
1. $-1$ is a quadratic non-residue in $\mathbb{F}_{619}$, so $\mathrm{PSL}(2, 619)$ remains **3-homogeneous** on all $\binom{620}{3} = 39,529,340$ unordered 3-subsets of $\mathbb{P}^1(\mathbb{F}_{619}) = \mathbb{F}_{619} \cup \{\infty\}$. Every 6-subset of $\mathbb{P}^1(\mathbb{F}_{619})$ is therefore mapped by an element of $\mathrm{PSL}(2, 619)$ onto a 6-subset containing $\{\infty, 0, 1\}$.
2. Meanwhile, for cross-ratios $\lambda \in \mathbb{F}_{619} \setminus \{0, 1\}$ such that both $-\lambda$ and $\lambda - 1$ are quadratic residues in $\mathbb{F}_{619}^\times$, the 6-element $\mathrm{PGL}(2, 619)$ cross-ratio class splits into **two** 3-element $\mathrm{PSL}(2, 619)$ classes $\{\lambda, \frac{1}{1-\lambda}, \frac{\lambda-1}{\lambda}\}$ and $\{\frac{1}{\lambda}, 1-\lambda, \frac{\lambda}{\lambda-1}\}$, increasing the number of orbit variables from $104$ ($\mathrm{PGL}$) to **$130$ ($\mathrm{PSL}$)** ($62$ classes in color `0`, $68$ classes in color `1`).

---

## 2. Explicit Definition of the Coloring $F_{620}$

Identify $\mathbb{P}^1(\mathbb{F}_{619})$ with $\{0, 1, \dots, 618, \infty\}$ where $\infty$ is ordered last ($619$). For any 4-subset $\{a, b, c, d\}$ with $a < b < c < d$:
$$x = \begin{cases} \dfrac{(a - c)(b - d)}{(a - d)(b - c)} \bmod 619 & \text{if } d < 619, \\[8pt] \dfrac{a - c}{b - c} \bmod 619 & \text{if } d = 619, \end{cases} \qquad \Delta = (b - a)(c - a)(c - b) \bmod 619.$$
Let `table` be the 619-character binary string in `R664_620_points_rule.json` (`SHA-256: 6658e8cfc640c17e14b425f5b0a19bd03017ed1aba7a035752df5550199467c6`). Then the color of $\{a, b, c, d\}$ is `table[x]` if $\Delta$ is a quadratic residue modulo $619$, and `table[1/x mod 619]` otherwise.

---

## 3. Independent Clean-Room Verification (~2.3 Seconds)

`verify_r664_psl.rs` is written completely independently of the search solver (`rust_turbo_psl_pgl_r664.rs`), using zero shared code and zero lookup-shortcut identities:

```powershell
rustc -C opt-level=3 -C target-cpu=native verify_r664_psl.rs -o verify_r664_psl.exe
.\verify_r664_psl.exe R664_620_points_rule.json
```

It executes 6 independent computational checks:
1. **Check 1**: Verifies $q = 619$ is prime and $619 \equiv 3 \pmod 4$.
2. **Check 2**: Verifies all $12$ $\mathrm{SL}(2, 619)$ ($\det \equiv 1 \pmod{619}$) stabilizer/coset maps yield identical colors on 4-subsets.
3. **Check 3**: **Exhaustively** constructs an explicit $\det = 1$ matrix in $\mathrm{SL}(2, 619)$ mapping $\{u, v, w\} \to \{\infty, 0, 1\}$ for **all $\binom{620}{3} = 39,529,340$ unordered 3-subsets** of $\mathbb{P}^1(\mathbb{F}_{619})$.
4. **Check 4**: Verifies $\mathrm{color}(M(E)) = \mathrm{color}(E)$ on $1,000,000$ random pairs $(E, M) \in \binom{\mathbb{P}^1(\mathbb{F}_{619})}{4} \times \mathrm{SL}(2, 619)$.
5. **Check 5**: **Exhaustively** checks **all $\binom{617}{3} = 38,957,380$ 6-subsets containing $\{\infty, 0, 1\}$** (covering all $\binom{620}{6} = 79,532,803,405,740$ 6-subsets by Checks 3 & 4): **zero** monochromatic 6-subsets in either color (`1`-edge count strictly in `[1, 14]` for every 6-subset).
6. **Check 6**: Directly evaluates $500,000$ arbitrary random 6-subsets in $\{0, \dots, 619\}$ without symmetry reduction: **zero** monochromatic 6-subsets.

---

## 4. Citation

```bibtex
@misc{hashimoto2026r664,
  author       = {Katsutoshi Hashimoto},
  title        = {An Improved Lower Bound for the Hypergraph Ramsey Number {$R(6,6;4)$}},
  year         = {2026},
  month        = nov,
  note         = {Explicit $\mathrm{PSL}(2,619)$-invariant witness proving $R(6,6;4) \ge 621$},
  howpublished = {\url{https://github.com/ramuza0113-sketch/ramsey-r664-621}}
}
```

