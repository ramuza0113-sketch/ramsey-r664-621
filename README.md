# Improved Constructive Lower Bounds for Hypergraph Ramsey Numbers (`v1.2.0`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24462206.svg)](https://doi.org/10.5281/zenodo.24462206)

**Author**: Katsutoshi Hashimoto (Independent Researcher, Japan — `ramuza0113@gmail.com` · [ORCID: `0009-0009-8292-5085`](https://orcid.org/0009-0009-8292-5085))  
**Date**: November 2026 (`v1.2.0`)  
**Concept DOI (always resolves to latest version)**: [`10.5281/zenodo.24462206`](https://doi.org/10.5281/zenodo.24462206) (`v1.2.0`: [`10.5281/zenodo.24587745`](https://doi.org/10.5281/zenodo.24587745), `v1.1.0`: [`10.5281/zenodo.24474219`](https://doi.org/10.5281/zenodo.24474219), `v1.0.0`: [`10.5281/zenodo.24462207`](https://doi.org/10.5281/zenodo.24462207))  
**Manuscripts**:
- **Part II (`v1.2.0`)**: [`paper_part2/main.pdf`](paper_part2/main.pdf) ([`paper_part2/main.tex`](paper_part2/main.tex)) — *Constructive Lower Bounds for Multicolour and Off-Diagonal Hypergraph Ramsey Numbers* (16 explicit constructions)
- **Part I (`v1.1.0`)**: [`paper/main.pdf`](paper/main.pdf) ([`paper/main.tex`](paper/main.tex)) — *Improved Constructive Lower Bounds for Small Hypergraph Ramsey Numbers*

---

## 1. Summary of Explicit Constructions (`v1.2.0` + `v1.1.0`: 18 Explicit Parameter Families)

Let $R(k_1, \dots, k_r; t)$ denote the smallest integer $n$ such that every $r$-colouring of the $t$-subsets of an $n$-element set contains, for some colour $i$, a $k_i$-subset all of whose $t$-subsets have colour $i$, and write $R_r(k; t)$ when $k_1 = \dots = k_r = k$.

### A. Part II (`v1.2.0`): 16 Explicit Multicolour & Off-Diagonal Constructions (`witnesses_part2/`)

| Hypergraph Ramsey Number | Dynamic Survey DS1 (Apr 2026) | Recent 2026 Preprints | **New Bound (`v1.2.0`)** | Order $n$ | Orbits | Group & Witness File |
| :--- | :---: | :---: | :---: | :---: | :---: | :--- |
| **$R(5, 5; 3)$** | $88$ | $99$; $101$ (Lysenstøen, Nov 2026) | **$\mathbf{110}$** | $109$ | $1,983$ | $\mathbb{Z}_{106} + 3\infty$ ([`R553_109_points_rule.json`](witnesses_part2/R553_109_points_rule.json)) |
| **$R(6, 6; 3)$** | — | — | **$\mathbf{308}$** | $307$ | $103$ | $\mathrm{AGL}^+(1, 307)$ ([`R663_307_points_rule.json`](witnesses_part2/R663_307_points_rule.json)) |
| **$R(5, 7; 3)$** | — | — | **$\mathbf{284}$** | $283$ | $95$ | $\mathrm{AGL}^+(1, 283)$ ([`R573_283_points_rule.json`](witnesses_part2/R573_283_points_rule.json)) |
| **$R(5, 6; 3)$** | — | — | **$\mathbf{156}$** | $155$ | $71$ | $G(155, 3)$ ([`R563_155_points_rule.json`](witnesses_part2/R563_155_points_rule.json)) |
| **$R(4, 8; 3)$** | — | — | **$\mathbf{164}$** | $163$ | $55$ | $\mathrm{AGL}^+(1, 163)$ ([`R483_163_points_rule.json`](witnesses_part2/R483_163_points_rule.json)) |
| **$R(4, 7; 3)$** | — | — | **$\mathbf{108}$** | $107$ | $35$ | $G(107, 3)$ ([`R473_107_points_rule.json`](witnesses_part2/R473_107_points_rule.json)) |
| **$R(4, 4, 4; 3)$** | $79$ | $84$ (Yang); $100$ (`v1.1.0`) | **$\mathbf{103}$** | $102$ | $1,758$ | $\mathbb{Z}_{98} + 4\infty$ ([`R4443_102_points_rule.json`](witnesses_part2/R4443_102_points_rule.json)) |
| **$R(4, 4, 5; 3)$** | — | — | **$\mathbf{164}$** | $163$ | $55$ | $\mathrm{AGL}^+(1, 163)$ ([`R4453_163_points_rule.json`](witnesses_part2/R4453_163_points_rule.json)) |
| **$R(4, 5, 5; 3)$** | — | — | **$\mathbf{272}$** | $271$ | $91$ | $\mathrm{AGL}^+(1, 271)$ ([`R4553_271_points_rule.json`](witnesses_part2/R4553_271_points_rule.json)) |
| **$R_4(4; 3)$** | — | — | **$\mathbf{381}$** | $380$ | $1,152$ | $G(379, 255) + 1\infty$ ([`R44443_380_points_rule.json`](witnesses_part2/R44443_380_points_rule.json)) |
| **$R_5(4; 3)$** | — | — | **$\mathbf{1,260}$** | $1,259$ | $419$ | $\mathrm{AGL}^+(1, 1259)$ ([`R444443_1259_points_rule.json`](witnesses_part2/R444443_1259_points_rule.json)) |
| **$R_6(4; 3)$** | — | — | **$\mathbf{3,780}$** | $3,779$ | $1,259$ | $\mathrm{AGL}^+(1, 3779)$ ([`R4444443_3779_points_rule.json`](witnesses_part2/R4444443_3779_points_rule.json)) |
| **$R_7(4; 3)$** | — | — | **$\mathbf{5,232}$** | $5,231$ | $1,743$ | $\mathrm{AGL}^+(1, 5231)$ ([`R44444443_5231_points_rule.json`](witnesses_part2/R44444443_5231_points_rule.json)) |
| **$R_3(5; 4)$** | — | — | **$\mathbf{969}$** | $968$ | $203$ | $\mathrm{PSL}(2, 967)$ ([`R5554_968_points_rule.json`](witnesses_part2/R5554_968_points_rule.json)) |
| **$R_4(5; 4)$** | — | — | **$\mathbf{3,805}$** | $3,804$ | $792$ | $\mathrm{PSL}(2, 3803)$ ([`R55554_3804_points_rule.json`](witnesses_part2/R55554_3804_points_rule.json)) |
| **$R_5(5; 4)$** | — | — | **$\mathbf{9,439}$** | $9,438$ | $1,966$ | $\mathrm{PSL}(2, 9437)$ ([`R555554_9438_points_rule.json`](witnesses_part2/R555554_9438_points_rule.json)) |

**Selected Product & Stepping-Up Corollaries (`v1.2.0`)**:
- **$R(5, 5, 5; 3) \ge 11,882$**, **$R_4(5; 3) \ge 141,158,162$**, and **$R_r(5; 3) \ge 109^{2^{r-2}} + 1$** ($r \ge 3$) via Bruce–Budden–Hiller product from $R(5, 5; 3) \ge 110$
- **$R(9, 9; 4) > 2^{109}$** and **$R(11, 11; 4) > 2^{307}$** via Erdős–Hajnal stepping-up
- **$R_6(5; 4) > 2^{102}$**, **$R_7(5; 4) > 2^{380}$**, **$R_8(5; 4) > 2^{1,259}$**, **$R_9(5; 4) > 2^{3,779}$**, **$R_{10}(5; 4) > 2^{5,231}$**, and **$R_6(6; 5) > 2^{968}$**, **$R_7(6; 5) > 2^{3,804}$**, **$R_8(6; 5) > 2^{9,438}$** via Jartoux–Keller–Smorodinsky–Yuditsky stepping-up

---

### B. Part I (`v1.1.0`): Projective-Line $4$-Uniform & Base $3$-Uniform Constructions

| Hypergraph Ramsey Number | Dynamic Survey DS1 (Apr 2026) | Recent 2026 Bounds | **Bound in `v1.1.0`** | Witness & Symmetry Group |
| :--- | :---: | :---: | :---: | :--- |
| **$R(6, 6; 4)$** | $133$ | $601$ (Lysenstøen, Nov 2026) | **$\mathbf{685}$** | $F_{684}$ on $\mathbb{F}_{683} \cup \{\infty\}$ ($\mathrm{PSL}(2, 683)$, [`R664_684_points_rule.json`](R664_684_points_rule.json)) |
| **$R(5, 7; 4)$** | $133$ | $401$ (Lysenstøen, 2026a); $859$ (Lysenstøen, 2026b)* | **$\mathbf{711}$** | $G_{710}$ on $\mathbb{F}_{709} \cup \{\infty\}$ ($\mathrm{PGL}(2, 709)$, [`R574_710_points_rule.json`](R574_710_points_rule.json)) |
| **$R(4, 4, 4; 3)$** | $79$ | $84$ (Yang, 2026) | **$\mathbf{100}$** *(superseded by $103$ above)* | $T_{99}$ on $\mathbb{Z}_{98} \cup \{\infty\}$ ($G(98, 67)$, [`R4443_99_points_rule.json`](R4443_99_points_rule.json)) |

*\*Note: Subsequent to `v1.1.0`, Lysenstøen (`stepping-up-ramsey`, Nov 2026) extended the $\mathrm{PGL}(2, q)$ family to $q = 857$, establishing $R(5, 7; 4) \ge 859$; meanwhile $R(6, 6; 4) \ge 685$ implies $R(12, 12; 5) > 2^{684}$ (or $> 2^{684}$ via stepping-up).*

---

## 2. Quick Clean-Room Verification (Zero External Dependencies)

### A. Verify All 16 Part II Bounds (`v1.2.0`) — ~2.5s in Rust / ~20s in Python

```bash
# 100% Exhaustive Zero-Dependency Rust Verifier (~2.5s total for all 16 bounds up to 9,438 points)
rustc -C opt-level=3 -C target-cpu=native verify_part2_records.rs -o verify_part2_records
./verify_part2_records

# Pure-Python Standard-Library Verifier (~20s)
python verify_part2_records.py
```

### B. Verify Part I Bounds (`v1.1.0`) — ~1.2s in Python / ~5s in Rust

```bash
python verify_all_records.py

rustc -C opt-level=3 -C target-cpu=native verify_r444_3.rs -o verify_r444_3
./verify_r444_3 R4443_99_points_rule.json

rustc -C opt-level=3 -C target-cpu=native verify_r574_psl_1mod4.rs -o verify_r574_psl_1mod4
./verify_r574_psl_1mod4 R574_710_points_rule.json

rustc -C opt-level=3 -C target-cpu=native verify_r664_psl.rs -o verify_r664_psl
./verify_r664_psl R664_684_points_rule.json
```

---

## 3. Citation

```bibtex
@misc{hashimoto2026hypergraph_part2,
  author       = {Katsutoshi Hashimoto},
  title        = {Constructive Lower Bounds for Multicolour and Off-Diagonal Hypergraph Ramsey Numbers},
  year         = {2026},
  month        = nov,
  version      = {v1.2.0},
  publisher    = {Zenodo},
  doi          = {10.5281/zenodo.24462206},
  url          = {https://doi.org/10.5281/zenodo.24462206}
}
```
