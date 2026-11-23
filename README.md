# Improved Constructive Lower Bounds for Small Hypergraph Ramsey Numbers (`v1.1.0`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24462206.svg)](https://doi.org/10.5281/zenodo.24462206)

**Author**: Katsutoshi Hashimoto (Independent Researcher, Japan — `ramuza0113@gmail.com` · [ORCID: `0009-0009-8292-5085`](https://orcid.org/0009-0009-8292-5085))  
**Date**: November 2026  
**Concept DOI (always resolves to latest version)**: [`10.5281/zenodo.24462206`](https://doi.org/10.5281/zenodo.24462206) (`v1.0.0` DOI: [`10.5281/zenodo.24462207`](https://doi.org/10.5281/zenodo.24462207))  
**Paper**: [`paper/main.pdf`](paper/main.pdf) ([`paper/main.tex`](paper/main.tex))

---

## 1. Summary of New Lower Bounds (10 Improved Entries)

Let $R(k_1, \dots, k_r; t)$ denote the smallest integer $n$ such that every $r$-colouring of the $t$-subsets of an $n$-element set contains, for some colour $i$, a $k_i$-subset all of whose $t$-subsets have colour $i$.

### Direct Explicit Constructions (Machine-Readable Witnesses + Clean-Room Verifiers)

| Hypergraph Ramsey Number | Dynamic Survey DS1 (Apr 2026) | Recent 2026 Bounds | **New Bound (`v1.1.0`)** | Witness & Symmetry Group |
| :--- | :---: | :---: | :---: | :--- |
| **$R(4, 4, 4; 3)$** | $79$ | $84$ (Yang, 2026) | **$\mathbf{100}$** | $T_{99}$ on $\mathbb{Z}_{98} \cup \{\infty\}$ ($G(98, 67)$, $545$ orbits) |
| **$R(5, 7; 4)$** | $133$ | $401$ (Lysenstøen, Nov 2026) | **$\mathbf{711}$** | $G_{710}$ on $\mathbb{F}_{709} \cup \{\infty\}$ ($\mathrm{PGL}(2, 709)$, $119$ classes) |
| **$R(6, 6; 4)$** | $133$ | $601$ (Lysenstøen, Nov 2026) | **$\mathbf{685}$** | $F_{684}$ on $\mathbb{F}_{683} \cup \{\infty\}$ ($\mathrm{PSL}(2, 683)$, $142$ narrow classes) |

*(Progressive intermediate witnesses $F_{620}, F_{632}, F_{648}, F_{660}$ for $R(6,6;4)$, $G_{660}, G_{702}$ for $R(5,7;4)$, and $T_{98}$ for $R(4,4,4;3)$ are also included in this repository.)*

### Consequences via Known Recurrences & Stepping-Up Constructions

| Hypergraph Ramsey Number | Dynamic Survey DS1 | Recent 2026 Bounds | **New Bound (`v1.1.0`)** | Derivation |
| :--- | :---: | :---: | :---: | :--- |
| **$R(6, 7; 4)$** | $661$ | $2,001$ | **$\mathbf{3,551}$** | Song–Ye–Liu recurrence from $R(5, 7; 4) \ge 711$ |
| **$R(7, 7; 4)$** | $3,961$ | $12,001$ | **$\mathbf{21,301}$** | Song–Ye–Liu recurrence from $R(6, 7; 4) \ge 3,551$ |
| **$R(7, 8; 4)$** | — | $84,001$ | **$\mathbf{149,101}$** | Song–Ye–Liu recurrence from $R(7, 7; 4) \ge 21,301$ |
| **$R(8, 8; 4)$** | $194,041$ | $588,001$ | **$\mathbf{1,043,701}$** | Song–Ye–Liu recurrence from $R(7, 8; 4) \ge 149,101$ |
| **$R(13, 6; 4)$** | $50,689$ | ($128,001$) | **$\mathbf{227,201}$** | $6$ doublings from $R(6, 7; 4) \ge 3,551$ |
| **$R_6(5; 4)$** | $> 2^{78}$ | ($> 2^{83}$) | **$> \mathbf{2^{99}}$** | Jartoux–Keller–Smorodinsky–Yuditsky stepping-up |
| **$R(12, 12; 5)$** | $> 2^{132}$ | ($> 2^{600}$) | **$> \mathbf{2^{684}}$** | Erdős–Hajnal stepping-up from $R(6, 6; 4) \ge 685$ |

---

## 2. Quick Clean-Room Verification (Zero External Dependencies)

### A. One-Command Pure-Python Verification (~1.2s, Python Standard Library Only)

```bash
python verify_all_records.py
```

Verifies SHA-256 digests, group invariance, all normalized $4$-subsets of $T_{99}$, and **all** $249,571$ normalized $5$-subsets + **all** $\binom{707}{4} = 10,368,268,935$ normalized $7$-subsets of $G_{710}$.

### B. Full Exhaustive Zero-Shared-Code Rust Verifiers (~5s Total)

```bash
rustc -C opt-level=3 -C target-cpu=native verify_r444_3.rs -o verify_r444_3
./verify_r444_3 R4443_99_points_rule.json

rustc -C opt-level=3 -C target-cpu=native verify_r574_psl_1mod4.rs -o verify_r574_psl_1mod4
./verify_r574_psl_1mod4 R574_710_points_rule.json

rustc -C opt-level=3 -C target-cpu=native verify_r664_psl.rs -o verify_r664_psl
./verify_r664_psl R664_684_points_rule.json
```

---

## 3. SHA-256 Digests of Flagship Witnesses

- `T_99` (`R4443_99_points_rule.json`, $545$-orbit string): `524a14cbc477f4966994b3a0efa6b6488484e329016302c4858b89940a836549`
- `T_99` (expanded $156,849$-triple lexicographic string): `75b4560cf8cd2191fad4a85a5597b51850dedf42056aedb867a9da473a994d03`
- `G_710` (`R574_710_points_rule.json`, `tau_table`): `1c700d6603970e03fbbbb2495e3616c142072dcccd7c9603ed6594b7cfc35618`
- `F_684` (`R664_684_points_rule.json`, `table`): `0c9e37be4ee4b5493869cb55e75553e2165f49b805b7934d212d16d30225f482`
- `F_620` (`R664_620_points_rule.json`, `table`, `v1.0.0`): `6658e8cfc640c17e14b425f5b0a19bd03017ed1aba7a035752df5550199467c6`

---

## 4. Citation

```bibtex
@misc{hashimoto2026hypergraph,
  author       = {Katsutoshi Hashimoto},
  title        = {Improved Constructive Lower Bounds for Small Hypergraph Ramsey Numbers},
  year         = {2026},
  month        = nov,
  version      = {v1.1.0},
  publisher    = {Zenodo},
  doi          = {10.5281/zenodo.24462206},
  url          = {https://doi.org/10.5281/zenodo.24462206}
}
```
