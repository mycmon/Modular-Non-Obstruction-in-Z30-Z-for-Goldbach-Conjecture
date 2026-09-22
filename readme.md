```
# Modular Non-Obstruction in $\mathbb{Z}/30\mathbb{Z}$ for Goldbach's Conjecture

![Lean 4](https://img.shields.io/badge/Lean_4-Formal_Proof-blue)
![Python](https://img.shields.io/badge/Python-3.x-green)
![License](https://img.shields.io/badge/License-MIT-yellow)

Formal verification in **Lean 4** and empirical validation in **Python** regarding local modular non-obstruction for Goldbach's conjecture within the residue ring $\mathbb{Z}/30\mathbb{Z}$ and primorial unit groups.

---

## 📌 Overview

This repository contains the formal proofs, LaTeX/Markdown source papers, and computational scripts for the research paper:

> **"Modular Non-Obstruction in $\mathbb{Z}/30\mathbb{Z}$ for Goldbach's Conjecture: Formal Verification in Lean 4 and Empirical Validation"**  
> *Author:* Michel Monfette (Independent Researcher)

### Key Contributions
1. **Modular Algebra ($\mathbb{Z}/30\mathbb{Z}$):** Complete analysis of the reduced residue classes $\mathcal{P}_{30} = \{1, 7, 11, 13, 17, 19, 23, 29\}$, proving that all 15 even residue classes modulo 30 are covered by sum pairs in $\mathcal{P}_{30}$.
2. **Formal Verification in Lean 4:** A machine-checked structural proof (`goldbach_local_primorial_general`) demonstrating general non-obstruction across primorial unit groups $\prod_{i=1}^k (\mathbb{Z}/p_i\mathbb{Z})^\times$ using Mathlib and the Chinese Remainder Theorem (CRT), certified with 0 `sorry` placeholders.
3. **Empirical Validation (Python):** High-performance sieve verification showing 100% coverage for all even integers $18 \le 2N \le 1,000,000$ restricted strictly to prime candidates in $\mathcal{P}_{30}$.

---

## 📁 Repository Structure

├── Lean/
│   └── GoldbachLocalPrimorial.lean   # Complete Lean 4 formal proof
├── Python/
│   └── verify_coverage.py            # Goldbach sieve script (P30 restricted)
├── Paper/
│   └── Modular_Non_Obstruction_Goldbach.md # Full manuscript (EN/FR)
├── LICENSE                           # MIT License
└── README.md                         # Project overview
```

## 🛠️ Prerequisites & Execution

### 1. Formal Verification in Lean 4

To verify the Lean 4 proof locally, ensure you have [elan](https://github.com/leanprover/elan?utm_source=gemini) and Lean 4 installed.

Bash

```
# Clone the repository
git clone [https://github.com/your-username/goldbach-z30z-non-obstruction.git](https://github.com/your-username/goldbach-z30z-non-obstruction.git)
cd goldbach-z30z-non-obstruction/Lean

# Build and verify with Lake (Mathlib dependency required)
lake build

or 

use https://live.lean-lang.org/?from=lean

```

### 2. Empirical Verification in Python

The Python script runs using Python 3.8+ (standard library only).

Bash

```
cd Python
python verify_coverage.py
```

**Expected Console Output:**

Plaintext

```
========================================================================================
 GOLDBACH COVERAGE VERIFICATION WITH P30 = {1, 7, 11, 13, 17, 19, 23, 29} 
========================================================================================

Execution Summary for 2N <= 1,000,000:
  Total evens tested        : 499,998
  Goldbach pairs found      : 499,993 (99.9990%)
  Execution time            : 0.98s
  Missed evens list         : [6, 8, 10, 12, 16]
  Missed distribution (mod 30): {0: 0, 2: 0, 4: 0, 6: 1, 8: 1, 10: 1, 12: 1, 14: 0, 16: 1, 18: 0, 20: 0, 22: 0, 24: 0, 26: 0, 28: 0}
========================================================================================

```

> **Note on Boundary Exceptions ($2N < 18$):** The 5 missed evens $\{6, 8, 10, 12, 16\}$ result from the structural exclusion of small prime factors ($2, 3, 5$). Since $p \in \mathcal{P}_{30} \implies p \ge 7$, the minimum representable sum is $7 + 7 = 14$. For $2N \ge 18$, coverage is $100.0000\%$.

## 📊 Addition Matrix $\mathcal{P}_{30} \times \mathcal{P}_{30} \pmod{30}$

| **+(mod30)** | **1** | **7** | **11** | **13** | **17** | **19** | **23** | **29** |
| ------------ | ----- | ----- | ------ | ------ | ------ | ------ | ------ | ------ |
| **1**        | 2     | **8** | 12     | 14     | 18     | 20     | 24     | 0      |
| **7**        | **8** | 14    | 18     | 20     | 24     | 26     | 0      | 6      |
| **11**       | 12    | 18    | 22     | 24     | 28     | 0      | 4      | 10     |
| **13**       | 14    | 20    | 24     | 26     | 0      | 2      | 6      | 12     |
| **17**       | 18    | 24    | 28     | 0      | 4      | 6      | 10     | 16     |
| **19**       | 20    | 26    | 0      | 2      | 6      | **8**  | 12     | 18     |
| **23**       | 24    | 0     | 4      | 6      | 10     | 12     | 16     | 22     |
| **29**       | 0     | 6     | 10     | 12     | 16     | 18     | 22     | 28     |

## 📜 Citation

If you reference this proof or computational framework in your work, please cite:

Extrait de code

```
@article{monfette2026goldbach,
  title={Modular Non-Obstruction in $\mathbb{Z}/30\mathbb{Z}$ for Goldbach's Conjecture: Formal Verification in Lean 4 and Empirical Validation},
  author={Monfette, Michel},
  year={2026}
}
```

## 📄 License

This project is released under the [MIT License](https://www.google.com/search?q=LICENSE&utm_source=gemini).

Michel Monfette
mycmon@gmail.com

[Chicoutimi, Canada]

[https://github.com/mycmon/Modular-Non-Obstruction-in-Z30-Z-for-Goldbach-Conjecture/releases/tag/Goldbach]

https://zenodo.org/account/settings/github/repository/mycmon/Modular-Non-Obstruction-in-Z30-Z-for-Goldbach-Conjecture