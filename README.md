# λₖ-Driven Incompressibility: Lower Bounds Separating P from NP

This repository contains the source code and data to reproduce the key regression analysis presented in the paper:

**"λₖ-Driven Incompressibility: Lower Bounds Separating P from NP"**  
DOI: [10.5281/zenodo.16734162](https://doi.org/10.5281/zenodo.16734162)

---

## 📌 Purpose

The core goal is to empirically validate the structural complexity lower bound:

\[
\log_2 T(x) \approx \alpha \cdot \lambda_k(x) + \beta \cdot \log_2 n + \gamma
\]

Where:
- \( T(x) \): Runtime of algorithm solving input \( x \)
- \( \lambda_k(x) \): Structural compressibility indicator
- \( n \): Problem size
- \( \Lambda(x) = \lambda_k(x) \cdot \log_2 T(x) \): Structure-time coupling

---

## 🔬 Key Result

This script fits the above model and achieves an extraordinarily high coefficient of determination:


This result suggests **nearly perfect alignment** between structural compressibility and runtime complexity across synthetic NP-complete and P-class instances.

---

## 📂 Files

- `lambda_log2n_regression.py` — core regression code
- `sample_data.csv` — data of [n, λₖ(x), log₂T(x)]
- `plot_fit.png` — optional visualization of regression surface (if included)

---

## ▶️ Usage

Run the script directly in a Python environment with `numpy`, `pandas`, and `scikit-learn`:

```bash
python lambda_log2n_regression.py


