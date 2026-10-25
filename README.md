# Lean 4 formalization: *Barycentric Clouds: Centers of Mass of Random Complex Numbers under Analytic Maps*

This repository contains the complete Lean 4 / Mathlib formalization accompanying

> S. A. Sheikh,
> *Barycentric Clouds: Centers of Mass of Random Complex Numbers under Analytic Maps* (2026).

The whole development is a single file, [`BarycentricClouds.lean`](BarycentricClouds.lean) (about 7,000 lines). It contains **no `sorry` and no `axiom` declarations**, and no external results are taken as hypotheses.

## What is formalized

The paper studies what happens to centers of mass of random complex numbers ("darts") under analytic maps: the mean of the images versus the image of the mean. The formalization covers:

- **Section 2:** means of `n`th powers of darts in the unit disk, with bounds, almost sure convergence and a central limit theorem, and the powers of the center
- **Section 3:** exact moments of the center, the Pearson random-walk constants `κ_{m,n}`, and their inequalities, equality cases and monotonicity
- **Section 4:** the main comparison of "center of the image" and "image of the center" (Proposition 4.1, Theorem 4.2 with its sharp constant, equality cases and optimality), deficits, deviation bounds, and `L²` and almost sure convergence
- **Section 5:** worked examples (`e^z`, a rigid polynomial, Gaussian radial moments)
- **Section 6:** fluctuation limits (Theorem 6.1, Proposition 6.2), including a proof of the central limit theorem they need
- **Section 7:** exact polynomial bias for general i.i.d. samples and the moment criterion for exact means
- **Section 8:** Gauss's mean value theorem in probabilistic form, Monte Carlo contour integration, and the rotated trapezoidal rule
- **Section 9:** coefficients of polynomials with rotationally invariant random zeros

[`VERIFICATION.md`](VERIFICATION.md) maps each numbered result of the paper to its Lean theorem names.

## Building

Requirements: [Lean 4](https://lean-lang.org/) via `elan`. The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.28.0`), and Mathlib is pinned to `v4.28.0` in `lakefile.toml`.

```bash
git clone https://github.com/sajadcosmos/BarycenterClouds.git
cd BarycenterClouds
lake update          # resolves Mathlib
lake exe cache get   # downloads precompiled Mathlib
lake build
```

A successful `lake build` with no errors confirms that every proof checks.

An automated build (GitHub Actions, see the **Actions** tab) runs on every change. It compiles the file and prints the axioms of the main theorems, failing if any of them depends on `sorry`.

## Files

| File | Purpose |
|---|---|
| `BarycentricClouds.lean` | The complete formalization |
| `VERIFICATION.md` | Map from the paper's numbered results to Lean theorem names |
| `lakefile.toml` | Lake build configuration (Mathlib dependency) |
| `lean-toolchain` | Pinned Lean version |
| `CITATION.cff` | Citation metadata (powers GitHub's "Cite this repository" button) |
| `.github/workflows/lean.yml` | Automated build and axiom check |

## Contact

Sajad Ahmad Sheikh, Department of Mathematics, University of Kashmir, South Campus, Anantnag, 192101, Jammu and Kashmir, India
sajadsheikh@uok.edu.in

## License

See [`LICENSE`](LICENSE).
