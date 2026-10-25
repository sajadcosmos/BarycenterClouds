# Claim-by-claim verification map

Each numbered result of the paper is listed with the Lean declarations in `BarycentricClouds.lean` that prove it. Declarations live in four namespaces: `Barycenter` (deterministic and combinatorial facts), `RadialSample` (i.i.d. rotationally invariant darts), `IIDSample` (general i.i.d. samples, Section 7) and `OrthoMoments`. Names below are given in full.

## Section 2 — Powers in the unit disk

| Paper | Lean |
|---|---|
| Proposition 2.1 (disk moments) | `RadialSample.disk_moments` |
| Theorem 2.2 (mean of `n`th powers), (2.1)–(2.2), a.s. convergence, CLT | `RadialSample.disk_Wpow_mean`, `RadialSample.disk_Wpow_bounds`, `RadialSample.disk_Wpow_ae`, `RadialSample.disk_Wpow_clt` |
| Example 2.3 (unit circle) | `RadialSample.circle_Wpow_sq` |
| Proposition 2.4 (powers of the center), (2.4), asymptotics, bounds | `RadialSample.disk_center_pow_mean`, `RadialSample.disk_center_pow_sq_formulas`, `RadialSample.disk_center_pow_sq_asymp`, `RadialSample.disk_center_pow_sq_le` |
| Remark in Section 2 (where the `n`th power sends a dart) | `Barycenter.disk_pow_cdf` |

## Section 3 — Moments of the center

| Paper | Lean |
|---|---|
| Lemma 3.2 (rotational invariance) | `Barycenter.RotInv.cmom_eq` |
| Lemma 3.3 (monomial centers), bounds | `RadialSample.integral_Wpow`, `RadialSample.integral_Wpow_mul_conj`, `RadialSample.Wpow_bounds` |
| Lemma 3.4 (moments of the center) | `RadialSample.cmom_sum`, `RadialSample.cmom_Scen`, `RadialSample.integral_Wpow_mul_conj_Scen` |
| Eqs. (3.3)–(3.4) | `Barycenter.qmom_two`, `Barycenter.qmom_three` |
| Example 3.5 (`κ_{m,n} ∼ n!/m^n`) | `Barycenter.kappa_one`, `Barycenter.kappa_two`, `Barycenter.tendsto_pow_mul_kappa` |
| Lemma 3.6 (inequalities, equality case, monotonicity) | `RadialSample.qmom_le`, `RadialSample.qmom_eq_iff`, `Barycenter.Qsum_eq_pow_mul_imp`, `Barycenter.kappa_le_inv`, `Barycenter.kappa_le_factorial_div`, `Barycenter.kappa_strictAnti` |

## Section 4 — Center of the image versus image of the center

| Paper | Lean |
|---|---|
| Proposition 4.1, means and (4.2)–(4.4) | `RadialSample.integral_Aimg`, `RadialSample.integral_Bimg`, `RadialSample.Vf_eq_integral`, `RadialSample.integral_norm_sq_Aimg`, `RadialSample.integral_norm_sq_Bimg`, `RadialSample.integral_cov_AB` |
| Theorem 4.2, (4.6), constant, equality cases (i)–(ii), optimality | `RadialSample.term_le`, `RadialSample.main_le`, `RadialSample.main_eq_A`, `RadialSample.main_constant`, `RadialSample.main_eq_iff_one`, `RadialSample.main_eq_iff_ge_two`, `RadialSample.main_optimal` |
| Corollary 4.3 (deficit at a quadratic critical point) | `RadialSample.deficit_ge`, `RadialSample.deficit_pure_quadratic`, `RadialSample.deficit_fixed_radius` |
| Corollary 4.4, (4.5), deviations, `L²` and a.s. convergence | `RadialSample.coeff_bound`, `RadialSample.deviation_A`, `RadialSample.deviation_B`, `RadialSample.tendsto_L2`, `RadialSample.ae_tendsto_Aimg`, `RadialSample.ae_tendsto_Bimg` |
| Remark 4.5 (exponential tails) | `RadialSample.hoeffding_Aimg` |
| Corollary 4.6, (4.7)–(4.8) | `Barycenter.disk_A`, `Barycenter.disk_B`, `Barycenter.disk_cauchy_A`, `Barycenter.disk_cauchy_B` |

## Section 5 — Examples

| Paper | Lean |
|---|---|
| Example 5.1 (`e^z`, unit-disk darts) | `Barycenter.expDiskV_bounds`, `Barycenter.exp_disk_example`, `Barycenter.exp_disk_B_values` |
| Example 5.2 (a rigid polynomial) | `Barycenter.rigid_example`, `Barycenter.rigid_values` |
| Example 5.3 | `RadialSample.gaussian_example` |
| Example 5.4 (complex Gaussian radial moments) | `Barycenter.Qsum_gaussian` |

## Section 6 — Fluctuations

| Paper | Lean |
|---|---|
| Theorem 6.1, (6.1)–(6.3) | `RadialSample.tendstoInDistribution_Bimg_clt`, `RadialSample.tendsto_law_Bimg`, `RadialSample.tendsto_scaled_mse`, `RadialSample.tendsto_scaled_abs_clt`, `RadialSample.tendsto_scaled_abs_gamma_clt` |
| Proposition 6.2 (joint fluctuations), remainder, case `d = 1` | `RadialSample.tendstoInDistribution_joint_clt`, `RadialSample.tendstoInDistribution_joint_paper`, `RadialSample.remainder_gaussian_indep`, `RadialSample.tendstoInDistribution_A_sub_B` |

The file first proves Theorem 6.1 and Proposition 6.2 relative to the central limit theorem (`RadialSample.tendstoInDistribution_Bimg`, `RadialSample.tendsto_scaled_abs`, `RadialSample.tendsto_scaled_abs_gamma`, `RadialSample.tendstoInDistribution_joint`), and then discharges that hypothesis. The `_clt` versions listed above are unconditional.

## Section 7 — General i.i.d. samples

| Paper | Lean |
|---|---|
| Proposition 7.1 (exact polynomial bias), special cases | `IIDSample.integral_Scen_pow`, `IIDSample.integral_Scen_pow_small` |
| Theorem 7.2 (moment criterion for exact means), entire maps | `IIDSample.criterion`, `IIDSample.integral_entire_of_vanishing`, `Barycenter.Bsum_of_vanishing` |
| Example 7.3 (non-radial law) | `Barycenter.nonradial_moments`, `Barycenter.nonradial_example` |
| Example 7.4 (bias for real sampling) | `IIDSample.bias_real_sampling` |

## Section 8 — Mean values and Monte Carlo contour integration

| Paper | Lean |
|---|---|
| Theorem 8.1 (Gauss), (8.1)–(8.2) | `Barycenter.gauss_mean_circle`, `Barycenter.gauss_mean_value`, `Barycenter.gauss_mean_disk`, `Barycenter.circle_variance` |
| Proposition 8.2 (Monte Carlo contour integration) | `Barycenter.contour_analytic`, `Barycenter.contour_continuous` |
| Proposition 8.3 (rotated trapezoidal rule), and the example after it | `Barycenter.Trule_sub`, `Barycenter.Trule_mean_var`, `Barycenter.Trule_bound`, `Barycenter.roots_exp_error` |

## Section 9 — Polynomials with random zeros

| Paper | Lean |
|---|---|
| Proposition 9.1 (coefficients for rotationally invariant zeros) | `RadialSample.integral_esym`, `RadialSample.integral_esym_mul_conj`, `RadialSample.integral_norm_sq_poly`, `RadialSample.disk_esym` |
