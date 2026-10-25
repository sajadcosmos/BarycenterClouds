# Claim-by-claim verification map

Each numbered result of the paper is listed with the Lean declarations in `BarycentricClouds.lean` that prove it, by full name. Everything lives in the namespace `Barycenter`; results about i.i.d. rotationally invariant darts are in `Barycenter.RadialSample`, and results about general i.i.d. samples (Section 7) are in `Barycenter.IIDSample`.

## Section 2 — Powers in the unit disk

| Paper | Lean |
|---|---|
| Proposition 2.1 (disk moments) | `Barycenter.disk_moments` |
| Theorem 2.2 (mean of `n`th powers), (2.1)–(2.2), a.s. convergence, CLT | `Barycenter.disk_Wpow_mean`, `Barycenter.disk_Wpow_bounds`, `Barycenter.disk_Wpow_ae`, `Barycenter.disk_Wpow_clt` |
| Example 2.3 (unit circle) | `Barycenter.circle_Wpow_sq` |
| Proposition 2.4 (powers of the center), (2.4), asymptotics, bounds | `Barycenter.disk_center_pow_mean`, `Barycenter.disk_center_pow_sq_formulas`, `Barycenter.disk_center_pow_sq_asymp`, `Barycenter.disk_center_pow_sq_le` |
| Remark in Section 2 (where the `n`th power sends a dart) | `Barycenter.disk_pow_cdf` |

## Section 3 — Moments of the center

| Paper | Lean |
|---|---|
| Lemma 3.2 (rotational invariance) | `Barycenter.RotInv.cmom_eq` |
| Lemma 3.3 (monomial centers), bounds | `Barycenter.RadialSample.integral_Wpow`, `Barycenter.RadialSample.integral_Wpow_mul_conj`, `Barycenter.RadialSample.Wpow_bounds` |
| Lemma 3.4 (moments of the center) | `Barycenter.RadialSample.cmom_sum`, `Barycenter.RadialSample.cmom_Scen`, `Barycenter.RadialSample.integral_Wpow_mul_conj_Scen` |
| Eqs. (3.3)–(3.4) | `Barycenter.qmom_two`, `Barycenter.qmom_three` |
| Example 3.5 (`κ_{m,n} ∼ n!/m^n`) | `Barycenter.kappa_one`, `Barycenter.kappa_two`, `Barycenter.tendsto_pow_mul_kappa` |
| Lemma 3.6 (inequalities, equality case, monotonicity) | `Barycenter.RadialSample.qmom_le`, `Barycenter.RadialSample.qmom_eq_iff`, `Barycenter.Qsum_eq_pow_mul_imp`, `Barycenter.kappa_le_inv`, `Barycenter.kappa_le_factorial_div`, `Barycenter.kappa_strictAnti` |

## Section 4 — Center of the image versus image of the center

| Paper | Lean |
|---|---|
| Proposition 4.1, means and (4.2)–(4.4) | `Barycenter.RadialSample.integral_Aimg`, `Barycenter.RadialSample.integral_Bimg`, `Barycenter.RadialSample.Vf_eq_integral`, `Barycenter.RadialSample.integral_norm_sq_Aimg`, `Barycenter.RadialSample.integral_norm_sq_Bimg`, `Barycenter.RadialSample.integral_cov_AB` |
| Theorem 4.2, (4.6), constant, equality cases (i)–(ii), optimality | `Barycenter.RadialSample.term_le`, `Barycenter.RadialSample.main_le`, `Barycenter.RadialSample.main_eq_A`, `Barycenter.RadialSample.main_constant`, `Barycenter.RadialSample.main_eq_iff_one`, `Barycenter.RadialSample.main_eq_iff_ge_two`, `Barycenter.main_optimal` |
| Corollary 4.3 (deficit at a quadratic critical point) | `Barycenter.RadialSample.deficit_ge`, `Barycenter.RadialSample.deficit_pure_quadratic`, `Barycenter.RadialSample.deficit_fixed_radius` |
| Corollary 4.4, (4.5), deviations, `L²` and a.s. convergence | `Barycenter.RadialSample.coeff_bound`, `Barycenter.RadialSample.deviation_A`, `Barycenter.RadialSample.deviation_B`, `Barycenter.RadialSample.tendsto_L2`, `Barycenter.RadialSample.ae_tendsto_Aimg`, `Barycenter.RadialSample.ae_tendsto_Bimg` |
| Remark 4.5 (exponential tails) | `Barycenter.RadialSample.hoeffding_Aimg` |
| Corollary 4.6, (4.7)–(4.8) | `Barycenter.disk_A`, `Barycenter.disk_B`, `Barycenter.disk_cauchy_A`, `Barycenter.disk_cauchy_B` |

## Section 5 — Examples

| Paper | Lean |
|---|---|
| Example 5.1 (`e^z`, unit-disk darts) | `Barycenter.expDiskV_bounds`, `Barycenter.exp_disk_example`, `Barycenter.exp_disk_B_values` |
| Example 5.2 (a rigid polynomial) | `Barycenter.rigid_example`, `Barycenter.rigid_values` |
| Example 5.3 | `Barycenter.RadialSample.gaussian_example` |
| Example 5.4 (complex Gaussian radial moments) | `Barycenter.Qsum_gaussian` |

## Section 6 — Fluctuations

| Paper | Lean |
|---|---|
| Theorem 6.1, (6.1)–(6.3) | `Barycenter.RadialSample.tendstoInDistribution_Bimg_clt`, `Barycenter.RadialSample.tendsto_law_Bimg`, `Barycenter.RadialSample.tendsto_scaled_mse`, `Barycenter.RadialSample.tendsto_scaled_abs_clt`, `Barycenter.RadialSample.tendsto_scaled_abs_gamma_clt` |
| Proposition 6.2 (joint fluctuations), remainder, case `d = 1` | `Barycenter.RadialSample.tendstoInDistribution_joint_clt`, `Barycenter.RadialSample.tendstoInDistribution_joint_paper`, `Barycenter.RadialSample.remainder_gaussian_indep`, `Barycenter.RadialSample.tendstoInDistribution_A_sub_B` |

The file first proves Theorem 6.1 and Proposition 6.2 relative to the central limit theorem (`Barycenter.RadialSample.tendstoInDistribution_Bimg`, `Barycenter.RadialSample.tendsto_scaled_abs`, `Barycenter.RadialSample.tendsto_scaled_abs_gamma`, `Barycenter.RadialSample.tendstoInDistribution_joint`), and then discharges that hypothesis. The `_clt` versions listed above are unconditional.

## Section 7 — General i.i.d. samples

| Paper | Lean |
|---|---|
| Proposition 7.1 (exact polynomial bias), special cases | `Barycenter.IIDSample.integral_Scen_pow`, `Barycenter.IIDSample.integral_Scen_pow_small` |
| Theorem 7.2 (moment criterion for exact means), entire maps | `Barycenter.IIDSample.criterion`, `Barycenter.IIDSample.integral_entire_of_vanishing`, `Barycenter.Bsum_of_vanishing` |
| Example 7.3 (non-radial law) | `Barycenter.nonradial_moments`, `Barycenter.nonradial_example` |
| Example 7.4 (bias for real sampling) | `Barycenter.bias_real_sampling` |

## Section 8 — Mean values and Monte Carlo contour integration

| Paper | Lean |
|---|---|
| Theorem 8.1 (Gauss), (8.1)–(8.2) | `Barycenter.gauss_mean_circle`, `Barycenter.gauss_mean_value`, `Barycenter.gauss_mean_disk`, `Barycenter.circle_variance` |
| Proposition 8.2 (Monte Carlo contour integration) | `Barycenter.contour_analytic`, `Barycenter.contour_continuous` |
| Proposition 8.3 (rotated trapezoidal rule), and the example after it | `Barycenter.Trule_sub`, `Barycenter.Trule_mean_var`, `Barycenter.Trule_bound`, `Barycenter.roots_exp_error` |

## Section 9 — Polynomials with random zeros

| Paper | Lean |
|---|---|
| Proposition 9.1 (coefficients for rotationally invariant zeros) | `Barycenter.RadialSample.integral_esym`, `Barycenter.RadialSample.integral_esym_mul_conj`, `Barycenter.RadialSample.integral_norm_sq_poly`, `Barycenter.disk_esym` |
