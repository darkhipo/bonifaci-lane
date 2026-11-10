# Merge receipt — M6 + M7 onto the true base (`ec6e530`)

Date: 2026-11-10. Lane: `/Volumes/Substrate-1/bigo/bonifaci-lane` (branch `main`).
Toolchain `leanprover/lean4:v4.34.1`; Mathlib pin `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Driver discipline for every build below: exclusive `fcntl` lock on `.lane-build.lock`
(single writer per lane), live-pressure gate before spending CPU, kill-retry on signal,
receipts written to files (`receipts/build_*.receipt`), polled in-turn.

## 1. Build

| target | exit | jobs | log | warnings |
|---|---|---|---|---|
| `Bonnifaci` (root, incl. M6 + M7) | **0** | 2257 | `receipts/build_merged.log` | 4, all pre-existing (Thm11 ×3, Lemma43 ×1); **M6/M7: 0** |
| `Bonnifaci.M7` | **0** | 2148 | `receipts/build_m7.log` | 0 |
| `Bonnifaci` (M6 merge, first green) | **0** | 2256 | `receipts/build_m6_merge.log` | 4 pre-existing; M6: 0 |

Incremental cost of the merge: 66 new Mathlib modules (~2 min at load ≈ 120), from the
rank-nullity route chosen over the determinant route (49 vs 119 unbuilt modules — measured
by import-closure walk, not guessed).

## 2. Named oleans (14)

`Model KL Core Optimality Features Feasibility Theorem Thm11 Duality Lemma41 Lemma43 Mu M6 M7`

## 3. Axiom banner

`receipts/axioms_merged.txt`, `lake env lean` exit 0, 27 declarations, **every line exactly**

    [propext, Classical.choice, Quot.sound]

Zero off-target lines. `grep -r 'sorry\|admit' Bonnifaci/*.lean` → nothing.

M6 (3): `Lmat_injective`, `exists_potential`, `exists_step`.
M7 (8): `res_energy_eq_zero`, `flow_eq_of_kirchhoff_ohm`, `potential_eq_of_ohm`,
`step_unique`, `step_p_unique`, `existsUnique_flow`, `qfun_eq_steps`,
`Solution.q_eq_qfun`.
Restored M3/M5 family (16): `thm11_final`, `thm11`, `kl_deriv_le`, `kl_deriv_sum`,
`cost_log_deriv_le`, `sum_cq_le`, `cost_deriv`, `log_cost_deriv`, `differentiable_kl_sum`,
`lem42_core`, `duality_inner`, `phi_decrease_core`, `feasibility_invariant`,
`edge_no_retirement`, `kl_bound_mu`, `entropy_summand_le`.

## 4. `Model.lean` diff verdict

`Bonnifaci/Model.lean` is **byte-identical to `ec6e530`** — `git diff ec6e530 --
Bonnifaci/Model.lean` is empty. M6 compiled against it unmodified.

The re-derived `Model.lean` in the rebuilt copy was strictly poorer:

* common declarations: 8 (all of them)
* only in the rebuild: **0**
* only in the original: `differentiableAt_finset_sum`, `deriv_finset_sum`
* only in the original: `import Mathlib.Analysis.Calculus.Deriv.Add`

The two lemmas have **9 call sites** (`Feasibility` 2, `Lemma41` 1, `Lemma43` 2, `Thm11` 4):
taking the rebuild would have broken four modules.

## 5. M7 position

Landed: the flow map is well defined (uniqueness of the electrical data at each point), the
ODE right-hand side exists as a function, and a trajectory's flow is that function.

Named, not proved: `LPData.FlowLipschitzOnOrthant` (local Lipschitz — needs Mathlib's
continuous-linear-map inverse theory, outside this pin's built prefix) and
`LPData.HasSolution` ([SV16, Thm 1.1]).
