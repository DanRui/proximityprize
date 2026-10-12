/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._AntipodalEvenOddDescent

/-!
# `IsolatedCountResidual` is false as stated

`IsolatedCountResidual F k` quantifies over every `E O : F[X]` with only `O.natDegree < k`;
`E` carries no degree bound and no subgroup, decodedness or support restriction. It asserts
that the isolated roots of `E(X²) - X·O(X²)` number at most `k + 1`.

At `k = 1` over `ℚ`, take `O = 1` and `E = -u²/6 + 7u/6`. Then `E(x²) = x` at
`x = 0, 1, 2` (`E(0)=0`, `E(1)=1`, `E(4)=2`), giving three isolated roots against the
claimed cap of `2`.

This refutes the recorded statement only. The intended restrictions (the halved-subgroup
domain and a degree bound on `E`) are not discharged here, and the underlying Kelley /
BGK general-position count remains open. It does not close #164.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ProximityGap.Frontier.IsolatedCountResidualRefuted

open AntipodalEvenOddDescent

/-- The interpolant `E(u) = -u²/6 + 7u/6`. -/
def E₀ : ℚ[X] := C (-1 / 6) * X ^ 2 + C (7 / 6) * X

/-- The three isolated roots `0, 1, 2` of `E₀(X²) - X · 1`. -/
theorem three_isolated_roots :
    (↑({0, 1, 2} : Finset ℚ) : Set ℚ) ⊆
      {x : ℚ | (E₀.comp (X ^ 2) - X * (C (1 : ℚ)).comp (X ^ 2)).IsRoot x ∧
        (C (1 : ℚ)).eval (x ^ 2) ≠ 0} := by
  intro x hx
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  refine ⟨?_, by simp⟩
  rcases hx with rfl | rfl | rfl <;> simp [E₀, IsRoot.def] <;> norm_num

/-- `IsolatedCountResidual ℚ 1` is false: three isolated roots exceed the cap `k + 1 = 2`. -/
theorem not_isolatedCountResidual_rat_one : ¬ IsolatedCountResidual ℚ 1 := by
  intro h
  have hc := (h E₀ (C 1) (by simp)).2 {0, 1, 2} three_isolated_roots
  have : ({0, 1, 2} : Finset ℚ).card = 3 := by decide +revert
  omega

end ProximityGap.Frontier.IsolatedCountResidualRefuted

#print axioms ProximityGap.Frontier.IsolatedCountResidualRefuted.three_isolated_roots
#print axioms ProximityGap.Frontier.IsolatedCountResidualRefuted.not_isolatedCountResidual_rat_one
