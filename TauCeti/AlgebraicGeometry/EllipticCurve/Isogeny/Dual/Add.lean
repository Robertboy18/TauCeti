/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.WeilPairing

/-!
# The dual isogeny is additive

Let `φ, ψ : W₁ → W₂` be separable isogenies of elliptic curves over a separably closed field, and
suppose that their sum in the group of morphisms is again a separable isogeny `χ`. Then the dual of
the sum is the sum of the duals: `χ̂ = φ̂ + ψ̂` (Silverman III.6.2(b)).

The proof goes through the Weil pairing. For `N` invertible in the field, the dual is adjoint to
the isogeny (`TauCeti.Isogeny.weilPairing_eq_weilPairing_dual`), so for `S ∈ W₁[N]` and
`T ∈ W₂[N]`

    e_N(S, χ̂ T) = e_N(χ S, T) = e_N(φ S, T) · e_N(ψ S, T) = e_N(S, φ̂ T) · e_N(S, ψ̂ T)
                = e_N(S, φ̂ T + ψ̂ T).

Nondegeneracy of the pairing gives `χ̂ T = φ̂ T + ψ̂ T` on `W₂[N]`, and two morphisms agreeing on
the `ℓ`-torsion for every prime `ℓ` other than the characteristic are equal
(`TauCeti.Isogeny.Hom.ext_pointMap_of_prime_zsmul_eq_zero`).

Additivity of the dual is what makes the degree a quadratic form on the morphisms: writing
`deg f = f̂ ∘ f`, the pairing `(f, g) ↦ f̂ ∘ g + ĝ ∘ f = deg (f + g) − deg f − deg g` is bilinear
exactly because the dual is additive (Silverman III.6.3). Silverman proves the additivity by the
Picard-group description of the dual; the argument here replaces it with the Weil pairing, whose
compatibility with the dual (Silverman III.8.2) is already available.

## Main result

* `TauCeti.Isogeny.ofIsogeny_dual_add`: if `χ = φ + ψ` as morphisms, then `χ̂ = φ̂ + ψ̂`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.2(b), III.6.3 and
  III.8.2.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ ψ χ : Isogeny W₁ W₂) [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]
  [Algebra.IsSeparable ψ.fieldPullback.fieldRange W₁.FunctionField]
  [Algebra.IsSeparable χ.fieldPullback.fieldRange W₁.FunctionField]

/-- The dual of a sum is the sum of the duals on every `N`-torsion point, `N` invertible: the Weil
pairing step of `ofIsogeny_dual_add`. -/
private theorem pointMap_dual_eq_add_of_zsmul_eq_zero
    (hχ : Hom.ofIsogeny χ = Hom.ofIsogeny φ + Hom.ofIsogeny ψ) {N : ℕ} [NeZero N]
    (hN : (N : F) ≠ 0) {T : W₂.Point} (hT : (N : ℤ) • T = 0) :
    (Hom.ofIsogeny χ.dual).pointMap T =
      (Hom.ofIsogeny φ.dual).pointMap T + (Hom.ofIsogeny ψ.dual).pointMap T := by
  -- the dual images of `T` are `N`-torsion, so they are points of `W₁[N]`
  have hdual (ρ : Isogeny W₁ W₂) [Algebra.IsSeparable ρ.fieldPullback.fieldRange W₁.FunctionField] :
      (Hom.ofIsogeny ρ.dual).pointMap T ∈ Submodule.torsionBy ℤ W₁.Point (N : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr (by rw [← pointMap_dual_zsmul, hT, Hom.pointMap_zero])
  let T' : Submodule.torsionBy ℤ W₂.Point (N : ℤ) := ⟨T, (Submodule.mem_torsionBy_iff _ _).mpr hT⟩
  let Tχ : Submodule.torsionBy ℤ W₁.Point (N : ℤ) := ⟨_, hdual χ⟩
  let Tφ : Submodule.torsionBy ℤ W₁.Point (N : ℤ) := ⟨_, hdual φ⟩
  let Tψ : Submodule.torsionBy ℤ W₁.Point (N : ℤ) := ⟨_, hdual ψ⟩
  suffices h : Tχ = Tφ + Tψ from congrArg Subtype.val h
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_weilPairing_eq_zero W₁ N hN fun S ↦ ?_
  -- the images of an `N`-torsion point `S` under `φ`, `ψ`, `χ` are points of `W₂[N]`
  have himg (ρ : Isogeny W₁ W₂) [Algebra.IsSeparable ρ.fieldPullback.fieldRange W₁.FunctionField] :
      (Hom.ofIsogeny ρ).pointMap S ∈ Submodule.torsionBy ℤ W₂.Point (N : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr (by
      rw [← Hom.pointMap_zsmul, (Submodule.mem_torsionBy_iff _ _).mp S.2, Hom.pointMap_zero])
  let Sχ : Submodule.torsionBy ℤ W₂.Point (N : ℤ) := ⟨_, himg χ⟩
  let Sφ : Submodule.torsionBy ℤ W₂.Point (N : ℤ) := ⟨_, himg φ⟩
  let Sψ : Submodule.torsionBy ℤ W₂.Point (N : ℤ) := ⟨_, himg ψ⟩
  have hS : Sχ = Sφ + Sψ := Subtype.ext <| by
    rw [Submodule.coe_add]
    exact (congrArg (fun f : Hom W₁ W₂ ↦ f.pointMap S) hχ).trans (Hom.add_pointMap _ _ _)
  -- adjointness moves the duals across the pairing, where `χ S = φ S + ψ S`
  rw [map_sub, map_add, ← χ.weilPairing_eq_weilPairing_dual N hN (S' := Sχ) (T := T') rfl rfl,
    ← φ.weilPairing_eq_weilPairing_dual N hN (S' := Sφ) (T := T') rfl rfl,
    ← ψ.weilPairing_eq_weilPairing_dual N hN (S' := Sψ) (T := T') rfl rfl, hS, map_add,
    AddMonoidHom.add_apply, sub_self]

omit [DecidableEq F] in
/-- **The dual isogeny is additive** (Silverman III.6.2(b)): if the separable isogenies `φ` and
`ψ` sum, as morphisms, to the separable isogeny `χ`, then `χ̂ = φ̂ + ψ̂`. -/
theorem ofIsogeny_dual_add (hχ : Hom.ofIsogeny χ = Hom.ofIsogeny φ + Hom.ofIsogeny ψ) :
    Hom.ofIsogeny χ.dual = Hom.ofIsogeny φ.dual + Hom.ofIsogeny ψ.dual := by
  classical
  refine Hom.ext_pointMap_of_prime_zsmul_eq_zero fun N hp hN T hT ↦ ?_
  have : NeZero N := ⟨hp.ne_zero⟩
  exact (pointMap_dual_eq_add_of_zsmul_eq_zero φ ψ χ hχ hN hT).trans
    (Hom.add_pointMap _ _ _).symm

end TauCeti.Isogeny

end
