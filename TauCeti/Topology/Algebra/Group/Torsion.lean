/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The torsion subgroup under a product decomposition

Let `A` be an abelian group isomorphic to `Multiplicative (M × T)`, where `M` is a torsion-free
additive group and `T` is a torsion additive group. Then the torsion subgroup of `A` is exactly the
preimage of the factor `T`, and the quotient `A ⧸ torsion A` is identified with `M`; when the
isomorphism is a topological isomorphism, so is the identification of the quotient.

These are the statements behind the uniqueness clauses of the structure theorems for finitely
generated abelian groups and for topologically finitely generated abelian pro-`p` groups: in a
decomposition `A ≅ M × T` of this shape the factor `T` is the torsion subgroup and `M` is the
torsion-free quotient, so both are determined by `A` up to isomorphism.

## Main definitions

* `TauCeti.mem_torsion_iff_of_mulEquiv`: an element is torsion exactly when its `M`-coordinate
  vanishes.
* `TauCeti.torsionMulEquivOfMulEquiv`: the torsion subgroup of `A` is isomorphic to `T`.
* `TauCeti.torsionFactorAddEquiv`: two decompositions of `A` have isomorphic torsion factors.
* `TauCeti.quotientTorsionMulEquivOfMulEquiv`, `TauCeti.quotientTorsionContinuousMulEquiv`: the
  quotient of `A` by its torsion subgroup is isomorphic to `M`, algebraically and topologically.
-/

public section

namespace TauCeti

open CommGroup (torsion)
open Multiplicative

variable {A M T : Type*} [CommGroup A] [AddCommGroup M] [IsAddTorsionFree M] [AddCommGroup T]

/-- Under an isomorphism `A ≃* Multiplicative (M × T)` with `M` torsion-free and `T` torsion, an
element of `A` is torsion exactly when its `M`-coordinate vanishes. -/
theorem mem_torsion_iff_of_mulEquiv (hT : IsAddTorsion T) (e : A ≃* Multiplicative (M × T))
    {x : A} : x ∈ torsion A ↔ (e x).toAdd.1 = 0 := by
  have h : IsOfFinOrder (e x) ↔ IsOfFinAddOrder (e x).toAdd := by
    rw [← isOfFinOrder_ofAdd_iff, ofAdd_toAdd]
  rw [CommGroup.mem_torsion, ← Function.Injective.isOfFinOrder_iff (f := e.toMonoidHom) e.injective,
    MulEquiv.coe_toMonoidHom, h, IsOfFinAddOrder.prod_iff, isOfFinAddOrder_iff_eq_zero,
    and_iff_left (hT _)]

/-- Under an isomorphism `A ≃* Multiplicative (M × T)` with `M` torsion-free and `T` torsion, the
torsion subgroup of `A` is the factor `T`. -/
def torsionMulEquivOfMulEquiv (hT : IsAddTorsion T) (e : A ≃* Multiplicative (M × T)) :
    torsion A ≃* Multiplicative T where
  toFun x := ofAdd (e x).toAdd.2
  invFun t := ⟨e.symm (ofAdd (0, t.toAdd)), (mem_torsion_iff_of_mulEquiv hT e).2 (by simp)⟩
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    have hx' := (mem_torsion_iff_of_mulEquiv hT e).1 hx
    refine Subtype.ext (e.symm_apply_eq.2 ?_)
    simp only [toAdd_ofAdd]
    rw [← hx', Prod.mk.eta, ofAdd_toAdd]
  right_inv t := by simp
  map_mul' x y := by simp

@[simp]
theorem torsionMulEquivOfMulEquiv_apply (hT : IsAddTorsion T) (e : A ≃* Multiplicative (M × T))
    (x : torsion A) : torsionMulEquivOfMulEquiv hT e x = ofAdd (e x).toAdd.2 :=
  (rfl)

@[simp]
theorem coe_torsionMulEquivOfMulEquiv_symm_apply (hT : IsAddTorsion T)
    (e : A ≃* Multiplicative (M × T)) (t : Multiplicative T) :
    ((torsionMulEquivOfMulEquiv hT e).symm t : A) = e.symm (ofAdd (0, t.toAdd)) :=
  (rfl)

/-- Two decompositions of `A` as torsion-free times torsion have isomorphic torsion factors: both
are the torsion subgroup of `A`. -/
def torsionFactorAddEquiv {M' T' : Type*} [AddCommGroup M'] [IsAddTorsionFree M']
    [AddCommGroup T'] (hT : IsAddTorsion T) (hT' : IsAddTorsion T')
    (e : A ≃* Multiplicative (M × T)) (e' : A ≃* Multiplicative (M' × T')) : T ≃+ T' :=
  AddEquiv.toMultiplicative.symm
    ((torsionMulEquivOfMulEquiv hT e).symm.trans (torsionMulEquivOfMulEquiv hT' e'))

/-- Under an isomorphism `A ≃* Multiplicative (M × T)` with `M` torsion-free and `T` torsion, the
quotient of `A` by its torsion subgroup is the factor `M`. -/
noncomputable def quotientTorsionMulEquivOfMulEquiv (hT : IsAddTorsion T)
    (e : A ≃* Multiplicative (M × T)) : A ⧸ torsion A ≃* Multiplicative M :=
  QuotientGroup.liftEquiv (torsion A)
    (φ := (AddMonoidHom.fst M T).toMultiplicative.comp e.toMonoidHom)
    (fun v ↦ ⟨e.symm (ofAdd (v.toAdd, 0)), by simp [AddMonoidHom.coe_toMultiplicative]⟩)
    (by
      ext x
      rw [MonoidHom.mem_ker, mem_torsion_iff_of_mulEquiv hT e]
      simp)

@[simp]
theorem quotientTorsionMulEquivOfMulEquiv_mk (hT : IsAddTorsion T)
    (e : A ≃* Multiplicative (M × T)) (x : A) :
    quotientTorsionMulEquivOfMulEquiv hT e (x : A ⧸ torsion A) = ofAdd (e x).toAdd.1 := by
  simp [quotientTorsionMulEquivOfMulEquiv, QuotientGroup.liftEquiv,
    AddMonoidHom.coe_toMultiplicative]

@[simp]
theorem quotientTorsionMulEquivOfMulEquiv_symm_apply (hT : IsAddTorsion T)
    (e : A ≃* Multiplicative (M × T)) (v : Multiplicative M) :
    (quotientTorsionMulEquivOfMulEquiv hT e).symm v =
      ((e.symm (ofAdd (v.toAdd, 0)) : A) : A ⧸ torsion A) :=
  (quotientTorsionMulEquivOfMulEquiv hT e).injective (by simp)

section Topology

variable [TopologicalSpace A] [TopologicalSpace M] [TopologicalSpace T]

/-- Under a topological isomorphism `A ≃ₜ* Multiplicative (M × T)` with `M` torsion-free and `T`
torsion, the quotient of `A` by its torsion subgroup is topologically isomorphic to `M`. -/
noncomputable def quotientTorsionContinuousMulEquiv (hT : IsAddTorsion T)
    (e : A ≃ₜ* Multiplicative (M × T)) : A ⧸ torsion A ≃ₜ* Multiplicative M where
  toMulEquiv := quotientTorsionMulEquivOfMulEquiv hT e.toMulEquiv
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 <|
    (continuous_ofAdd.comp (continuous_fst.comp (continuous_toAdd.comp e.continuous))).congr
      fun x ↦ (quotientTorsionMulEquivOfMulEquiv_mk hT e.toMulEquiv x).symm
  continuous_invFun :=
    (QuotientGroup.continuous_mk.comp (e.symm.continuous.comp
      (continuous_ofAdd.comp (continuous_toAdd.prodMk continuous_const)))).congr
      fun v ↦ (quotientTorsionMulEquivOfMulEquiv_symm_apply hT e.toMulEquiv v).symm

@[simp]
theorem quotientTorsionContinuousMulEquiv_mk (hT : IsAddTorsion T)
    (e : A ≃ₜ* Multiplicative (M × T)) (x : A) :
    quotientTorsionContinuousMulEquiv hT e (x : A ⧸ torsion A) = ofAdd (e x).toAdd.1 :=
  quotientTorsionMulEquivOfMulEquiv_mk hT e.toMulEquiv x

@[simp]
theorem quotientTorsionContinuousMulEquiv_symm_apply (hT : IsAddTorsion T)
    (e : A ≃ₜ* Multiplicative (M × T)) (v : Multiplicative M) :
    (quotientTorsionContinuousMulEquiv hT e).symm v =
      ((e.symm (ofAdd (v.toAdd, 0)) : A) : A ⧸ torsion A) :=
  quotientTorsionMulEquivOfMulEquiv_symm_apply hT e.toMulEquiv v

end Topology

end TauCeti
