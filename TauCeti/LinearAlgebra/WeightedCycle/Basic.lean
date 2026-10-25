/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Fixed coefficients of a weighted cycle

A weighted cycle sends coordinate `i` to coordinate `finRotate _ i`, multiplying
by `a i`. Its fixed tuples are determined by coordinate zero: the other coordinates
are its scalar multiples by the prefix products, and the closing equation is
torsion by `(∏ i, a i) - 1`. This holds over every commutative ring, with arbitrary
weights. In particular, monodromy `1` gives the coefficient module, while monodromy
`-1` gives its `2`-torsion.

This is the single-cycle coefficient calculation for ReductiveGroups 9A.1b.
The basis-facing consumer is in `WeightedCycle.Basis`.

Roadmap: ReductiveGroups
-/

@[expose] public section

namespace TauCeti.WeightedCycle

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}

/-- The weighted cyclic shift: the weight at a source coordinate travels with it. -/
def linearMap (a : Fin (n + 1) → A) : (Fin (n + 1) → M) →ₗ[A] (Fin (n + 1) → M) :=
  LinearMap.pi fun j ↦
    a ((finRotate (n + 1)).symm j) • LinearMap.proj ((finRotate (n + 1)).symm j)

/-- The coefficient at the successor of `i` comes from `i`. -/
theorem linearMap_apply_rotate (a : Fin (n + 1) → A) (v : Fin (n + 1) → M)
    (i : Fin (n + 1)) :
    linearMap a v (finRotate (n + 1) i) = a i • v i := by
  simp [linearMap]

/-- Fixed tuples satisfy the cyclic recurrence, including its closing edge. -/
theorem mem_fixedSubmodule_iff (a : Fin (n + 1) → A) (v : Fin (n + 1) → M) :
    v ∈ (linearMap a).fixedSubmodule ↔
      ∀ i, v (finRotate (n + 1) i) = a i • v i := by
  rw [LinearMap.mem_fixedSubmodule_iff]
  constructor
  · intro h i
    exact (congrFun h (finRotate (n + 1) i)).symm.trans (linearMap_apply_rotate a v i)
  · intro h
    funext j
    obtain ⟨i, rfl⟩ := (finRotate (n + 1)).surjective j
    exact (linearMap_apply_rotate a v i).trans (h i).symm

private theorem partialProd_last_mul (a : Fin (n + 1) → A) :
    Fin.partialProd (Fin.init a) (Fin.last n) * a (Fin.last n) = ∏ i, a i := by
  rw [Fin.prod_univ_castSucc]
  congr 1
  change (List.take n (List.ofFn (Fin.init a))).prod = _
  have ht : List.take (List.ofFn (Fin.init a)).length (List.ofFn (Fin.init a)) =
      List.ofFn (Fin.init a) := List.take_length
  simp only [List.length_ofFn] at ht
  rw [ht, List.prod_ofFn]
  rfl

private theorem rotate_castSucc (i : Fin n) :
    finRotate (n + 1) i.castSucc = i.succ := by
  rw [finRotate_apply, Fin.coeSucc_eq_succ]

/-- Every fixed coordinate is the initial coordinate multiplied by a prefix product. -/
theorem coeff_eq_partialProd_smul (a : Fin (n + 1) → A)
    (v : (linearMap a (M := M)).fixedSubmodule) (i : Fin (n + 1)) :
    v.val i = Fin.partialProd (Fin.init a) i • v.val 0 := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have h := (mem_fixedSubmodule_iff a v.val).mp v.property i.castSucc
    rw [rotate_castSucc] at h
    rw [h, ih, Fin.partialProd_succ]
    rw [mul_smul]
    exact smul_comm _ _ _

/-- The fixed condition is the prefix formula together with the monodromy equation. -/
theorem mem_fixedSubmodule_iff_partialProd (a : Fin (n + 1) → A)
    (v : Fin (n + 1) → M) :
    v ∈ (linearMap a).fixedSubmodule ↔
      (∀ i, v i = Fin.partialProd (Fin.init a) i • v 0) ∧
        ((∏ i, a i) - 1) • v 0 = 0 := by
  constructor
  · intro hv
    have hc : ∀ i, v i = Fin.partialProd (Fin.init a) i • v 0 :=
      coeff_eq_partialProd_smul a ⟨v, hv⟩
    refine ⟨hc, ?_⟩
    have h := (mem_fixedSubmodule_iff a v).mp hv (Fin.last n)
    rw [finRotate_last, hc (Fin.last n), ← mul_smul, mul_comm,
      partialProd_last_mul] at h
    simpa [sub_smul, sub_eq_zero] using h.symm
  · rintro ⟨hc, hm⟩
    rw [mem_fixedSubmodule_iff]
    intro i
    induction i using Fin.lastCases with
    | last =>
      rw [finRotate_last, hc (Fin.last n), ← mul_smul, mul_comm, partialProd_last_mul]
      have hm' : (∏ i, a i) • v 0 = v 0 := by
        simpa [sub_smul, sub_eq_zero] using hm
      exact hm'.symm
    | cast i =>
      rw [rotate_castSucc, hc i.succ, hc i.castSucc, Fin.partialProd_succ]
      rw [mul_smul]
      exact smul_comm _ _ _

/-- Evaluation at zero identifies fixed tuples with torsion by monodromy minus one.
The inverse has the literal prefix-product coordinates. -/
def fixedEquivTorsion (a : Fin (n + 1) → A) :
    (linearMap a (M := M)).fixedSubmodule ≃ₗ[A]
      Submodule.torsionBy A M ((∏ i, a i) - 1) where
  toFun v := ⟨v.val 0, ((mem_fixedSubmodule_iff_partialProd a v.val).mp v.property).2⟩
  invFun t := ⟨fun i ↦ Fin.partialProd (Fin.init a) i • t.val,
    (mem_fixedSubmodule_iff_partialProd a _).mpr ⟨by simp, by simp⟩⟩
  left_inv v := Subtype.ext <| funext fun i ↦ (coeff_eq_partialProd_smul a v i).symm
  right_inv t := Subtype.ext <| by simp
  map_add' v w := rfl
  map_smul' r v := rfl

/-- The forward equivalence reads the initial coefficient. -/
@[simp]
theorem fixedEquivTorsion_apply (a : Fin (n + 1) → A)
    (v : (linearMap a (M := M)).fixedSubmodule) :
    (fixedEquivTorsion a v : M) = v.val 0 :=
  rfl

/-- The inverse equivalence multiplies by the prefix products. -/
@[simp]
theorem fixedEquivTorsion_symm_apply (a : Fin (n + 1) → A)
    (t : Submodule.torsionBy A M ((∏ i, a i) - 1)) (i : Fin (n + 1)) :
    ((fixedEquivTorsion a).symm t).val i = Fin.partialProd (Fin.init a) i • t.val :=
  rfl

/-- A cycle of monodromy one contributes one copy of the coefficient module. -/
def fixedEquivOfProdEqOne (a : Fin (n + 1) → A) (h : ∏ i, a i = 1) :
    (linearMap a (M := M)).fixedSubmodule ≃ₗ[A] M :=
  (fixedEquivTorsion a).trans <|
    (LinearEquiv.ofEq _ _ (by ext t; simp [h])).trans
      (Submodule.topEquiv : (⊤ : Submodule A M) ≃ₗ[A] M)

/-- Positive monodromy: the forward map is evaluation at zero. -/
@[simp]
theorem fixedEquivOfProdEqOne_apply (a : Fin (n + 1) → A) (h : ∏ i, a i = 1)
    (v : (linearMap a (M := M)).fixedSubmodule) :
    fixedEquivOfProdEqOne a h v = v.val 0 :=
  rfl

/-- Positive monodromy: the inverse retains the prefix-product formula. -/
@[simp]
theorem fixedEquivOfProdEqOne_symm_apply (a : Fin (n + 1) → A) (h : ∏ i, a i = 1)
    (t : M) (i : Fin (n + 1)) :
    ((fixedEquivOfProdEqOne a h).symm t).val i = Fin.partialProd (Fin.init a) i • t :=
  rfl

/-- A cycle of monodromy minus one contributes the full `2`-torsion submodule. -/
def fixedEquivOfProdEqNegOne (a : Fin (n + 1) → A) (h : ∏ i, a i = -1) :
    (linearMap a (M := M)).fixedSubmodule ≃ₗ[A] Submodule.torsionBy A M 2 :=
  (fixedEquivTorsion a).trans <| LinearEquiv.ofEq _ _ (by
    ext t
    simp only [Submodule.mem_torsionBy_iff, h, sub_eq_add_neg, ← neg_add,
      neg_smul, neg_eq_zero, add_smul, one_smul, two_smul])

/-- Negative monodromy: the forward map reads a coefficient killed by two. -/
@[simp]
theorem fixedEquivOfProdEqNegOne_apply (a : Fin (n + 1) → A) (h : ∏ i, a i = -1)
    (v : (linearMap a (M := M)).fixedSubmodule) :
    (fixedEquivOfProdEqNegOne a h v : M) = v.val 0 :=
  rfl

/-- Negative monodromy: no `2`-torsion coefficient is discarded by the inverse. -/
@[simp]
theorem fixedEquivOfProdEqNegOne_symm_apply (a : Fin (n + 1) → A) (h : ∏ i, a i = -1)
    (t : Submodule.torsionBy A M 2) (i : Fin (n + 1)) :
    ((fixedEquivOfProdEqNegOne a h).symm t).val i = Fin.partialProd (Fin.init a) i • t.val :=
  rfl

end TauCeti.WeightedCycle
