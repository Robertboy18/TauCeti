/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.CongrRight
public import TauCeti.GroupTheory.DoubleCoset.Map

/-!
# Changing the reference family of a restricted product

Two families of reference subgroups that agree at all but finitely many indices define the same
restricted product up to a coordinatewise-identity isomorphism, which is a homeomorphism for
every pair of families.  This file records that isomorphism, its coordinate formulas in both
directions, its continuity, its coherence laws, and its naturality with respect to componentwise
maps.  It is the case of `restrictedProductCongrRight` in which every coordinate equivalence is
the identity.

The isomorphism identifies the ambient restricted products only.  It does not carry the
everywhere-integral subgroup of one family to that of the other, because the coordinate
condition changes at the finitely many indices where the families differ:
`exists_map_integralSubgroup_ne` exhibits a family of copies of `Multiplicative ℤ` where the two
subgroups differ.  For this reason the induced bijection of double-coset spaces,
`doubleCosetCongr`, is stated along the transported subgroups rather than along the integral
subgroup of the new family.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v w

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

/-- The multiplicative equivalence between the restricted products with respect to two reference
families that agree at all but finitely many indices. It is the identity in every coordinate. -/
def restrictedProductCongr (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i) :
    (Πʳ i, [G i, (U i : Set (G i))]) ≃* (Πʳ i, [G i, (U' i : Set (G i))]) :=
  restrictedProductCongrRight U U' (fun i ↦ MulEquiv.refl (G i)) <| by
    filter_upwards [h] with i hi
    simp only [MulEquiv.coe_refl, hi]
    exact Set.bijOn_id _

/-- The change-of-family equivalence is the identity in every coordinate. -/
@[simp]
theorem restrictedProductCongr_apply (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i)
    (x : Πʳ i, [G i, (U i : Set (G i))]) (i : ι) :
    restrictedProductCongr U U' h x i = x i :=
  restrictedProductCongrRight_apply U U' _ _ x i

/-- The inverse of the change-of-family equivalence is the identity in every coordinate. -/
@[simp]
theorem restrictedProductCongr_symm_apply (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i)
    (y : Πʳ i, [G i, (U' i : Set (G i))]) (i : ι) :
    (restrictedProductCongr U U' h).symm y i = y i :=
  restrictedProductCongrRight_symm_apply U U' _ _ y i

/-- The change-of-family equivalence is continuous, for every pair of reference families. -/
theorem continuous_restrictedProductCongr [∀ i, TopologicalSpace (G i)]
    (U U' : ∀ i, Subgroup (G i)) (h : ∀ᶠ i in cofinite, U i = U' i) :
    Continuous (restrictedProductCongr U U' h) :=
  continuous_restrictedProductCongrRight U U' _ _ fun _ ↦ continuous_id

/-- The inverse of the change-of-family equivalence is continuous, for every pair of reference
families. -/
theorem continuous_restrictedProductCongr_symm [∀ i, TopologicalSpace (G i)]
    (U U' : ∀ i, Subgroup (G i)) (h : ∀ᶠ i in cofinite, U i = U' i) :
    Continuous (restrictedProductCongr U U' h).symm :=
  continuous_restrictedProductCongrRight_symm U U' _ _ fun _ ↦ continuous_id

/-- The change-of-family equivalence from a family to itself is the identity. -/
@[simp]
theorem restrictedProductCongr_refl (U : ∀ i, Subgroup (G i)) :
    restrictedProductCongr U U (.of_forall fun _ ↦ rfl) =
      MulEquiv.refl (Πʳ i, [G i, (U i : Set (G i))]) := by
  ext x i
  simp

/-- The inverse of the change-of-family equivalence is the change-of-family equivalence in the
opposite direction. -/
theorem restrictedProductCongr_symm (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i) :
    (restrictedProductCongr U U' h).symm =
      restrictedProductCongr U' U (h.mono fun _ hi ↦ hi.symm) := by
  ext x i
  simp

/-- Two successive changes of family compose to the change of family between the outer two
families. -/
@[simp]
theorem restrictedProductCongr_trans (U U' U'' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i) (h' : ∀ᶠ i in cofinite, U' i = U'' i) :
    (restrictedProductCongr U U' h).trans (restrictedProductCongr U' U'' h') =
      restrictedProductCongr U U'' (by
        filter_upwards [h, h'] with i hi hi'
        exact hi.trans hi') := by
  ext x i
  simp

/-- Naturality of the change-of-family equivalence with respect to componentwise maps: changing
the family before or after applying a componentwise map gives the same homomorphism. -/
theorem restrictedProductCongr_naturality {H : ι → Type w} [∀ i, Group (H i)]
    (U U' : ∀ i, Subgroup (G i)) (V V' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i →* H i)
    (hφ : ∀ᶠ i in cofinite, Set.MapsTo (φ i) (U i) (V i))
    (hφ' : ∀ᶠ i in cofinite, Set.MapsTo (φ i) (U' i) (V' i))
    (h : ∀ᶠ i in cofinite, U i = U' i) (h' : ∀ᶠ i in cofinite, V i = V' i) :
    (restrictedProductCongr V V' h').toMonoidHom.comp (restrictedProductMap U V φ hφ) =
      (restrictedProductMap U' V' φ hφ').comp (restrictedProductCongr U U' h).toMonoidHom := by
  ext x i
  simp

/-- Transport of a double-coset space along a change of reference family. The subgroups on the
right are the images of those on the left under `restrictedProductCongr`, not the integral
subgroups of the new family; see `exists_map_integralSubgroup_ne`. -/
def doubleCosetCongr (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i)
    (Γ K : Subgroup (Πʳ i, [G i, (U i : Set (G i))])) :
    DoubleCoset.Quotient (Γ : Set (Πʳ i, [G i, (U i : Set (G i))])) K ≃
      DoubleCoset.Quotient
        (Γ.map (restrictedProductCongr U U' h :
            (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]) :
          Set (Πʳ i, [G i, (U' i : Set (G i))]))
        (K.map (restrictedProductCongr U U' h :
            (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]) :
          Set (Πʳ i, [G i, (U' i : Set (G i))])) :=
  DoubleCoset.quotientCongr Γ K (restrictedProductCongr U U' h) rfl rfl

/-- The transported double-coset space sends the double coset of `x` to the double coset of its
image under the change-of-family equivalence.

Not a `simp` lemma: the type of `doubleCosetCongr` mentions the coercions `↑(Γ.map e)` and
`↑(K.map e)`, which `Subgroup.coe_map` rewrites, so the left-hand side is not in simp-normal form.
Use `DoubleCoset.quotientCongr_apply_mk` after unfolding, or rewrite with this lemma directly. -/
theorem doubleCosetCongr_apply_mk (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i)
    (Γ K : Subgroup (Πʳ i, [G i, (U i : Set (G i))]))
    (x : Πʳ i, [G i, (U i : Set (G i))]) :
    doubleCosetCongr U U' h Γ K (DoubleCoset.mk Γ K x) =
      DoubleCoset.mk
        (Γ.map (restrictedProductCongr U U' h :
          (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]))
        (K.map (restrictedProductCongr U U' h :
          (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]))
        (restrictedProductCongr U U' h x) :=
  DoubleCoset.quotientCongr_apply_mk Γ K _ rfl rfl x

/-- The inverse of the transported double-coset space sends the double coset of `y` to the double
coset of its image under the inverse change-of-family equivalence.

Not a `simp` lemma, for the same reason as `doubleCosetCongr_apply_mk`. -/
theorem doubleCosetCongr_symm_apply_mk (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i)
    (Γ K : Subgroup (Πʳ i, [G i, (U i : Set (G i))]))
    (y : Πʳ i, [G i, (U' i : Set (G i))]) :
    (doubleCosetCongr U U' h Γ K).symm
        (DoubleCoset.mk
          (Γ.map (restrictedProductCongr U U' h :
            (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]))
          (K.map (restrictedProductCongr U U' h :
            (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]))
          y) =
      DoubleCoset.mk Γ K ((restrictedProductCongr U U' h).symm y) :=
  DoubleCoset.quotientCongr_symm_apply_mk Γ K _ rfl rfl y

/-- The change-of-family equivalence need not carry the everywhere-integral subgroup onto the
everywhere-integral subgroup of the new family. The witness uses copies of `Multiplicative ℤ`
indexed by `ℕ`, with the first family everywhere `⊤` and the second family equal to `⊥` at zero
and `⊤` elsewhere. -/
theorem exists_map_integralSubgroup_ne :
    ∃ (U U' : ℕ → Subgroup (Multiplicative ℤ)) (h : ∀ᶠ i in cofinite, U i = U' i),
      (integralSubgroup U).map (restrictedProductCongr U U' h) ≠ integralSubgroup U' := by
  let U : ℕ → Subgroup (Multiplicative ℤ) := fun _ ↦ ⊤
  let U' : ℕ → Subgroup (Multiplicative ℤ) := fun i ↦ if i = 0 then ⊥ else ⊤
  have h : ∀ᶠ i in cofinite, U i = U' i := by
    filter_upwards [eventually_cofinite_ne 0] with i hi
    simp [U, U', hi]
  refine ⟨U, U', h, fun heq ↦ ?_⟩
  let x : Πʳ i, [Multiplicative ℤ, (U i : Set (Multiplicative ℤ))] :=
    ⟨fun _ ↦ Multiplicative.ofAdd 1, .of_forall fun i ↦ by simp [U]⟩
  have hx : restrictedProductCongr U U' h x ∈ integralSubgroup U' := by
    rw [← heq]
    exact Subgroup.mem_map_of_mem _ ((mem_integralSubgroup U x).mpr fun i ↦ by simp [U])
  have h0 := (mem_integralSubgroup U' _).mp hx 0
  rw [restrictedProductCongr_apply] at h0
  simp [U', x] at h0

end TauCeti
