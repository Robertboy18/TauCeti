/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.WeightedCycle.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Fixed vectors of a weighted cycle on a basis

An enumeration of a basis and the actual weighted-cycle action equations for a
linear endomorphism identify its fixed submodule with the annihilator of monodromy
minus one. The inverse is the basis expansion with prefix-product coefficients.
This consumes a supplied basis and action; it does not construct a root-orbit basis.
The enumeration exhausts the basis, so the module consists of one cycle.

Roadmap: ReductiveGroups
-/

@[expose] public section

namespace TauCeti.WeightedCycle

variable {A V ι : Type*} [CommRing A] [AddCommGroup V] [Module A V] {n : ℕ}

/-- Basis coordinates intertwine an actual weighted-cycle action with `linearMap`.
The enumeration is used in the native basis reindexing direction `e.symm`. -/
theorem equivFun_comp_of_basis (b : Module.Basis ι A V) (e : Fin (n + 1) ≃ ι)
    (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) :
    (b.reindex e.symm).equivFun.toLinearMap ∘ₗ f =
      linearMap a ∘ₗ (b.reindex e.symm).equivFun.toLinearMap := by
  apply (b.reindex e.symm).ext
  intro i
  change (b.reindex e.symm).equivFun (f ((b.reindex e.symm) i)) =
    linearMap a ((b.reindex e.symm).equivFun ((b.reindex e.symm) i))
  have hi : f ((b.reindex e.symm) i) = a i •
      (b.reindex e.symm) (finRotate (n + 1) i) := by
    simpa using h i
  rw [hi, map_smul]
  funext j
  obtain ⟨k, rfl⟩ := (finRotate (n + 1)).surjective j
  rw [linearMap_apply_rotate]
  change a i * (b.reindex e.symm).equivFun
    ((b.reindex e.symm) (finRotate (n + 1) i)) (finRotate (n + 1) k) =
      a k * (b.reindex e.symm).equivFun ((b.reindex e.symm) i) k
  simp only [Module.Basis.equivFun_self, Equiv.apply_eq_iff_eq]
  by_cases hik : i = k
  · simp [hik]
  · simp [hik]

/-- Basis coordinates restrict to an equivalence of the actual fixed submodules. -/
noncomputable def fixedBasisEquiv (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) :
    f.fixedSubmodule ≃ₗ[A] (linearMap a (M := A)).fixedSubmodule :=
  (b.reindex e.symm).equivFun.ofSubmodules _ _ (by
    ext w
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [LinearMap.mem_fixedSubmodule_iff]
      have hc := LinearMap.congr_fun (equivFun_comp_of_basis b e a f h) v
      simpa [LinearMap.mem_fixedSubmodule_iff.mp hv] using hc.symm
    · intro hw
      refine ⟨(b.reindex e.symm).equivFun.symm w, ?_, ?_⟩
      · rw [LinearMap.mem_fixedSubmodule_iff]
        apply (b.reindex e.symm).equivFun.injective
        have hc := LinearMap.congr_fun (equivFun_comp_of_basis b e a f h)
          ((b.reindex e.symm).equivFun.symm w)
        change (b.reindex e.symm).equivFun
          (f ((b.reindex e.symm).equivFun.symm w)) =
            linearMap a ((b.reindex e.symm).equivFun
              ((b.reindex e.symm).equivFun.symm w)) at hc
        simpa only [LinearEquiv.apply_symm_apply,
          LinearMap.mem_fixedSubmodule_iff.mp hw] using hc
      · exact (b.reindex e.symm).equivFun.apply_symm_apply w)

/-- The initial basis coefficient classifies fixed vectors of the given endomorphism.
For a negative signed cycle the codomain retains every coefficient killed by two. -/
noncomputable def fixedEquivTorsionOfBasis (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) :
    f.fixedSubmodule ≃ₗ[A] Submodule.torsionBy A A ((∏ i, a i) - 1) :=
  (fixedBasisEquiv b e a f h).trans (fixedEquivTorsion a)

/-- The equivalence reads the coefficient of the enumerated initial basis vector. -/
@[simp]
theorem fixedEquivTorsionOfBasis_apply (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i)))
    (v : f.fixedSubmodule) :
    (fixedEquivTorsionOfBasis b e a f h v : A) = b.repr v.val (e 0) := by
  change (b.reindex e.symm).repr v.val 0 = _
  rw [Module.Basis.repr_reindex_apply, Equiv.symm_symm]

/-- The inverse is the literal basis expansion with prefix-product coefficients. -/
@[simp]
theorem fixedEquivTorsionOfBasis_symm_apply (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i)))
    (t : Submodule.torsionBy A A ((∏ i, a i) - 1)) :
    ((fixedEquivTorsionOfBasis b e a f h).symm t).val =
      ∑ i, (Fin.partialProd (Fin.init a) i * t.val) • b (e i) := by
  change (b.reindex e.symm).equivFun.symm
    (fun i ↦ Fin.partialProd (Fin.init a) i • t.val) = _
  simp [Module.Basis.equivFun_symm_apply]

/-- Every coefficient of a fixed vector is the corresponding prefix product times
its initial coefficient, in the original basis indexing. -/
theorem repr_eq_partialProd_mul (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i)))
    (v : f.fixedSubmodule) (i : Fin (n + 1)) :
    b.repr v.val (e i) = Fin.partialProd (Fin.init a) i * b.repr v.val (e 0) := by
  have hc := coeff_eq_partialProd_smul a (fixedBasisEquiv b e a f h v) i
  change (b.reindex e.symm).repr v.val i =
    Fin.partialProd (Fin.init a) i • (b.reindex e.symm).repr v.val 0 at hc
  simpa only [Module.Basis.repr_reindex_apply, Equiv.symm_symm, smul_eq_mul] using hc

end TauCeti.WeightedCycle
