/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Module
public import TauCeti.Topology.Algebra.Group.Profinite.Free.PadicInt
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.PadicInt

/-!
# The rank-one pro-`p` chain as free p-adic modules

The free pro-`p` group on one generator and the maximal pro-`p` quotient of the profinite
integers carry their canonical `ℤ_[p]`-module structures from p-adic exponentiation. The
established group isomorphisms with the additive group of `ℤ_[p]` become continuous linear
equivalences for these actions, sending the distinguished generators to `1`.

These generators are one-element bases. Both canonical modules are free of rank one, and
their module ranks agree with their topological generator ranks. The equivalences identify
the free generator, the class of the generator of the profinite integers, and `1 : ℤ_[p]`.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

namespace freeProP

variable (X : Type) [Unique X]

/-- A free pro-`p` group on one generator is commutative. -/
noncomputable instance : CommGroup (freeProP p X) :=
  { (inferInstance : Group (freeProP p X)) with
    mul_comm := fun x y ↦ (equivPadicInt p X).injective (by simp [mul_comm]) }

/-- The canonical p-adic action makes the free pro-`p` group on one generator continuously
linearly equivalent to `ℤ_[p]`, with the generator as the unit vector. -/
noncomputable def continuousLinearEquivPadicInt :
    letI := (isProP_freeProP p X).module
    Additive (freeProP p X) ≃L[ℤ_[p]] ℤ_[p] := by
  letI := (isProP_freeProP p X).module
  letI := (isProP_freeProP p X).continuousSMul_module
  exact (MulEquiv.toAdditiveLeft (equivPadicInt p X).toMulEquiv).toPadicIntLinearEquiv p
    (continuous_toAdd.comp ((equivPadicInt p X).continuous.comp continuous_toMul))
    (continuous_ofMul.comp ((equivPadicInt p X).symm.continuous.comp continuous_ofAdd))

/-- The linear equivalence has the same underlying map as the rank-one group isomorphism. -/
@[simp]
theorem continuousLinearEquivPadicInt_apply (x : Additive (freeProP p X)) :
    letI := (isProP_freeProP p X).module
    continuousLinearEquivPadicInt p X x = (equivPadicInt p X x.toMul).toAdd := by
  let := (isProP_freeProP p X).module
  let := (isProP_freeProP p X).continuousSMul_module
  exact congrFun (AddEquiv.coe_toPadicIntLinearEquiv p
    (MulEquiv.toAdditiveLeft (equivPadicInt p X).toMulEquiv) _ _) x

/-- The linear equivalence sends the free generator to `1`. -/
theorem continuousLinearEquivPadicInt_of (x : X) :
    letI := (isProP_freeProP p X).module
    continuousLinearEquivPadicInt p X (Additive.ofMul (of x)) = 1 := by
  simp

/-- The inverse coordinate map is scalar multiplication of the free generator. -/
@[simp]
theorem continuousLinearEquivPadicInt_symm_apply (l : ℤ_[p]) :
    letI := (isProP_freeProP p X).module
    (continuousLinearEquivPadicInt p X).symm l =
      l • Additive.ofMul (of (default : X)) := by
  let := (isProP_freeProP p X).module
  apply (continuousLinearEquivPadicInt p X).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul, continuousLinearEquivPadicInt_of]
  simp

/-- The unique free generator is a basis for the canonical `ℤ_[p]`-module. -/
noncomputable def basisPadicInt :
    letI := (isProP_freeProP p X).module
    Module.Basis X ℤ_[p] (Additive (freeProP p X)) := by
  letI := (isProP_freeProP p X).module
  exact (Module.Basis.singleton X ℤ_[p]).map
    (continuousLinearEquivPadicInt p X).symm.toLinearEquiv

/-- The basis vector is the original free generator. -/
@[simp]
theorem basisPadicInt_apply (x : X) :
    letI := (isProP_freeProP p X).module
    basisPadicInt p X x = Additive.ofMul (of x) := by
  let := (isProP_freeProP p X).module
  simp [basisPadicInt, Unique.eq_default x]

/-- The free pro-`p` group on one generator is free for its canonical p-adic action. -/
theorem module_free :
    letI := (isProP_freeProP p X).module
    Module.Free ℤ_[p] (Additive (freeProP p X)) := by
  let := (isProP_freeProP p X).module
  exact Module.Free.of_basis (basisPadicInt p X)

/-- The canonical p-adic module on the free pro-`p` group on one generator has rank one. -/
@[simp]
theorem module_finrank :
    letI := (isProP_freeProP p X).module
    Module.finrank ℤ_[p] (Additive (freeProP p X)) = 1 := by
  let := (isProP_freeProP p X).module
  exact (continuousLinearEquivPadicInt p X).toLinearEquiv.finrank_eq.trans
    (CommSemiring.finrank_self ℤ_[p])

/-- The cardinal-valued module rank is one. -/
@[simp]
theorem module_rank :
    letI := (isProP_freeProP p X).module
    Module.rank ℤ_[p] (Additive (freeProP p X)) = 1 := by
  let := (isProP_freeProP p X).module
  exact Module.rank_eq_one_iff_finrank_eq_one.mpr (module_finrank p X)

/-- The topological generator rank and the canonical p-adic module rank agree. -/
theorem topologicalGeneratorRank_eq_module_rank :
    letI := (isProP_freeProP p X).module
    topologicalGeneratorRank (freeProP p X) =
      Module.rank ℤ_[p] (Additive (freeProP p X)) := by
  simp

end freeProP

namespace zHat

/-- The maximal pro-`p` quotient of the profinite integers is commutative. -/
noncomputable instance : CommGroup (maximalProPQuotient p zHat) :=
  { (inferInstance : Group (maximalProPQuotient p zHat)) with
    mul_comm := fun x y ↦
      (maximalProPQuotientEquivPadicInt p).injective (by simp [mul_comm]) }

/-- The canonical p-adic action makes the maximal pro-`p` quotient of the profinite integers
continuously linearly equivalent to `ℤ_[p]`, with the class of the generator as unit vector. -/
noncomputable def maximalProPQuotientContinuousLinearEquivPadicInt :
    letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
    Additive (maximalProPQuotient p zHat) ≃L[ℤ_[p]] ℤ_[p] := by
  letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
  letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).continuousSMul_module
  exact AddEquiv.toPadicIntLinearEquiv p
    (MulEquiv.toAdditiveLeft (maximalProPQuotientEquivPadicInt p).toMulEquiv)
    (continuous_toAdd.comp
      ((maximalProPQuotientEquivPadicInt p).continuous.comp continuous_toMul))
    (continuous_ofMul.comp
      ((maximalProPQuotientEquivPadicInt p).symm.continuous.comp continuous_ofAdd))

/-- The linear equivalence has the same underlying map as the quotient group isomorphism. -/
@[simp]
theorem maximalProPQuotientContinuousLinearEquivPadicInt_apply
    (x : Additive (maximalProPQuotient p zHat)) :
    letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
    maximalProPQuotientContinuousLinearEquivPadicInt p x =
      (maximalProPQuotientEquivPadicInt p x.toMul).toAdd := by
  let := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
  let := (isProP_maximalProPQuotient (p := p) (G := zHat)).continuousSMul_module
  exact congrFun (AddEquiv.coe_toPadicIntLinearEquiv p
    (MulEquiv.toAdditiveLeft (maximalProPQuotientEquivPadicInt p).toMulEquiv) _ _) x

/-- The linear equivalence sends the class of the generator of the profinite integers to `1`. -/
theorem maximalProPQuotientContinuousLinearEquivPadicInt_gen :
    letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
    maximalProPQuotientContinuousLinearEquivPadicInt p
      (Additive.ofMul (gen : maximalProPQuotient p zHat)) = 1 := by
  simp

/-- The inverse coordinate map is scalar multiplication of the class of the generator. -/
@[simp]
theorem maximalProPQuotientContinuousLinearEquivPadicInt_symm_apply (l : ℤ_[p]) :
    letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
    (maximalProPQuotientContinuousLinearEquivPadicInt p).symm l =
      l • Additive.ofMul (gen : maximalProPQuotient p zHat) := by
  let := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
  apply (maximalProPQuotientContinuousLinearEquivPadicInt p).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul,
    maximalProPQuotientContinuousLinearEquivPadicInt_gen]
  simp

/-- The class of the generator of the profinite integers is a basis of their maximal pro-`p`
quotient for its canonical p-adic action. -/
noncomputable def maximalProPQuotientBasisPadicInt :
    letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
    Module.Basis (Fin 1) ℤ_[p] (Additive (maximalProPQuotient p zHat)) := by
  letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
  exact (Module.Basis.singleton (Fin 1) ℤ_[p]).map
    (maximalProPQuotientContinuousLinearEquivPadicInt p).symm.toLinearEquiv

/-- The basis vector is the class of the original generator. -/
@[simp]
theorem maximalProPQuotientBasisPadicInt_apply (i : Fin 1) :
    letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
    maximalProPQuotientBasisPadicInt p i =
      Additive.ofMul (gen : maximalProPQuotient p zHat) := by
  let := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
  simp [maximalProPQuotientBasisPadicInt]

/-- The maximal pro-`p` quotient of the profinite integers is free for its canonical p-adic
action. -/
theorem maximalProPQuotient_module_free :
    letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
    Module.Free ℤ_[p] (Additive (maximalProPQuotient p zHat)) := by
  let := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
  exact Module.Free.of_basis (maximalProPQuotientBasisPadicInt p)

/-- The canonical p-adic module on the maximal pro-`p` quotient has rank one. -/
@[simp]
theorem maximalProPQuotient_module_finrank :
    letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
    Module.finrank ℤ_[p] (Additive (maximalProPQuotient p zHat)) = 1 := by
  let := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
  exact (maximalProPQuotientContinuousLinearEquivPadicInt p).toLinearEquiv.finrank_eq.trans
    (CommSemiring.finrank_self ℤ_[p])

/-- The cardinal-valued module rank of the maximal pro-`p` quotient is one. -/
@[simp]
theorem maximalProPQuotient_module_rank :
    letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
    Module.rank ℤ_[p] (Additive (maximalProPQuotient p zHat)) = 1 := by
  let := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
  exact Module.rank_eq_one_iff_finrank_eq_one.mpr (maximalProPQuotient_module_finrank p)

/-- The two notions of rank agree on the maximal pro-`p` quotient of the profinite integers. -/
theorem maximalProPQuotient_topologicalGeneratorRank_eq_module_rank :
    letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
    topologicalGeneratorRank (maximalProPQuotient p zHat) =
      Module.rank ℤ_[p] (Additive (maximalProPQuotient p zHat)) := by
  rw [topologicalGeneratorRank_congr (maximalProPQuotientEquivPadicInt p)]
  simp

end zHat

namespace freeProP

variable (X : Type) [Unique X]

/-- The rank-one universal-property chain as an equivalence of the canonical topological
p-adic modules. -/
noncomputable def continuousLinearEquivMaximalProPQuotient :
    letI := (isProP_freeProP p X).module
    letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
    Additive (freeProP p X) ≃L[ℤ_[p]] Additive (maximalProPQuotient p zHat) := by
  letI := (isProP_freeProP p X).module
  letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
  exact (continuousLinearEquivPadicInt p X).trans
    (zHat.maximalProPQuotientContinuousLinearEquivPadicInt p).symm

/-- The module chain identifies the free generator with the class of the generator of the
profinite integers. -/
@[simp]
theorem continuousLinearEquivMaximalProPQuotient_of (x : X) :
    letI := (isProP_freeProP p X).module
    letI := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
    continuousLinearEquivMaximalProPQuotient p X (Additive.ofMul (of x)) =
      Additive.ofMul (zHat.gen : maximalProPQuotient p zHat) := by
  let := (isProP_freeProP p X).module
  let := (isProP_maximalProPQuotient (p := p) (G := zHat)).module
  simp [continuousLinearEquivMaximalProPQuotient]

end freeProP

end TauCeti
