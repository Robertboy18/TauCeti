/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous maps on a one-point compactification vanishing at infinity

Let `S` be a discrete space and `M` a discrete topological module. A continuous map from the
one-point compactification `S⁺` of `S` to `M` that vanishes at `∞` is determined by its values on
`S`, and these values form a finitely supported function: continuity at `∞` says that all but
finitely many of them are `0`. Conversely a finitely supported function `S →₀ M` extends by `0` at
`∞` to a continuous map on `S⁺`. The two constructions are the mutually inverse linear maps of
`TauCeti.OnePoint.finsuppLinearEquivKerEvalInfty`, an isomorphism between `S →₀ M` and the
kernel of evaluation at `∞` on `C(S⁺, M)`.

## Main definitions

* `TauCeti.OnePoint.continuousMapOfFinsupp`: the extension by `0` at `∞` of a finitely supported
  function on a discrete space, as a continuous map on the one-point compactification.
* `TauCeti.OnePoint.finsuppLinearEquivKerEvalInfty`: the linear isomorphism between `S →₀ M` and
  the continuous maps `S⁺ → M` vanishing at `∞`, for `S` and `M` discrete.
* `TauCeti.ContinuousMap.coe_apply_eq_zero_of_mem_ker_evalCLM`: a continuous map in the kernel of
  evaluation at a point vanishes there, stated with the evaluation written as a function value.
-/

public section

open Filter Topology
open scoped OnePoint

namespace TauCeti

namespace OnePoint

universe u v

variable {S : Type u} [TopologicalSpace S] [DiscreteTopology S]

/-- A continuous map from the one-point compactification of a discrete space to a discrete space
takes the value `f ∞` at all but finitely many points of `S`. -/
theorem finite_setOf_apply_coe_ne_apply_infty {Y : Type*} [TopologicalSpace Y]
    [DiscreteTopology Y] (f : C(OnePoint S, Y)) : {s : S | f s ≠ f ∞}.Finite := by
  have h := (_root_.OnePoint.continuous_iff_from_discrete f).mp f.continuous
  rw [nhds_discrete, tendsto_pure] at h
  exact eventually_cofinite.mp h

section Zero

variable (M : Type v) [Zero M] [TopologicalSpace M] [DiscreteTopology M]

/-- The support of a finitely supported function `S →₀ M` is finite, so its extension by `0` at
`∞` is continuous on the one-point compactification of the discrete space `S`. -/
noncomputable def continuousMapOfFinsupp (g : S →₀ M) : C(OnePoint S, M) :=
  _root_.OnePoint.continuousMapMkDiscrete g 0 <| by
    rw [nhds_discrete, tendsto_pure, eventually_cofinite]
    exact g.hasFiniteSupport

@[simp]
theorem continuousMapOfFinsupp_apply_coe (g : S →₀ M) (s : S) :
    continuousMapOfFinsupp M g s = g s :=
  (rfl)

@[simp]
theorem continuousMapOfFinsupp_apply_infty (g : S →₀ M) : continuousMapOfFinsupp M g ∞ = 0 :=
  (rfl)

end Zero

section Module

variable (R : Type*) [Semiring R]
variable (M : Type v) [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M] [Module R M]
  [ContinuousConstSMul R M]

/-- A continuous map in the kernel of evaluation at a point vanishes there. -/
theorem _root_.TauCeti.ContinuousMap.coe_apply_eq_zero_of_mem_ker_evalCLM {α : Type*}
    [TopologicalSpace α] (x : α) (f : (ContinuousMap.evalCLM R x : C(α, M) →L[R] M).ker) :
    (f : C(α, M)) x = 0 :=
  (ContinuousMap.evalCLM_apply R x (f : C(α, M))).symm.trans (LinearMap.mem_ker.mp f.2)

variable (S) [DiscreteTopology M]

/-- **Continuous maps vanishing at infinity are finitely supported functions.** For a discrete
space `S` and a discrete topological module `M`, restriction to `S` identifies the continuous maps
`S⁺ → M` vanishing at `∞` with the finitely supported functions `S →₀ M`, as `R`-modules. The
inverse extends a finitely supported function by `0` at `∞`. -/
noncomputable def finsuppLinearEquivKerEvalInfty :
    (S →₀ M) ≃ₗ[R] (ContinuousMap.evalCLM R (∞ : OnePoint S) : C(OnePoint S, M) →L[R] M).ker where
  toFun g := ⟨continuousMapOfFinsupp M g, by simp⟩
  map_add' g₁ g₂ := Subtype.ext <| ContinuousMap.ext fun x ↦ by
    induction x using OnePoint.rec <;> simp
  map_smul' c g := Subtype.ext <| ContinuousMap.ext fun x ↦ by
    induction x using OnePoint.rec <;> simp
  invFun f := Finsupp.ofSupportFinite (fun s ↦ f.1 s) <| by
    have h := finite_setOf_apply_coe_ne_apply_infty f.1
    rwa [ContinuousMap.coe_apply_eq_zero_of_mem_ker_evalCLM R M ∞ f] at h
  left_inv g := by
    ext s
    exact congrFun Finsupp.ofSupportFinite_coe s
  right_inv f := Subtype.ext <| ContinuousMap.ext fun x ↦ by
    induction x using OnePoint.rec with
    | infty => simp [ContinuousMap.coe_apply_eq_zero_of_mem_ker_evalCLM R M ∞ f]
    | coe s =>
      simp only [continuousMapOfFinsupp_apply_coe]
      exact congrFun Finsupp.ofSupportFinite_coe s

@[simp]
theorem coe_finsuppLinearEquivKerEvalInfty_apply (g : S →₀ M) :
    ((finsuppLinearEquivKerEvalInfty S R M g :
      (ContinuousMap.evalCLM R (∞ : OnePoint S) : C(OnePoint S, M) →L[R] M).ker) :
        C(OnePoint S, M)) =
      continuousMapOfFinsupp M g :=
  (rfl)

@[simp]
theorem finsuppLinearEquivKerEvalInfty_symm_apply
    (f : (ContinuousMap.evalCLM R (∞ : OnePoint S) : C(OnePoint S, M) →L[R] M).ker) (s : S) :
    (finsuppLinearEquivKerEvalInfty S R M).symm f s = (f : C(OnePoint S, M)) s :=
  (rfl)

end Module

end OnePoint

end TauCeti
