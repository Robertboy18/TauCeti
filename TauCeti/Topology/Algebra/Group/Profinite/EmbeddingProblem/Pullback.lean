/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Of.Surjective
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Basic
public import TauCeti.Topology.Algebra.GroupExtension.Profinite

/-!
# The pullback extension of a finite embedding problem

For a finite embedding problem `G → Q ← E`, the pullback consists of pairs `(g, e)` with
`π g = α e`. Its projection to `G` is an extension by `ker α`. A continuous splitting of this
extension is equivalent to a solution of the embedding problem.

When `ker α` is abelian, conjugation descends to an action of `Q` on the kernel. Restricting
along `π` gives the coefficient action of `G` induced by the pullback extension.
-/

public section

namespace TauCeti.FiniteEmbeddingProblem

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (P : FiniteEmbeddingProblem.{u, v, w} G)

/-- The subgroup of compatible pairs in an embedding problem. -/
def pullback : Subgroup (G × P.E) :=
  (P.π.comp (MonoidHom.fst G P.E)).eqLocus (P.α.comp (MonoidHom.snd G P.E))

@[simp]
theorem mem_pullback (x : G × P.E) : x ∈ P.pullback ↔ P.π x.1 = P.α x.2 :=
  Iff.rfl

/-- The projection of the pullback extension to its base. -/
def pullbackFst : P.pullback →* G :=
  (MonoidHom.fst G P.E).domRestrict P.pullback

/-- The map from the pullback to the finite group of the embedding problem. -/
def pullbackSnd : P.pullback →* P.E :=
  (MonoidHom.snd G P.E).domRestrict P.pullback

@[simp]
theorem pullbackFst_apply (x : P.pullback) : P.pullbackFst x = x.1.1 :=
  (rfl)

@[simp]
theorem pullbackSnd_apply (x : P.pullback) : P.pullbackSnd x = x.1.2 :=
  (rfl)

/-- Surjectivity of `α` makes the pullback projection surjective. -/
theorem pullbackFst_surjective : Function.Surjective P.pullbackFst := by
  intro g
  obtain ⟨e, he⟩ := P.α_surjective (P.π g)
  exact ⟨⟨(g, e), he.symm⟩, rfl⟩

/-- The kernel of the pullback projection is the original kernel, by `e ↦ (1, e)`. -/
def kernelEquivPullbackKer : P.α.ker ≃* P.pullbackFst.ker where
  toFun n := ⟨⟨(1, n), by simpa using n.property.symm⟩, rfl⟩
  invFun x := ⟨x.1.1.2, by
    change P.α x.1.1.2 = 1
    rw [← (P.mem_pullback _).mp x.1.property]
    change P.π (P.pullbackFst x.1) = 1
    rw [x.property, map_one]⟩
  left_inv _ := rfl
  right_inv x := Subtype.ext (Subtype.ext (Prod.ext x.property.symm rfl))
  map_mul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (one_mul _).symm rfl

/-- The abstract extension of `G` by `ker α` obtained by pullback along `π`. -/
def pullbackGroupExtension : GroupExtension P.α.ker P.pullback G :=
  GroupExtension.ofMulEquivKer P.pullbackFst_surjective P.kernelEquivPullbackKer

@[simp]
theorem pullbackGroupExtension_rightHom :
    P.pullbackGroupExtension.rightHom = P.pullbackFst :=
  GroupExtension.ofMulEquivKer_rightHom _ _

@[simp]
theorem pullbackGroupExtension_inl (n : P.α.ker) :
    (P.pullbackGroupExtension.inl n : G × P.E) = ((1 : G), (n : P.E)) := by
  rw [pullbackGroupExtension, GroupExtension.ofMulEquivKer_inl]
  rfl

/-- Conjugation in the pullback acts on its kernel through the second coordinate. -/
theorem coe_pullbackGroupExtension_conjAct (x : P.pullback) (n : P.α.ker) :
    (P.pullbackGroupExtension.conjAct x n : P.E) = x.1.2 * n * x.1.2⁻¹ := by
  have h := congrArg P.pullbackSnd
    (P.pullbackGroupExtension.inl_conjAct_comm (e := x) (n := n))
  simpa only [map_mul, map_inv, pullbackSnd_apply, pullbackGroupExtension_inl] using h

private theorem continuous_of_isOpen_ker {H : Type*} [Group H] [TopologicalSpace H]
    [ContinuousMul H] (f : G →* H) (hf : IsOpen (f.ker : Set G)) : Continuous f := by
  apply continuous_of_tendsto_nhds_one f
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [hf.mem_nhds (f.ker.one_mem)] with g hg
  exact hg.symm

/-- The quotient map of an embedding problem is continuous for any group topology on `Q`. -/
theorem continuous_π [TopologicalSpace P.Q] [ContinuousMul P.Q] : Continuous P.π :=
  continuous_of_isOpen_ker P.π P.isOpen_ker_π

section Topology

variable [TopologicalSpace P.E]

theorem continuous_pullbackFst : Continuous P.pullbackFst :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_pullbackSnd : Continuous P.pullbackSnd :=
  continuous_snd.comp continuous_subtype_val

theorem continuous_pullbackGroupExtension_inl : Continuous P.pullbackGroupExtension.inl := by
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, pullbackGroupExtension_inl] using
    (continuous_const.prodMk continuous_subtype_val :
      Continuous fun n : P.α.ker ↦ ((1 : G), (n : P.E)))

variable [DiscreteTopology P.E]

/-- For a discrete target, the open-kernel definition of a solution is continuity. -/
theorem isSolution_iff_continuous (β : G →* P.E) :
    P.IsSolution β ↔ Continuous β ∧ P.α.comp β = P.π := by
  rw [isSolution_iff]
  apply and_congr_left'
  exact ⟨continuous_of_isOpen_ker β,
    fun h ↦ h.isOpen_preimage {1} (isOpen_discrete _)⟩

/-- Continuous splittings of the pullback exist exactly when the embedding problem has a
solution. The solution is not required to be surjective. -/
theorem exists_splitting_iff_hasSolution :
    (∃ s : P.pullbackGroupExtension.Splitting, Continuous ⇑s) ↔
      ∃ β : G →* P.E, P.IsSolution β := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨P.pullbackSnd.comp s.toMonoidHom, (P.isSolution_iff_continuous _).mpr
      ⟨P.continuous_pullbackSnd.comp hs, ?_⟩⟩
    ext g
    change P.α (s g).1.2 = P.π g
    rw [← (P.mem_pullback _).mp (s g).property]
    congr 1
    simpa using s.rightHom_splitting g
  · rintro ⟨β, hβ⟩
    let s : P.pullbackGroupExtension.Splitting :=
      { toFun := fun g ↦ ⟨(g, β g), (DFunLike.congr_fun hβ.comp_eq g).symm⟩
        map_one' := by
          apply Subtype.ext
          exact Prod.ext rfl (map_one β)
        map_mul' := fun g h ↦ by
          apply Subtype.ext
          exact Prod.ext rfl (map_mul β g h)
        rightInverse_rightHom := fun g ↦ by simp }
    exact ⟨s, (continuous_id.prodMk
      ((P.isSolution_iff_continuous β).mp hβ).1).subtype_mk _⟩

variable [TopologicalSpace P.Q] [DiscreteTopology P.Q]

/-- The compatible-pair subgroup is closed in `G × E`. -/
theorem isClosed_pullback : IsClosed (P.pullback : Set (G × P.E)) :=
  isClosed_eq (P.continuous_π.comp continuous_fst)
    ((continuous_of_discreteTopology : Continuous P.α).comp continuous_snd)

/-- Over a compact base the pullback group is compact. -/
theorem compactSpace_pullback [CompactSpace G] : CompactSpace P.pullback :=
  isCompact_iff_compactSpace.mp P.isClosed_pullback.isCompact

end Topology

/-- The commutative group structure on an abelian kernel, preserving its subgroup operations. -/
@[expose, instance_reducible]
def kernelCommGroup
    (hcomm : ∀ x ∈ P.α.ker, ∀ y ∈ P.α.ker, x * y = y * x) : CommGroup P.α.ker where
  toGroup := inferInstanceAs (Group P.α.ker)
  mul_comm := fun x y ↦ Subtype.ext (hcomm x x.property y y.property)

section Abelian

variable (hcomm : ∀ x ∈ P.α.ker, ∀ y ∈ P.α.ker, x * y = y * x)

/-- Conjugation on the abelian kernel descends to the finite quotient `Q`. -/
noncomputable def kernelConj : P.Q →* MulAut P.α.ker := by
  letI := P.kernelCommGroup hcomm
  exact GroupExtension.conjActOfSection
    (GroupExtension.ofSurjective P.α_surjective).surjInvRightHom

/-- The action of the image of `e` is conjugation by `e`. -/
theorem coe_kernelConj (e : P.E) (n : P.α.ker) :
    (P.kernelConj hcomm (P.α e) n : P.E) = e * n * e⁻¹ := by
  let := P.kernelCommGroup hcomm
  let S := GroupExtension.ofSurjective P.α_surjective
  have he : S.rightHom (S.surjInvRightHom (P.α e)) = S.rightHom e := by
    simpa only [S, GroupExtension.ofSurjective_rightHom] using
      S.surjInvRightHom.rightHom_section (P.α e)
  change (GroupExtension.conjActOfSection S.surjInvRightHom (P.α e) n : P.E) = _
  rw [GroupExtension.conjActOfSection_apply,
    GroupExtension.conjAct_eq_of_rightHom_eq he]
  simpa only [S, GroupExtension.ofSurjective_inl, Subgroup.coe_subtype] using
    S.inl_conjAct_comm (e := e) (n := n)

/-- The action on the kernel obtained by restricting conjugation along `π`. -/
@[instance_reducible]
noncomputable def kernelAction : MulDistribMulAction G P.α.ker :=
  MulDistribMulAction.compHom P.α.ker ((P.kernelConj hcomm).comp P.π)

/-- The kernel action evaluates the quotient action at `π g`. -/
theorem kernelAction_smul (g : G) (n : P.α.ker) :
    letI := P.kernelAction hcomm
    g • n = P.kernelConj hcomm (P.π g) n :=
  (rfl)

/-- The pullback extension induces the restricted conjugation action on its kernel. -/
theorem pullbackGroupExtension_inducesAction :
    letI := P.kernelAction hcomm
    GroupExtension.InducesAction P.pullbackGroupExtension := by
  let := P.kernelCommGroup hcomm
  let := P.kernelAction hcomm
  let σ := P.pullbackGroupExtension.surjInvRightHom
  apply (GroupExtension.inducesAction_iff_conjActOfSection_eq σ).mpr
  ext g n
  rw [GroupExtension.conjActOfSection_apply, coe_pullbackGroupExtension_conjAct]
  change (σ g).1.2 * n * (σ g).1.2⁻¹ = (P.kernelConj hcomm (P.π g) n : P.E)
  have hg : P.α (σ g).1.2 = P.π g := by
    rw [← (P.mem_pullback _).mp (σ g).property]
    congr 1
    simpa using σ.rightHom_section g
  rw [← hg, coe_kernelConj]

variable [TopologicalSpace P.E] [DiscreteTopology P.E]
  [TopologicalSpace P.Q] [DiscreteTopology P.Q]

/-- The kernel action is continuous because it factors through the finite discrete quotient. -/
theorem continuousSMul_kernelAction :
    letI := P.kernelAction hcomm
    ContinuousSMul G P.α.ker := by
  let := P.kernelAction hcomm
  constructor
  change Continuous fun x : G × P.α.ker ↦ P.kernelConj hcomm (P.π x.1) x.2
  exact (continuous_of_discreteTopology :
    Continuous fun x : P.Q × P.α.ker ↦ P.kernelConj hcomm x.1 x.2).comp
    ((P.continuous_π.comp continuous_fst).prodMk continuous_snd)

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The profinite pullback extension of an embedding problem with abelian kernel, equipped with
the conjugation action restricted along `π`. -/
noncomputable abbrev pullbackExtension :
    letI := P.kernelCommGroup hcomm
    letI := P.kernelAction hcomm
    ProfiniteGroupExtension G P.α.ker := by
  letI := P.kernelCommGroup hcomm
  letI := P.kernelAction hcomm
  letI := P.compactSpace_pullback
  exact
    { E := P.pullback
      toGroupExtension := P.pullbackGroupExtension
      continuous_inl := P.continuous_pullbackGroupExtension_inl
      continuous_rightHom := by simpa using P.continuous_pullbackFst
      inducesAction := P.pullbackGroupExtension_inducesAction hcomm }

end Abelian

end TauCeti.FiniteEmbeddingProblem
