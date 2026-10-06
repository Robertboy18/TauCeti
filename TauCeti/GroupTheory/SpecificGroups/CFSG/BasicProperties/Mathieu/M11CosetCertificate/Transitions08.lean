/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits4
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions4
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Eligibility
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership07

/-!
# M11 coset deductions: transition group 08

Each block proves word eligibility and a transition between two literal bit states.
The individual computations remain separate so each kernel check covers at most
32 deductions. Their composition is proved in `M11CosetCertificate`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem eligible064 : deductions064.all eligible = true := by
  simp only [deductions064, List.all_cons, List.all_nil, eligible, r451_mem, r452_mem, r453_mem,
    r454_mem, r455_mem, r456_mem, r457_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_064 :
    deductions064.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits064 =
      bits065 := by
  decide +kernel

theorem eligible065 : deductions065.all eligible = true := by
  simp only [deductions065, List.all_cons, List.all_nil, eligible, r457_mem, r458_mem, r459_mem,
    r460_mem, r461_mem, r462_mem, r463_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_065 :
    deductions065.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits065 =
      bits066 := by
  decide +kernel

theorem eligible066 : deductions066.all eligible = true := by
  simp only [deductions066, List.all_cons, List.all_nil, eligible, r463_mem, r464_mem, r465_mem,
    r466_mem, r467_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_066 :
    deductions066.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits066 =
      bits067 := by
  decide +kernel

theorem eligible067 : deductions067.all eligible = true := by
  simp only [deductions067, List.all_cons, List.all_nil, eligible, r467_mem, r468_mem, r469_mem,
    r470_mem, r471_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_067 :
    deductions067.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits067 =
      bits068 := by
  decide +kernel

theorem eligible068 : deductions068.all eligible = true := by
  simp only [deductions068, List.all_cons, List.all_nil, eligible, r471_mem, r472_mem, r473_mem,
    r474_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_068 :
    deductions068.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits068 =
      bits069 := by
  decide +kernel

theorem eligible069 : deductions069.all eligible = true := by
  simp only [deductions069, List.all_cons, List.all_nil, eligible, r474_mem, r475_mem, r476_mem,
    r477_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_069 :
    deductions069.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits069 =
      bits070 := by
  decide +kernel

theorem eligible070 : deductions070.all eligible = true := by
  simp only [deductions070, List.all_cons, List.all_nil, eligible, r477_mem, r478_mem, r479_mem,
    r480_mem, r481_mem, r482_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_070 :
    deductions070.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits070 =
      bits071 := by
  decide +kernel

theorem eligible071 : deductions071.all eligible = true := by
  simp only [deductions071, List.all_cons, List.all_nil, eligible, r482_mem, r483_mem, r484_mem,
    r485_mem, r486_mem, r487_mem, r488_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_071 :
    deductions071.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits071 =
      bits072 := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
