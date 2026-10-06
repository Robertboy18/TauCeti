/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits5
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions5
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Eligibility
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership08

/-!
# M11 coset deductions: transition group 11

Each block proves word eligibility and a transition between two literal bit states.
The individual computations remain separate so each kernel check covers at most
32 deductions. Their composition is proved in `M11CosetCertificate`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem eligible088 : deductions088.all eligible = true := by
  simp only [deductions088, List.all_cons, List.all_nil, eligible, r523_mem, r524_mem, r525_mem,
    r526_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_088 :
    deductions088.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits088 =
      bits089 := by
  decide +kernel

theorem eligible089 : deductions089.all eligible = true := by
  simp only [deductions089, List.all_cons, List.all_nil, eligible, r526_mem, r527_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_089 :
    deductions089.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits089 =
      bits090 := by
  decide +kernel

theorem eligible090 : deductions090.all eligible = true := by
  simp only [deductions090, List.all_cons, List.all_nil, eligible, r527_mem, r528_mem, r529_mem,
    r530_mem, r531_mem, r532_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_090 :
    deductions090.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits090 =
      bits091 := by
  decide +kernel

theorem eligible091 : deductions091.all eligible = true := by
  simp only [deductions091, List.all_cons, List.all_nil, eligible, r532_mem, r533_mem, r534_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_091 :
    deductions091.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits091 =
      bits092 := by
  decide +kernel

theorem eligible092 : deductions092.all eligible = true := by
  simp only [deductions092, List.all_cons, List.all_nil, eligible, r534_mem, r535_mem, r536_mem,
    r537_mem, r538_mem, r539_mem, r540_mem, r541_mem, r542_mem, decide_true, Bool.true_or,
    Bool.true_and]

theorem transition_092 :
    deductions092.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits092 =
      bits093 := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
