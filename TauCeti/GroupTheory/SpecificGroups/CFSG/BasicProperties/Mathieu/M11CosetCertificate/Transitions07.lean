/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits3
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits4
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions3
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Eligibility
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership06
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership07

/-!
# M11 coset deductions: transition group 07

Each block proves word eligibility and a transition between two literal bit states.
The individual computations remain separate so each kernel check covers at most
32 deductions. Their composition is proved in `M11CosetCertificate`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem eligible056 : deductions056.all eligible = true := by
  simp only [deductions056, List.all_cons, List.all_nil, eligible, r398_mem, r399_mem, r400_mem,
    r401_mem, r402_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_056 :
    deductions056.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits056 =
      bits057 := by
  decide +kernel

theorem eligible057 : deductions057.all eligible = true := by
  simp only [deductions057, List.all_cons, List.all_nil, eligible, r402_mem, r403_mem, r404_mem,
    r405_mem, r406_mem, r407_mem, r408_mem, r409_mem, r410_mem, r411_mem, r412_mem, r413_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_057 :
    deductions057.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits057 =
      bits058 := by
  decide +kernel

theorem eligible058 : deductions058.all eligible = true := by
  simp only [deductions058, List.all_cons, List.all_nil, eligible, r413_mem, r414_mem, r415_mem,
    r416_mem, r417_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_058 :
    deductions058.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits058 =
      bits059 := by
  decide +kernel

theorem eligible059 : deductions059.all eligible = true := by
  simp only [deductions059, List.all_cons, List.all_nil, eligible, r418_mem, r419_mem, r420_mem,
    r421_mem, r422_mem, r423_mem, r424_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_059 :
    deductions059.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits059 =
      bits060 := by
  decide +kernel

theorem eligible060 : deductions060.all eligible = true := by
  simp only [deductions060, List.all_cons, List.all_nil, eligible, r424_mem, r425_mem, r426_mem,
    r427_mem, r428_mem, r429_mem, r430_mem, r431_mem, r432_mem, r433_mem, r434_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_060 :
    deductions060.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits060 =
      bits061 := by
  decide +kernel

theorem eligible061 : deductions061.all eligible = true := by
  simp only [deductions061, List.all_cons, List.all_nil, eligible, r434_mem, r435_mem, r436_mem,
    r437_mem, r438_mem, r439_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_061 :
    deductions061.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits061 =
      bits062 := by
  decide +kernel

theorem eligible062 : deductions062.all eligible = true := by
  simp only [deductions062, List.all_cons, List.all_nil, eligible, r439_mem, r440_mem, r441_mem,
    r442_mem, r443_mem, r444_mem, r445_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_062 :
    deductions062.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits062 =
      bits063 := by
  decide +kernel

theorem eligible063 : deductions063.all eligible = true := by
  simp only [deductions063, List.all_cons, List.all_nil, eligible, r446_mem, r447_mem, r448_mem,
    r449_mem, r450_mem, r451_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_063 :
    deductions063.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits063 =
      bits064 := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
