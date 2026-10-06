/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits3
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions3
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Eligibility
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership04
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership05
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership06

/-!
# M11 coset deductions: transition group 06

Each block proves word eligibility and a transition between two literal bit states.
The individual computations remain separate so each kernel check covers at most
32 deductions. Their composition is proved in `M11CosetCertificate`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem eligible048 : deductions048.all eligible = true := by
  simp only [deductions048, List.all_cons, List.all_nil, eligible, r269_mem, r270_mem, r271_mem,
    r272_mem, r273_mem, r274_mem, r275_mem, r276_mem, r277_mem, r278_mem, r279_mem, r280_mem,
    r281_mem, r282_mem, r283_mem, r284_mem, r285_mem, r286_mem, r287_mem, r288_mem, r289_mem,
    r290_mem, r291_mem, r292_mem, r293_mem, r294_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_048 :
    deductions048.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits048 =
      bits049 := by
  decide +kernel

theorem eligible049 : deductions049.all eligible = true := by
  simp only [deductions049, List.all_cons, List.all_nil, eligible, r295_mem, r296_mem, r297_mem,
    r298_mem, r299_mem, r300_mem, r301_mem, r302_mem, r303_mem, r304_mem, r305_mem, r306_mem,
    r307_mem, r308_mem, r309_mem, r310_mem, r311_mem, r312_mem, r313_mem, r314_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_049 :
    deductions049.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits049 =
      bits050 := by
  decide +kernel

theorem eligible050 : deductions050.all eligible = true := by
  simp only [deductions050, List.all_cons, List.all_nil, eligible, r314_mem, r315_mem, r316_mem,
    r317_mem, r318_mem, r319_mem, r320_mem, r321_mem, r322_mem, r323_mem, r324_mem, r325_mem,
    r326_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_050 :
    deductions050.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits050 =
      bits051 := by
  decide +kernel

theorem eligible051 : deductions051.all eligible = true := by
  simp only [deductions051, List.all_cons, List.all_nil, eligible, r326_mem, r327_mem, r328_mem,
    r329_mem, r330_mem, r331_mem, r332_mem, r333_mem, r334_mem, r335_mem, r336_mem, r337_mem,
    r338_mem, r339_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_051 :
    deductions051.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits051 =
      bits052 := by
  decide +kernel

theorem eligible052 : deductions052.all eligible = true := by
  simp only [deductions052, List.all_cons, List.all_nil, eligible, r340_mem, r341_mem, r342_mem,
    r343_mem, r344_mem, r345_mem, r346_mem, r347_mem, r348_mem, r349_mem, r350_mem, r351_mem,
    r352_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_052 :
    deductions052.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits052 =
      bits053 := by
  decide +kernel

theorem eligible053 : deductions053.all eligible = true := by
  simp only [deductions053, List.all_cons, List.all_nil, eligible, r352_mem, r353_mem, r354_mem,
    r355_mem, r356_mem, r357_mem, r358_mem, r359_mem, r360_mem, r361_mem, r362_mem, r363_mem,
    r364_mem, r365_mem, r366_mem, r367_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_053 :
    deductions053.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits053 =
      bits054 := by
  decide +kernel

theorem eligible054 : deductions054.all eligible = true := by
  simp only [deductions054, List.all_cons, List.all_nil, eligible, r367_mem, r368_mem, r369_mem,
    r370_mem, r371_mem, r372_mem, r373_mem, r374_mem, r375_mem, r376_mem, r377_mem, r378_mem,
    r379_mem, r380_mem, r381_mem, r382_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_054 :
    deductions054.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits054 =
      bits055 := by
  decide +kernel

theorem eligible055 : deductions055.all eligible = true := by
  simp only [deductions055, List.all_cons, List.all_nil, eligible, r382_mem, r383_mem, r384_mem,
    r385_mem, r386_mem, r387_mem, r388_mem, r389_mem, r390_mem, r391_mem, r392_mem, r393_mem,
    r394_mem, r395_mem, r396_mem, r397_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_055 :
    deductions055.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits055 =
      bits056 := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
