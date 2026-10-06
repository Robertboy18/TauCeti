/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Data

/-!
# Membership of M11 scan words: group 05

These are membership proofs in the literal scan-word list.
They assert no group relation; interpretation of the words is a separate obligation.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem r320_mem : r320 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 0 < 64 by decide))

theorem r321_mem : r321 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 1 < 64 by decide))

theorem r322_mem : r322 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 2 < 64 by decide))

theorem r323_mem : r323 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 3 < 64 by decide))

theorem r324_mem : r324 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 4 < 64 by decide))

theorem r325_mem : r325 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 5 < 64 by decide))

theorem r326_mem : r326 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 6 < 64 by decide))

theorem r327_mem : r327 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 7 < 64 by decide))

theorem r328_mem : r328 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 8 < 64 by decide))

theorem r329_mem : r329 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 9 < 64 by decide))

theorem r330_mem : r330 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 10 < 64 by decide))

theorem r331_mem : r331 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 11 < 64 by decide))

theorem r332_mem : r332 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 12 < 64 by decide))

theorem r333_mem : r333 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 13 < 64 by decide))

theorem r334_mem : r334 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 14 < 64 by decide))

theorem r335_mem : r335 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 15 < 64 by decide))

theorem r336_mem : r336 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 16 < 64 by decide))

theorem r337_mem : r337 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 17 < 64 by decide))

theorem r338_mem : r338 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 18 < 64 by decide))

theorem r339_mem : r339 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 19 < 64 by decide))

theorem r340_mem : r340 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 20 < 64 by decide))

theorem r341_mem : r341 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 21 < 64 by decide))

theorem r342_mem : r342 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 22 < 64 by decide))

theorem r343_mem : r343 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 23 < 64 by decide))

theorem r344_mem : r344 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 24 < 64 by decide))

theorem r345_mem : r345 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 25 < 64 by decide))

theorem r346_mem : r346 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 26 < 64 by decide))

theorem r347_mem : r347 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 27 < 64 by decide))

theorem r348_mem : r348 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 28 < 64 by decide))

theorem r349_mem : r349 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 29 < 64 by decide))

theorem r350_mem : r350 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 30 < 64 by decide))

theorem r351_mem : r351 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 31 < 64 by decide))

theorem r352_mem : r352 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 32 < 64 by decide))

theorem r353_mem : r353 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 33 < 64 by decide))

theorem r354_mem : r354 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 34 < 64 by decide))

theorem r355_mem : r355 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 35 < 64 by decide))

theorem r356_mem : r356 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 36 < 64 by decide))

theorem r357_mem : r357 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 37 < 64 by decide))

theorem r358_mem : r358 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 38 < 64 by decide))

theorem r359_mem : r359 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 39 < 64 by decide))

theorem r360_mem : r360 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 40 < 64 by decide))

theorem r361_mem : r361 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 41 < 64 by decide))

theorem r362_mem : r362 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 42 < 64 by decide))

theorem r363_mem : r363 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 43 < 64 by decide))

theorem r364_mem : r364 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 44 < 64 by decide))

theorem r365_mem : r365 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 45 < 64 by decide))

theorem r366_mem : r366 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 46 < 64 by decide))

theorem r367_mem : r367 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 47 < 64 by decide))

theorem r368_mem : r368 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 48 < 64 by decide))

theorem r369_mem : r369 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 49 < 64 by decide))

theorem r370_mem : r370 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 50 < 64 by decide))

theorem r371_mem : r371 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 51 < 64 by decide))

theorem r372_mem : r372 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 52 < 64 by decide))

theorem r373_mem : r373 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 53 < 64 by decide))

theorem r374_mem : r374 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 54 < 64 by decide))

theorem r375_mem : r375 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 55 < 64 by decide))

theorem r376_mem : r376 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 56 < 64 by decide))

theorem r377_mem : r377 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 57 < 64 by decide))

theorem r378_mem : r378 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 58 < 64 by decide))

theorem r379_mem : r379 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 59 < 64 by decide))

theorem r380_mem : r380 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 60 < 64 by decide))

theorem r381_mem : r381 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 61 < 64 by decide))

theorem r382_mem : r382 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 62 < 64 by decide))

theorem r383_mem : r383 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk05) (show 63 < 64 by decide))

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
