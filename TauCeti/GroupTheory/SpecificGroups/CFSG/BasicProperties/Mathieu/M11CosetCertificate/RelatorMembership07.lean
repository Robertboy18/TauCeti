/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Data

/-!
# Membership of M11 scan words: group 07

These are membership proofs in the literal scan-word list.
They assert no group relation; interpretation of the words is a separate obligation.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem r448_mem : r448 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 0 < 64 by decide))

theorem r449_mem : r449 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 1 < 64 by decide))

theorem r450_mem : r450 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 2 < 64 by decide))

theorem r451_mem : r451 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 3 < 64 by decide))

theorem r452_mem : r452 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 4 < 64 by decide))

theorem r453_mem : r453 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 5 < 64 by decide))

theorem r454_mem : r454 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 6 < 64 by decide))

theorem r455_mem : r455 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 7 < 64 by decide))

theorem r456_mem : r456 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 8 < 64 by decide))

theorem r457_mem : r457 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 9 < 64 by decide))

theorem r458_mem : r458 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 10 < 64 by decide))

theorem r459_mem : r459 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 11 < 64 by decide))

theorem r460_mem : r460 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 12 < 64 by decide))

theorem r461_mem : r461 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 13 < 64 by decide))

theorem r462_mem : r462 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 14 < 64 by decide))

theorem r463_mem : r463 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 15 < 64 by decide))

theorem r464_mem : r464 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 16 < 64 by decide))

theorem r465_mem : r465 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 17 < 64 by decide))

theorem r466_mem : r466 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 18 < 64 by decide))

theorem r467_mem : r467 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 19 < 64 by decide))

theorem r468_mem : r468 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 20 < 64 by decide))

theorem r469_mem : r469 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 21 < 64 by decide))

theorem r470_mem : r470 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 22 < 64 by decide))

theorem r471_mem : r471 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 23 < 64 by decide))

theorem r472_mem : r472 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 24 < 64 by decide))

theorem r473_mem : r473 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 25 < 64 by decide))

theorem r474_mem : r474 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 26 < 64 by decide))

theorem r475_mem : r475 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 27 < 64 by decide))

theorem r476_mem : r476 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 28 < 64 by decide))

theorem r477_mem : r477 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 29 < 64 by decide))

theorem r478_mem : r478 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 30 < 64 by decide))

theorem r479_mem : r479 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 31 < 64 by decide))

theorem r480_mem : r480 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 32 < 64 by decide))

theorem r481_mem : r481 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 33 < 64 by decide))

theorem r482_mem : r482 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 34 < 64 by decide))

theorem r483_mem : r483 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 35 < 64 by decide))

theorem r484_mem : r484 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 36 < 64 by decide))

theorem r485_mem : r485 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 37 < 64 by decide))

theorem r486_mem : r486 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 38 < 64 by decide))

theorem r487_mem : r487 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 39 < 64 by decide))

theorem r488_mem : r488 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 40 < 64 by decide))

theorem r489_mem : r489 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 41 < 64 by decide))

theorem r490_mem : r490 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 42 < 64 by decide))

theorem r491_mem : r491 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 43 < 64 by decide))

theorem r492_mem : r492 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 44 < 64 by decide))

theorem r493_mem : r493 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 45 < 64 by decide))

theorem r494_mem : r494 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 46 < 64 by decide))

theorem r495_mem : r495 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 47 < 64 by decide))

theorem r496_mem : r496 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 48 < 64 by decide))

theorem r497_mem : r497 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 49 < 64 by decide))

theorem r498_mem : r498 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 50 < 64 by decide))

theorem r499_mem : r499 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 51 < 64 by decide))

theorem r500_mem : r500 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 52 < 64 by decide))

theorem r501_mem : r501 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 53 < 64 by decide))

theorem r502_mem : r502 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 54 < 64 by decide))

theorem r503_mem : r503 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 55 < 64 by decide))

theorem r504_mem : r504 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 56 < 64 by decide))

theorem r505_mem : r505 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 57 < 64 by decide))

theorem r506_mem : r506 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 58 < 64 by decide))

theorem r507_mem : r507 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 59 < 64 by decide))

theorem r508_mem : r508 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 60 < 64 by decide))

theorem r509_mem : r509 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 61 < 64 by decide))

theorem r510_mem : r510 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 62 < 64 by decide))

theorem r511_mem : r511 ∈ relators := by
  unfold relators
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_left
  exact Vector.mem_toList_iff.mpr
    (Vector.getElem_mem (xs := relatorChunk07) (show 63 < 64 by decide))

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
