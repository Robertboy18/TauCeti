/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.DerivedRelations.Part05

/-! Certified consequences of the exact M11 presentation relations. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations

/-- Canonical signed word at certificate node 484. -/
abbrev word484 : Word := decode [0, 0, 0, 1, 2, 3, 3, 2, 3, 3, 2, 1, 1, 1, 0, 3, 0, 1]

/-- Node 484 holds in the exact M11 presentation group. -/
theorem word484_eq_one : eval word484 = 1 := by
  have hl : eval (decode [2, 3, 3, 2, 1, 1, 1, 0, 1, 1, 0, 0, 3, 2, 1, 2]) = 1 :=
    variant_eq_one word421_eq_one true
      15 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 1, 2, 2, 3, 3, 3, 0, 1, 0, 0, 0, 1, 2, 3, 3]) = 1 :=
    variant_eq_one word361_eq_one false
      7 (by decide +kernel)
  have hc : eval (decode [2, 3, 3, 2, 1, 1, 1, 0, 3, 0, 1, 0, 0, 0, 1, 2, 3, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 490. -/
abbrev word490 : Word := decode [0, 0, 3, 3, 0, 1, 1, 1, 2, 3, 3, 0, 3, 0, 3]

/-- Node 490 holds in the exact M11 presentation group. -/
theorem word490_eq_one : eval word490 = 1 := by
  have hl : eval (decode [1, 1, 2, 3, 3, 0, 3, 0, 3, 2, 1, 0, 0, 1, 2, 2, 1, 0]) = 1 :=
    variant_eq_one word422_eq_one false
      7 (by decide +kernel)
  have hr : eval (decode [2, 3, 0, 0, 3, 2, 2, 3, 0, 0, 0, 3, 3, 0, 1]) = 1 :=
    variant_eq_one word129_eq_one false
      7 (by decide +kernel)
  have hc : eval (decode [1, 1, 2, 3, 3, 0, 3, 0, 3, 0, 0, 3, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 500. -/
abbrev word500 : Word := decode [0, 0, 3, 3, 0, 1, 1, 1, 2, 1, 1, 2, 2, 3]

/-- Node 500 holds in the exact M11 presentation group. -/
theorem word500_eq_one : eval word500 = 1 := by
  have hl : eval (decode [3, 2, 1, 1, 2, 2, 2, 1, 0, 0, 1, 2, 2, 1, 0]) = 1 :=
    variant_eq_one word129_eq_one true
      8 (by decide +kernel)
  have hr : eval (decode [2, 3, 0, 0, 3, 2, 2, 3, 0, 1, 0, 0, 3, 3, 0, 3, 3]) = 1 :=
    variant_eq_one word426_eq_one true
      10 (by decide +kernel)
  have hc : eval (decode [3, 2, 1, 1, 2, 2, 1, 0, 0, 3, 3, 0, 3, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 512. -/
abbrev word512 : Word := decode [0, 0, 0, 3, 3, 2, 3, 0, 0, 1, 2, 1, 1, 0, 3, 3]

/-- Node 512 holds in the exact M11 presentation group. -/
theorem word512_eq_one : eval word512 = 1 := by
  have hl : eval (decode [0, 0, 0, 3, 3, 2, 3, 2, 3, 2, 1, 1, 1, 0, 1, 1]) = 1 :=
    variant_eq_one word432_eq_one false
      0 (by decide +kernel)
  have hr : eval (decode [3, 3, 2, 3, 3, 3, 0, 1, 0, 0, 0, 1, 2, 1, 1, 0, 3, 3]) = 1 :=
    variant_eq_one word359_eq_one false
      10 (by decide +kernel)
  have hc : eval (decode [0, 0, 0, 3, 3, 2, 3, 0, 0, 1, 2, 1, 1, 0, 3, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    0 (by decide +kernel)

/-- Canonical signed word at certificate node 523. -/
abbrev word523 : Word := decode [0, 0, 1, 2, 1, 0, 0, 3, 2, 2, 3, 0, 0, 3]

/-- Node 523 holds in the exact M11 presentation group. -/
theorem word523_eq_one : eval word523 = 1 := by
  have hl : eval (decode [3, 2, 2, 3, 0, 0, 3, 3, 0, 1, 1, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word435_eq_one false
      4 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 2, 3, 3, 2, 1, 0, 0, 1, 2, 1, 0, 0]) = 1 :=
    variant_eq_one word280_eq_one true
      11 (by decide +kernel)
  have hc : eval (decode [3, 2, 2, 3, 0, 0, 3, 0, 0, 1, 2, 1, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 525. -/
abbrev word525 : Word := decode [0, 0, 0, 0, 0, 3, 3, 3, 0, 0, 3, 2, 2, 3, 0, 0, 3]

/-- Node 525 holds in the exact M11 presentation group. -/
theorem word525_eq_one : eval word525 = 1 := by
  have hl : eval (decode [3, 2, 2, 3, 0, 0, 3, 3, 0, 1, 1, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word435_eq_one false
      4 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 3, 3, 3, 0, 0]) = 1 :=
    variant_eq_one word282_eq_one false
      10 (by decide +kernel)
  have hc : eval (decode [3, 2, 2, 3, 0, 0, 3, 0, 0, 0, 0, 0, 3, 3, 3, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 530. -/
abbrev word530 : Word := decode [0, 0, 1, 0, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 3, 0, 3]

/-- Node 530 holds in the exact M11 presentation group. -/
theorem word530_eq_one : eval word530 = 1 := by
  have hl : eval (decode [2, 1, 2, 3, 0, 0, 3, 0, 3, 2, 3, 0, 3, 3]) = 1 :=
    variant_eq_one word437_eq_one false
      10 (by decide +kernel)
  have hr : eval (decode [1, 1, 2, 2, 2, 1, 2, 1, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      4 (by decide +kernel)
  have hc : eval (decode [2, 1, 2, 3, 0, 0, 3, 0, 3, 2, 3, 2, 2, 1, 2, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    4 (by decide +kernel)

/-- Canonical signed word at certificate node 538. -/
abbrev word538 : Word := decode [0, 0, 1, 1, 2, 2, 1, 0, 3, 2, 2, 1, 2, 1, 0, 1]

/-- Node 538 holds in the exact M11 presentation group. -/
theorem word538_eq_one : eval word538 = 1 := by
  have hl : eval (decode [2, 1, 2, 3, 0, 0, 3, 0, 3, 2, 3, 0, 3, 3]) = 1 :=
    variant_eq_one word437_eq_one false
      10 (by decide +kernel)
  have hr : eval (decode [1, 1, 2, 1, 0, 1, 2, 3, 2, 2, 3, 2, 3, 0, 3, 0, 0, 0]) = 1 :=
    variant_eq_one word126_eq_one false
      3 (by decide +kernel)
  have hc : eval (decode [1, 2, 3, 0, 0, 3, 3, 2, 2, 3, 2, 3, 0, 3, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [2])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 555. -/
abbrev word555 : Word := decode [0, 0, 0, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 1, 0, 3, 0, 1]

/-- Node 555 holds in the exact M11 presentation group. -/
theorem word555_eq_one : eval word555 = 1 := by
  have hl : eval (decode [3, 2, 1, 2, 3, 0, 0, 3, 0, 3, 2, 3, 0, 3]) = 1 :=
    variant_eq_one word437_eq_one false
      9 (by decide +kernel)
  have hr : eval (decode [1, 2, 1, 0, 3, 0, 0, 0, 3, 2, 2, 2]) = 1 :=
    variant_eq_one word4_eq_one true
      0 (by decide +kernel)
  have hc : eval (decode [3, 2, 1, 2, 3, 0, 0, 3, 0, 3, 3, 0, 0, 0, 3, 2, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    0 (by decide +kernel)

/-- Canonical signed word at certificate node 598. -/
abbrev word598 : Word := decode [0, 0, 1, 2, 1, 0, 0, 3, 3, 0, 1, 0, 3, 3, 2, 3, 0, 3]

/-- Node 598 holds in the exact M11 presentation group. -/
theorem word598_eq_one : eval word598 = 1 := by
  have hl : eval (decode [1, 2, 1, 0, 1, 1, 2, 3, 2, 3, 0, 3, 3, 3, 2, 1]) = 1 :=
    variant_eq_one word438_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [3, 0, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 0, 3, 2, 2]) = 1 :=
    variant_eq_one word281_eq_one true
      0 (by decide +kernel)
  have hc : eval (decode [1, 2, 1, 0, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 0, 3, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    0 (by decide +kernel)

/-- Canonical signed word at certificate node 611. -/
abbrev word611 : Word := decode [0, 0, 3, 3, 2, 1, 1, 1, 1, 0, 3, 3, 3, 2, 1, 0, 1]

/-- Node 611 holds in the exact M11 presentation group. -/
theorem word611_eq_one : eval word611 = 1 := by
  have hl : eval (decode [2, 1, 1, 1, 1, 0, 3, 3, 3, 3, 3, 2, 1, 2, 3, 0, 1, 1]) = 1 :=
    variant_eq_one word104_eq_one true
      6 (by decide +kernel)
  have hr : eval (decode [3, 3, 2, 1, 0, 3, 0, 1, 1, 2, 1, 0, 1, 0, 0, 3, 3]) = 1 :=
    variant_eq_one word439_eq_one false
      4 (by decide +kernel)
  have hc : eval (decode [2, 1, 1, 1, 1, 0, 3, 3, 3, 2, 1, 0, 1, 0, 0, 3, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    13 (by decide +kernel)

/-- Canonical signed word at certificate node 613. -/
abbrev word613 : Word := decode [0, 0, 0, 0, 0, 0, 1, 1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 3]

/-- Node 613 holds in the exact M11 presentation group. -/
theorem word613_eq_one : eval word613 = 1 := by
  have hl : eval (decode [1, 0, 3, 3, 2, 2, 2, 2, 2, 1, 1, 2, 1, 0, 1, 0, 0]) = 1 :=
    variant_eq_one word346_eq_one true
      8 (by decide +kernel)
  have hr : eval (decode [2, 2, 3, 2, 3, 0, 3, 3, 2, 1, 2, 3, 0, 1, 1, 1, 1]) = 1 :=
    variant_eq_one word439_eq_one true
      15 (by decide +kernel)
  have hc : eval (decode [1, 0, 3, 3, 2, 2, 2, 2, 2, 2, 1, 2, 3, 0, 1, 1, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 615. -/
abbrev word615 : Word := decode [0, 0, 0, 1, 2, 2, 3, 2, 3, 0, 3, 3, 0, 0, 3, 2, 2, 3]

/-- Node 615 holds in the exact M11 presentation group. -/
theorem word615_eq_one : eval word615 = 1 := by
  have hl : eval (decode [1, 2, 2, 3, 2, 3, 0, 3, 3, 2, 1, 2, 3, 0, 1, 1, 1]) = 1 :=
    variant_eq_one word439_eq_one true
      14 (by decide +kernel)
  have hr : eval (decode [3, 3, 3, 2, 1, 0, 3, 0, 0, 0, 3, 2, 2, 3, 0, 0, 0]) = 1 :=
    variant_eq_one word62_eq_one false
      10 (by decide +kernel)
  have hc : eval (decode [1, 2, 2, 3, 2, 3, 0, 3, 3, 0, 0, 3, 2, 2, 3, 0, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 617. -/
abbrev word617 : Word := decode [0, 1, 0, 3, 0, 1, 2, 3, 3, 0, 3, 3, 3, 3, 3, 3]

/-- Node 617 holds in the exact M11 presentation group. -/
theorem word617_eq_one : eval word617 = 1 := by
  have hl : eval (decode [0, 1, 1, 0, 3, 2, 1, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3]) = 1 :=
    variant_eq_one word440_eq_one false
      6 (by decide +kernel)
  have hr : eval (decode [1, 0, 3, 2, 3, 2, 1, 1, 1, 1, 1, 2, 2]) = 1 :=
    variant_eq_one word26_eq_one true
      0 (by decide +kernel)
  have hc : eval (decode [1, 1, 0, 3, 2, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 619. -/
abbrev word619 : Word := decode [0, 0, 0, 1, 1, 2, 1, 1, 0, 3, 2, 1, 2, 3, 3]

/-- Node 619 holds in the exact M11 presentation group. -/
theorem word619_eq_one : eval word619 = 1 := by
  have hl : eval (decode [0, 1, 1, 0, 3, 2, 1, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3]) = 1 :=
    variant_eq_one word440_eq_one false
      6 (by decide +kernel)
  have hr : eval (decode [1, 0, 3, 2, 3, 2, 3, 0, 3, 0, 0, 0, 1, 1, 2, 2]) = 1 :=
    variant_eq_one word91_eq_one false
      7 (by decide +kernel)
  have hc : eval (decode [1, 1, 0, 3, 2, 1, 2, 3, 3, 0, 0, 0, 1, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 642. -/
abbrev word642 : Word := decode [0, 0, 0, 1, 1, 0, 3, 3, 2, 2, 2, 3, 2, 2, 3]

/-- Node 642 holds in the exact M11 presentation group. -/
theorem word642_eq_one : eval word642 = 1 := by
  have hl : eval (decode [3, 0, 0, 1, 1, 0, 3, 3, 2, 1, 0, 3, 2, 1, 0, 3, 2, 2]) = 1 :=
    variant_eq_one word334_eq_one false
      17 (by decide +kernel)
  have hr : eval (decode [0, 0, 1, 2, 3, 0, 1, 2, 3, 2, 2, 3, 2, 2, 3, 0, 1]) = 1 :=
    variant_eq_one word445_eq_one true
      3 (by decide +kernel)
  have hc : eval (decode [0, 0, 1, 1, 0, 3, 3, 2, 2, 2, 3, 2, 2, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [3])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 646. -/
abbrev word646 : Word := decode [0, 0, 3, 3, 0, 1, 2, 3, 3, 0, 3, 0, 3, 3, 3, 3]

/-- Node 646 holds in the exact M11 presentation group. -/
theorem word646_eq_one : eval word646 = 1 := by
  have hl : eval (decode [1, 0, 3, 3, 0, 1, 2, 3, 3, 2, 1, 0, 3, 2, 3, 3, 0]) = 1 :=
    variant_eq_one word446_eq_one false
      1 (by decide +kernel)
  have hr : eval (decode [2, 1, 1, 0, 1, 2, 3, 0, 0, 3, 0, 3, 3, 3, 3, 0, 3]) = 1 :=
    variant_eq_one word130_eq_one false
      10 (by decide +kernel)
  have hc : eval (decode [0, 3, 3, 0, 1, 2, 3, 3, 0, 3, 0, 3, 3, 3, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [1])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 687. -/
abbrev word687 : Word := decode [0, 0, 3, 3, 0, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1]

/-- Node 687 holds in the exact M11 presentation group. -/
theorem word687_eq_one : eval word687 = 1 := by
  have hl : eval (decode [2, 2, 1, 1, 1, 0, 0, 3, 3, 2, 2, 1, 0, 1, 0, 1, 2, 2]) = 1 :=
    variant_eq_one word408_eq_one true
      16 (by decide +kernel)
  have hr : eval (decode [0, 0, 3, 2, 3, 2, 3, 0, 0, 0, 1, 1, 2, 1, 1]) = 1 :=
    variant_eq_one word451_eq_one false
      8 (by decide +kernel)
  have hc : eval (decode [2, 2, 1, 1, 1, 0, 0, 3, 3, 0, 1, 1, 2, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 691. -/
abbrev word691 : Word := decode [0, 1, 0, 3, 2, 3, 0, 1, 2, 1, 1, 0, 3, 2, 1]

/-- Node 691 holds in the exact M11 presentation group. -/
theorem word691_eq_one : eval word691 = 1 := by
  have hl : eval (decode [0, 1, 1, 0, 3, 2, 1, 0, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3]) = 1 :=
    variant_eq_one word434_eq_one true
      4 (by decide +kernel)
  have hr : eval (decode [1, 0, 3, 3, 0, 0, 1, 1, 0, 0, 3, 2, 3, 0, 1, 2, 2]) = 1 :=
    variant_eq_one word452_eq_one false
      13 (by decide +kernel)
  have hc : eval (decode [1, 1, 0, 3, 2, 1, 0, 1, 0, 3, 2, 3, 0, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 736. -/
abbrev word736 : Word := decode [0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 3, 3, 2, 2, 2, 1]

/-- Node 736 holds in the exact M11 presentation group. -/
theorem word736_eq_one : eval word736 = 1 := by
  have hl : eval (decode [3, 0, 3, 2, 2, 2, 2, 2, 1, 1, 0, 1, 0, 1, 2, 2]) = 1 :=
    variant_eq_one word461_eq_one true
      8 (by decide +kernel)
  have hr : eval (decode [0, 0, 3, 2, 3, 2, 3, 3, 2, 2, 3, 0, 0, 0, 1, 1, 1, 1]) = 1 :=
    variant_eq_one word373_eq_one false
      7 (by decide +kernel)
  have hc : eval (decode [0, 3, 2, 2, 2, 2, 2, 2, 2, 3, 0, 0, 0, 1, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [3])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 845. -/
abbrev word845 : Word := decode [0, 1, 1, 1, 2, 3, 0, 1, 2, 1, 2, 1, 1, 2, 1, 1]

/-- Node 845 holds in the exact M11 presentation group. -/
theorem word845_eq_one : eval word845 = 1 := by
  have hl : eval (decode [3, 0, 1, 2, 1, 2, 1, 0, 1, 0, 0, 3, 3]) = 1 :=
    variant_eq_one word465_eq_one false
      4 (by decide +kernel)
  have hr : eval (decode [1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 0, 1, 1, 1, 2]) = 1 :=
    variant_eq_one word476_eq_one true
      11 (by decide +kernel)
  have hc : eval (decode [3, 0, 1, 2, 1, 2, 1, 1, 2, 1, 1, 0, 1, 1, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 856. -/
abbrev word856 : Word := decode [0, 0, 3, 3, 2, 1, 1, 0, 1, 1, 1, 2, 3, 0, 1]

/-- Node 856 holds in the exact M11 presentation group. -/
theorem word856_eq_one : eval word856 = 1 := by
  have hl : eval (decode [1, 2, 1, 1, 0, 1, 1, 1, 2, 3, 3, 0, 3, 0, 3, 2]) = 1 :=
    variant_eq_one word478_eq_one false
      12 (by decide +kernel)
  have hr : eval (decode [0, 1, 2, 1, 2, 1, 0, 1, 0, 0, 3, 3, 3]) = 1 :=
    variant_eq_one word465_eq_one false
      5 (by decide +kernel)
  have hc : eval (decode [2, 1, 1, 0, 1, 1, 1, 2, 3, 0, 1, 0, 0, 3, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [1])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 884. -/
abbrev word884 : Word := decode [0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3]

/-- Node 884 holds in the exact M11 presentation group. -/
theorem word884_eq_one : eval word884 = 1 := by
  have hl : eval (decode [0, 0, 3, 0, 3, 0, 3, 0, 3, 2, 1, 0, 0, 1, 2, 2, 2, 1]) = 1 :=
    variant_eq_one word482_eq_one true
      1 (by decide +kernel)
  have hr : eval (decode [3, 0, 0, 0, 3, 2, 2, 3, 0, 0, 3, 0, 3, 0, 3, 0, 3, 2]) = 1 :=
    variant_eq_one word321_eq_one false
      17 (by decide +kernel)
  have hc : eval (decode [0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    0 (by decide +kernel)

/-- Canonical signed word at certificate node 1014. -/
abbrev word1014 : Word := decode [0, 0, 1, 2, 2, 1, 0, 1, 0, 1, 0, 3, 0, 3, 3]

/-- Node 1014 holds in the exact M11 presentation group. -/
theorem word1014_eq_one : eval word1014 = 1 := by
  have hl : eval (decode [1, 0, 1, 2, 2, 1, 0, 1, 0, 0, 0, 3, 0, 3, 2, 3, 2, 2]) = 1 :=
    variant_eq_one word396_eq_one false
      10 (by decide +kernel)
  have hr : eval (decode [0, 0, 1, 0, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 3, 0, 3]) = 1 :=
    variant_eq_one word530_eq_one false
      0 (by decide +kernel)
  have hc : eval (decode [0, 1, 2, 2, 1, 0, 1, 0, 1, 0, 3, 0, 3, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [1])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 1015. -/
abbrev word1015 : Word := decode [0, 1, 0, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1]

/-- Node 1015 holds in the exact M11 presentation group. -/
theorem word1015_eq_one : eval word1015 = 1 := by
  have hl : eval (decode [1, 2, 2, 1, 1, 0, 1, 1, 0, 0, 0, 3, 0, 3, 2, 3, 2, 2]) = 1 :=
    variant_eq_one word417_eq_one false
      10 (by decide +kernel)
  have hr : eval (decode [0, 0, 1, 0, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 3, 0, 3]) = 1 :=
    variant_eq_one word530_eq_one false
      0 (by decide +kernel)
  have hc : eval (decode [2, 1, 1, 0, 1, 1, 0, 1, 0, 3, 0, 3, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [1, 2])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 1085. -/
abbrev word1085 : Word := decode [0, 0, 3, 0, 3, 3, 0, 0, 3, 3, 2, 3, 3, 2, 1, 1]

/-- Node 1085 holds in the exact M11 presentation group. -/
theorem word1085_eq_one : eval word1085 = 1 := by
  have hl : eval (decode [2, 3, 3, 2, 3, 3, 2, 1, 1, 1, 0, 3, 0, 1, 0, 0, 0, 1]) = 1 :=
    variant_eq_one word484_eq_one false
      4 (by decide +kernel)
  have hr : eval (decode [3, 2, 2, 2, 3, 2, 1, 2, 3, 0, 0, 3, 0, 3, 3, 0, 0, 0]) = 1 :=
    variant_eq_one word555_eq_one true
      14 (by decide +kernel)
  have hc : eval (decode [3, 3, 2, 3, 3, 2, 1, 1, 0, 0, 3, 0, 3, 3, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [2])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 1145. -/
abbrev word1145 : Word := decode [0, 0, 1, 1, 2, 2, 1, 1, 0, 0, 3, 3, 0, 1, 0, 3]

/-- Node 1145 holds in the exact M11 presentation group. -/
theorem word1145_eq_one : eval word1145 = 1 := by
  have hl : eval (decode [1, 0, 0, 3, 3, 0, 1, 0, 3, 3, 2, 3, 0, 3, 0, 0, 1, 2]) = 1 :=
    variant_eq_one word598_eq_one false
      4 (by decide +kernel)
  have hr : eval (decode [0, 3, 2, 2, 1, 2, 1, 0, 1, 0, 0, 1, 1, 2, 2, 1]) = 1 :=
    variant_eq_one word538_eq_one false
      7 (by decide +kernel)
  have hc : eval (decode [1, 0, 0, 3, 3, 0, 1, 0, 3, 0, 0, 1, 1, 2, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 1163. -/
abbrev word1163 : Word := decode [0, 0, 3, 0, 1, 0, 0, 3, 3, 2, 1, 1, 0, 3, 0, 3]

/-- Node 1163 holds in the exact M11 presentation group. -/
theorem word1163_eq_one : eval word1163 = 1 := by
  have hl : eval (decode [0, 1, 0, 0, 3, 3, 2, 1, 1, 1, 1, 0, 3, 3, 3, 2, 1]) = 1 :=
    variant_eq_one word611_eq_one false
      15 (by decide +kernel)
  have hr : eval (decode [3, 0, 1, 1, 1, 2, 3, 3, 0, 3, 0, 3, 0, 0, 3]) = 1 :=
    variant_eq_one word490_eq_one false
      3 (by decide +kernel)
  have hc : eval (decode [0, 1, 0, 0, 3, 3, 2, 1, 1, 0, 3, 0, 3, 0, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    13 (by decide +kernel)

/-- Canonical signed word at certificate node 1165. -/
abbrev word1165 : Word := decode [0, 0, 0, 1, 0, 0, 0, 1, 1, 2, 3, 3, 3, 3, 3, 3]

/-- Node 1165 holds in the exact M11 presentation group. -/
theorem word1165_eq_one : eval word1165 = 1 := by
  have hl : eval (decode [0, 1, 1, 1, 1, 1, 0, 3, 3, 2, 2, 2, 2, 2, 2, 1, 2, 3]) = 1 :=
    variant_eq_one word613_eq_one true
      3 (by decide +kernel)
  have hr : eval (decode [1, 0, 3, 0, 0, 0, 3, 2, 2, 2, 1, 2]) = 1 :=
    variant_eq_one word4_eq_one true
      2 (by decide +kernel)
  have hc : eval (decode [1, 1, 1, 1, 1, 0, 3, 3, 2, 2, 2, 3, 2, 2, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 1167. -/
abbrev word1167 : Word := decode [0, 0, 0, 0, 0, 3, 2, 1, 0, 1, 0, 0, 3, 2, 3]

/-- Node 1167 holds in the exact M11 presentation group. -/
theorem word1167_eq_one : eval word1167 = 1 := by
  have hl : eval (decode [0, 0, 1, 2, 2, 3, 2, 3, 0, 3, 3, 0, 0, 3, 2, 2, 3, 0]) = 1 :=
    variant_eq_one word615_eq_one false
      1 (by decide +kernel)
  have hr : eval (decode [2, 1, 0, 0, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2]) = 1 :=
    variant_eq_one word525_eq_one true
      2 (by decide +kernel)
  have hc : eval (decode [0, 1, 2, 2, 3, 2, 3, 0, 1, 2, 2, 2, 2, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    1 (by decide +kernel)

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations
