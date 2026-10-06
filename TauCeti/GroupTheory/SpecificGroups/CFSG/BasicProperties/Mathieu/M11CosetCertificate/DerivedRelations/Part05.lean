/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.DerivedRelations.Part04

/-! Certified consequences of the exact M11 presentation relations. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations

/-- Canonical signed word at certificate node 411. -/
abbrev word411 : Word := decode [0, 0, 3, 2, 1, 2, 3, 2, 3, 0, 3, 3, 2, 1, 1, 1, 2, 1]

/-- Node 411 holds in the exact M11 presentation group. -/
theorem word411_eq_one : eval word411 = 1 := by
  have hl : eval (decode [3, 0, 3, 3, 3, 0, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 0]) = 1 :=
    variant_eq_one word395_eq_one true
      3 (by decide +kernel)
  have hr : eval (decode [2, 3, 3, 0, 0, 3, 3, 0, 0, 1, 0, 3, 0, 1, 2, 2]) = 1 :=
    variant_eq_one word259_eq_one true
      15 (by decide +kernel)
  have hc : eval (decode [3, 0, 3, 3, 3, 0, 1, 1, 2, 1, 0, 1, 0, 3, 0, 1, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    0 (by decide +kernel)

/-- Canonical signed word at certificate node 412. -/
abbrev word412 : Word := decode [0, 0, 0, 3, 3, 2, 1, 2, 3, 2, 1, 0, 1, 2, 2, 1, 0, 1]

/-- Node 412 holds in the exact M11 presentation group. -/
theorem word412_eq_one : eval word412 = 1 := by
  have hl : eval (decode [3, 2, 1, 2, 3, 0, 1, 0, 1, 2]) = 1 :=
    variant_eq_one word1_eq_one false
      5 (by decide +kernel)
  have hr : eval (decode [0, 3, 2, 3, 2, 2, 1, 0, 1, 2, 2, 1, 0, 1, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word396_eq_one false
      4 (by decide +kernel)
  have hc : eval (decode [3, 2, 1, 2, 3, 2, 1, 0, 1, 2, 2, 1, 0, 1, 0, 0, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 413. -/
abbrev word413 : Word := decode [0, 0, 0, 3, 3, 2, 2, 3, 2, 1, 0, 0, 1, 2, 2, 1, 0, 1]

/-- Node 413 holds in the exact M11 presentation group. -/
theorem word413_eq_one : eval word413 = 1 := by
  have hl : eval (decode [3, 2, 2, 3, 2, 1, 0, 3, 0, 0, 1, 0, 1, 2]) = 1 :=
    variant_eq_one word48_eq_one false
      6 (by decide +kernel)
  have hr : eval (decode [0, 3, 2, 3, 2, 2, 1, 0, 1, 2, 2, 1, 0, 1, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word396_eq_one false
      4 (by decide +kernel)
  have hc : eval (decode [3, 2, 2, 3, 2, 1, 0, 0, 1, 2, 2, 1, 0, 1, 0, 0, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 414. -/
abbrev word414 : Word := decode [0, 0, 0, 3, 3, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 0, 1]

/-- Node 414 holds in the exact M11 presentation group. -/
theorem word414_eq_one : eval word414 = 1 := by
  have hl : eval (decode [3, 2, 1, 1, 2, 3, 2, 1, 2, 3, 0, 0, 1, 0, 1, 2]) = 1 :=
    variant_eq_one word38_eq_one false
      6 (by decide +kernel)
  have hr : eval (decode [0, 3, 2, 3, 2, 2, 1, 0, 1, 2, 2, 1, 0, 1, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word396_eq_one false
      4 (by decide +kernel)
  have hc : eval (decode [3, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 0, 1, 0, 0, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 415. -/
abbrev word415 : Word := decode [0, 0, 1, 0, 1, 2, 2, 3, 3, 2, 1, 0, 3, 2, 3, 2, 3]

/-- Node 415 holds in the exact M11 presentation group. -/
theorem word415_eq_one : eval word415 = 1 := by
  have hl : eval (decode [0, 3, 2, 3, 2, 2, 1, 0, 1, 2, 2, 1, 0, 1, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word396_eq_one false
      4 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 2, 3, 2, 3, 0, 0, 0, 1, 2, 3, 0, 1, 1, 0]) = 1 :=
    variant_eq_one word284_eq_one false
      10 (by decide +kernel)
  have hc : eval (decode [0, 3, 2, 3, 2, 2, 1, 0, 1, 0, 1, 2, 3, 0, 1, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 416. -/
abbrev word416 : Word := decode [0, 0, 1, 0, 1, 2, 2, 3, 0, 1, 2, 3, 2, 2, 3, 2, 3]

/-- Node 416 holds in the exact M11 presentation group. -/
theorem word416_eq_one : eval word416 = 1 := by
  have hl : eval (decode [0, 3, 2, 3, 2, 2, 1, 0, 1, 2, 2, 1, 0, 1, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word396_eq_one false
      4 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 2, 3, 2, 3, 0, 0, 0, 0, 1, 0, 3, 2, 1, 0]) = 1 :=
    variant_eq_one word285_eq_one false
      10 (by decide +kernel)
  have hc : eval (decode [0, 3, 2, 3, 2, 2, 1, 0, 1, 0, 0, 1, 0, 3, 2, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 417. -/
abbrev word417 : Word := decode [0, 0, 0, 3, 0, 3, 2, 3, 2, 2, 1, 2, 2, 1, 1, 0, 1, 1]

/-- Node 417 holds in the exact M11 presentation group. -/
theorem word417_eq_one : eval word417 = 1 := by
  have hl : eval (decode [2, 2, 1, 1, 0, 1, 2, 3, 0, 0, 3, 2]) = 1 :=
    variant_eq_one word76_eq_one true
      10 (by decide +kernel)
  have hr : eval (decode [0, 1, 2, 2, 1, 0, 1, 0, 0, 0, 3, 0, 3, 2, 3, 2, 2, 1]) = 1 :=
    variant_eq_one word396_eq_one false
      11 (by decide +kernel)
  have hc : eval (decode [2, 2, 1, 1, 0, 1, 1, 0, 0, 0, 3, 0, 3, 2, 3, 2, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 419. -/
abbrev word419 : Word := decode [0, 0, 0, 0, 0, 3, 0, 1, 2, 2, 3, 0, 3, 3, 3, 2, 3, 3]

/-- Node 419 holds in the exact M11 presentation group. -/
theorem word419_eq_one : eval word419 = 1 := by
  have hl : eval (decode [3, 2, 3, 3, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 2, 1, 0]) = 1 :=
    variant_eq_one word120_eq_one false
      13 (by decide +kernel)
  have hr : eval (decode [2, 3, 0, 1, 1, 1, 1, 2, 3, 0, 1, 2, 2, 3, 0, 3, 3]) = 1 :=
    variant_eq_one word397_eq_one true
      4 (by decide +kernel)
  have hc : eval (decode [3, 2, 3, 3, 0, 0, 0, 0, 0, 3, 0, 1, 2, 2, 3, 0, 3, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    4 (by decide +kernel)

/-- Canonical signed word at certificate node 420. -/
abbrev word420 : Word := decode [0, 0, 0, 3, 0, 0, 3, 0, 1, 2, 2, 3, 3, 2, 1, 2, 2, 3]

/-- Node 420 holds in the exact M11 presentation group. -/
theorem word420_eq_one : eval word420 = 1 := by
  have hl : eval (decode [3, 2, 1, 2, 2, 3, 0, 1, 0, 1, 1, 2]) = 1 :=
    variant_eq_one word46_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [0, 3, 3, 2, 3, 0, 0, 3, 0, 0, 3, 0, 1, 2, 2, 3]) = 1 :=
    variant_eq_one word398_eq_one false
      11 (by decide +kernel)
  have hc : eval (decode [3, 2, 1, 2, 2, 3, 0, 0, 0, 3, 0, 0, 3, 0, 1, 2, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 421. -/
abbrev word421 : Word := decode [0, 0, 3, 0, 1, 2, 2, 3, 3, 2, 3, 3, 3, 0, 1, 1]

/-- Node 421 holds in the exact M11 presentation group. -/
theorem word421_eq_one : eval word421 = 1 := by
  have hl : eval (decode [3, 2, 3, 3, 3, 0, 1, 1, 1, 2, 2, 1, 0, 1, 1, 2]) = 1 :=
    variant_eq_one word149_eq_one true
      5 (by decide +kernel)
  have hr : eval (decode [0, 3, 3, 2, 3, 0, 0, 3, 0, 0, 3, 0, 1, 2, 2, 3]) = 1 :=
    variant_eq_one word398_eq_one false
      11 (by decide +kernel)
  have hc : eval (decode [3, 2, 3, 3, 3, 0, 1, 1, 0, 0, 3, 0, 1, 2, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 422. -/
abbrev word422 : Word := decode [0, 0, 1, 2, 2, 1, 0, 1, 1, 2, 3, 3, 0, 3, 0, 3, 2, 1]

/-- Node 422 holds in the exact M11 presentation group. -/
theorem word422_eq_one : eval word422 = 1 := by
  have hl : eval (decode [0, 3, 3, 2, 3, 0, 0, 3, 0, 0, 3, 0, 1, 2, 2, 3]) = 1 :=
    variant_eq_one word398_eq_one false
      11 (by decide +kernel)
  have hr : eval (decode [1, 0, 0, 3, 2, 1, 2, 2, 2, 2, 3, 0, 1, 2, 1, 2, 1, 1]) = 1 :=
    variant_eq_one word251_eq_one true
      8 (by decide +kernel)
  have hc : eval (decode [0, 3, 3, 2, 3, 0, 0, 3, 2, 2, 3, 0, 1, 2, 1, 2, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 426. -/
abbrev word426 : Word := decode [0, 0, 1, 2, 2, 1, 0, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1]

/-- Node 426 holds in the exact M11 presentation group. -/
theorem word426_eq_one : eval word426 = 1 := by
  have hl : eval (decode [3, 0, 3, 3, 2, 3, 0, 0, 3, 0, 0, 3, 0, 1, 2, 2]) = 1 :=
    variant_eq_one word398_eq_one false
      10 (by decide +kernel)
  have hr : eval (decode [0, 0, 3, 2, 1, 2, 2, 2, 2, 3, 0, 1, 0, 0, 3]) = 1 :=
    variant_eq_one word224_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [3, 0, 3, 3, 2, 3, 0, 0, 3, 2, 2, 3, 0, 1, 0, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 432. -/
abbrev word432 : Word := decode [0, 0, 0, 3, 3, 2, 3, 2, 3, 2, 1, 1, 1, 0, 1, 1]

/-- Node 432 holds in the exact M11 presentation group. -/
theorem word432_eq_one : eval word432 = 1 := by
  have hl : eval (decode [0, 1, 0, 1, 1, 2, 2, 2, 3, 0, 3, 3, 2, 3, 0, 0, 3, 3]) = 1 :=
    variant_eq_one word400_eq_one true
      10 (by decide +kernel)
  have hr : eval (decode [1, 1, 2, 2, 1, 0, 1, 1, 2, 3, 2, 3, 3, 3, 0, 1]) = 1 :=
    variant_eq_one word149_eq_one true
      12 (by decide +kernel)
  have hc : eval (decode [0, 1, 0, 1, 1, 2, 2, 2, 3, 3, 2, 3, 3, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 434. -/
abbrev word434 : Word := decode [0, 0, 1, 1, 0, 3, 2, 3, 0, 1, 2, 3, 3, 2, 1, 0, 3, 3]

/-- Node 434 holds in the exact M11 presentation group. -/
theorem word434_eq_one : eval word434 = 1 := by
  have hl : eval (decode [3, 0, 0, 1, 1, 0, 3, 2, 3, 0, 0, 1, 0, 3, 2, 2, 3, 2]) = 1 :=
    variant_eq_one word402_eq_one false
      9 (by decide +kernel)
  have hr : eval (decode [0, 1, 0, 0, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 0, 3]) = 1 :=
    variant_eq_one word52_eq_one false
      14 (by decide +kernel)
  have hc : eval (decode [3, 0, 0, 1, 1, 0, 3, 2, 3, 0, 1, 2, 3, 3, 2, 1, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 435. -/
abbrev word435 : Word := decode [0, 0, 0, 3, 3, 2, 2, 3, 0, 0, 3, 3, 0, 1, 1]

/-- Node 435 holds in the exact M11 presentation group. -/
theorem word435_eq_one : eval word435 = 1 := by
  have hl : eval (decode [3, 3, 0, 1, 1, 0, 0, 3, 3, 2, 2, 1, 1, 0, 3, 0, 3]) = 1 :=
    variant_eq_one word401_eq_one true
      6 (by decide +kernel)
  have hr : eval (decode [1, 2, 1, 2, 3, 3, 0, 0, 1, 1, 0, 3, 3, 2, 2, 3, 0, 0]) = 1 :=
    variant_eq_one word403_eq_one false
      12 (by decide +kernel)
  have hc : eval (decode [3, 3, 0, 1, 1, 0, 0, 0, 3, 3, 2, 2, 3, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 437. -/
abbrev word437 : Word := decode [0, 0, 3, 0, 3, 2, 3, 0, 3, 3, 2, 1, 2, 3]

/-- Node 437 holds in the exact M11 presentation group. -/
theorem word437_eq_one : eval word437 = 1 := by
  have hl : eval (decode [3, 2, 2, 3, 0, 3, 3, 2, 1, 1, 1, 2, 1, 0, 0, 0, 3, 2]) = 1 :=
    variant_eq_one word410_eq_one false
      5 (by decide +kernel)
  have hr : eval (decode [0, 1, 2, 2, 2, 3, 0, 3, 3, 2, 3, 0, 0, 3, 0, 3, 0, 1]) = 1 :=
    variant_eq_one word399_eq_one true
      13 (by decide +kernel)
  have hc : eval (decode [2, 3, 0, 3, 3, 2, 1, 2, 3, 0, 0, 3, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [3, 2])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 438. -/
abbrev word438 : Word := decode [0, 1, 0, 3, 3, 2, 3, 0, 3, 3, 0, 1, 1, 1, 2, 1]

/-- Node 438 holds in the exact M11 presentation group. -/
theorem word438_eq_one : eval word438 = 1 := by
  have hl : eval (decode [1, 1, 2, 1, 0, 1, 0, 3, 0, 1, 2, 2, 3, 0, 3, 3, 3, 0]) = 1 :=
    variant_eq_one word411_eq_one true
      6 (by decide +kernel)
  have hr : eval (decode [2, 1, 1, 1, 2, 1, 0, 0, 3, 2, 3, 2, 3, 0, 3, 3, 0, 1]) = 1 :=
    variant_eq_one word385_eq_one false
      12 (by decide +kernel)
  have hc : eval (decode [1, 1, 2, 1, 0, 1, 0, 3, 3, 2, 3, 0, 3, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    4 (by decide +kernel)

/-- Canonical signed word at certificate node 439. -/
abbrev word439 : Word := decode [0, 0, 3, 3, 3, 3, 2, 1, 0, 3, 0, 1, 1, 2, 1, 0, 1]

/-- Node 439 holds in the exact M11 presentation group. -/
theorem word439_eq_one : eval word439 = 1 := by
  have hl : eval (decode [3, 0, 1, 1, 2, 1, 0, 1, 0, 3, 0, 1, 2, 2, 3, 0, 3, 3]) = 1 :=
    variant_eq_one word411_eq_one true
      4 (by decide +kernel)
  have hr : eval (decode [1, 1, 2, 1, 0, 0, 3, 2, 1, 0, 3, 3, 3, 3, 2, 1, 0]) = 1 :=
    variant_eq_one word397_eq_one false
      13 (by decide +kernel)
  have hc : eval (decode [3, 0, 1, 1, 2, 1, 0, 1, 0, 0, 3, 3, 3, 3, 2, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 440. -/
abbrev word440 : Word := decode [0, 1, 0, 1, 2, 3, 0, 1, 1, 0, 3, 2, 1, 2, 3, 2, 1]

/-- Node 440 holds in the exact M11 presentation group. -/
theorem word440_eq_one : eval word440 = 1 := by
  have hl : eval (decode [3, 2, 1, 2, 3, 2, 1, 0, 1, 2, 2, 1, 0, 1, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word412_eq_one false
      4 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 2, 3, 2, 3, 0, 0, 0, 1, 2, 3, 0, 1, 1, 0]) = 1 :=
    variant_eq_one word284_eq_one false
      10 (by decide +kernel)
  have hc : eval (decode [3, 2, 1, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 0, 1, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 443. -/
abbrev word443 : Word := decode [0, 0, 0, 3, 3, 2, 2, 3, 2, 1, 2, 1, 1, 0, 1, 1]

/-- Node 443 holds in the exact M11 presentation group. -/
theorem word443_eq_one : eval word443 = 1 := by
  have hl : eval (decode [0, 3, 2, 3, 3, 0, 0, 0, 1, 2, 2, 1]) = 1 :=
    variant_eq_one word76_eq_one false
      7 (by decide +kernel)
  have hr : eval (decode [3, 0, 0, 3, 2, 2, 3, 0, 1, 0, 0, 1, 1, 2, 2, 2, 3, 2]) = 1 :=
    variant_eq_one word413_eq_one true
      2 (by decide +kernel)
  have hc : eval (decode [3, 2, 3, 3, 0, 3, 0, 1, 0, 0, 1, 1, 2, 2, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 445. -/
abbrev word445 : Word := decode [0, 0, 1, 0, 0, 1, 0, 3, 2, 1, 0, 3, 2, 2, 3, 2, 1]

/-- Node 445 holds in the exact M11 presentation group. -/
theorem word445_eq_one : eval word445 = 1 := by
  have hl : eval (decode [3, 2, 2, 3, 2, 1, 0, 0, 1, 2, 2, 1, 0, 1, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word413_eq_one false
      4 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 2, 3, 2, 3, 0, 0, 0, 0, 1, 0, 3, 2, 1, 0]) = 1 :=
    variant_eq_one word285_eq_one false
      10 (by decide +kernel)
  have hc : eval (decode [3, 2, 2, 3, 2, 1, 0, 0, 1, 0, 0, 1, 0, 3, 2, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 446. -/
abbrev word446 : Word := decode [0, 1, 0, 3, 3, 0, 1, 2, 3, 3, 2, 1, 0, 3, 2, 3, 3]

/-- Node 446 holds in the exact M11 presentation group. -/
theorem word446_eq_one : eval word446 = 1 := by
  have hl : eval (decode [2, 3, 3, 2, 1, 0, 3, 2, 2, 2, 1, 0, 1, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word284_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 2, 3, 2, 3, 0, 0, 3, 3, 0, 1, 0, 3, 3, 0, 1]) = 1 :=
    variant_eq_one word414_eq_one true
      14 (by decide +kernel)
  have hc : eval (decode [2, 3, 3, 2, 1, 0, 3, 2, 3, 3, 0, 1, 0, 3, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    10 (by decide +kernel)

/-- Canonical signed word at certificate node 448. -/
abbrev word448 : Word := decode [0, 0, 1, 0, 1, 2, 2, 3, 3, 2, 2, 1, 2, 3, 3]

/-- Node 448 holds in the exact M11 presentation group. -/
theorem word448_eq_one : eval word448 = 1 := by
  have hl : eval (decode [0, 1, 1, 0, 0, 3, 2, 3, 2, 2, 1, 0, 1, 0, 1, 2, 3]) = 1 :=
    variant_eq_one word415_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [1, 0, 3, 2, 3, 2, 1, 0, 3, 0]) = 1 :=
    variant_eq_one word1_eq_one true
      4 (by decide +kernel)
  have hc : eval (decode [0, 1, 1, 0, 0, 3, 2, 3, 2, 2, 1, 1, 0, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 449. -/
abbrev word449 : Word := decode [0, 0, 1, 0, 1, 2, 2, 3, 3, 0, 3, 3, 3, 3, 3, 3]

/-- Node 449 holds in the exact M11 presentation group. -/
theorem word449_eq_one : eval word449 = 1 := by
  have hl : eval (decode [0, 1, 1, 0, 0, 3, 2, 3, 2, 2, 1, 0, 1, 0, 1, 2, 3]) = 1 :=
    variant_eq_one word415_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [1, 0, 3, 2, 3, 2, 1, 1, 1, 1, 1, 2, 2]) = 1 :=
    variant_eq_one word26_eq_one true
      0 (by decide +kernel)
  have hc : eval (decode [1, 1, 0, 0, 3, 2, 3, 2, 2, 1, 1, 1, 1, 1, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 451. -/
abbrev word451 : Word := decode [0, 0, 0, 1, 1, 2, 1, 1, 0, 0, 3, 2, 3, 2, 3]

/-- Node 451 holds in the exact M11 presentation group. -/
theorem word451_eq_one : eval word451 = 1 := by
  have hl : eval (decode [0, 1, 1, 0, 0, 3, 2, 3, 2, 2, 1, 0, 1, 0, 1, 2, 3]) = 1 :=
    variant_eq_one word415_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [1, 0, 3, 2, 3, 2, 3, 0, 3, 0, 0, 0, 1, 1, 2, 2]) = 1 :=
    variant_eq_one word91_eq_one false
      7 (by decide +kernel)
  have hc : eval (decode [1, 1, 0, 0, 3, 2, 3, 2, 3, 0, 0, 0, 1, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 452. -/
abbrev word452 : Word := decode [0, 0, 1, 1, 0, 0, 3, 2, 3, 0, 1, 2, 2, 1, 0, 3, 3]

/-- Node 452 holds in the exact M11 presentation group. -/
theorem word452_eq_one : eval word452 = 1 := by
  have hl : eval (decode [0, 1, 1, 0, 0, 3, 2, 3, 2, 2, 1, 0, 1, 0, 1, 2, 3]) = 1 :=
    variant_eq_one word415_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [1, 0, 3, 2, 3, 2, 3, 0, 0, 0, 1, 2, 2, 1, 0, 3, 3, 0]) = 1 :=
    variant_eq_one word165_eq_one false
      11 (by decide +kernel)
  have hc : eval (decode [0, 1, 1, 0, 0, 3, 2, 3, 0, 1, 2, 2, 1, 0, 3, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    16 (by decide +kernel)

/-- Canonical signed word at certificate node 461. -/
abbrev word461 : Word := decode [0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 3, 2, 3, 2, 3, 3]

/-- Node 461 holds in the exact M11 presentation group. -/
theorem word461_eq_one : eval word461 = 1 := by
  have hl : eval (decode [0, 3, 3, 0, 0, 0, 0, 0, 1, 1, 2, 3, 2, 2, 3, 2, 3]) = 1 :=
    variant_eq_one word346_eq_one false
      14 (by decide +kernel)
  have hr : eval (decode [1, 0, 1, 0, 0, 1, 0, 3, 2, 1, 0, 0, 3, 2, 3, 2, 2]) = 1 :=
    variant_eq_one word416_eq_one true
      0 (by decide +kernel)
  have hc : eval (decode [3, 3, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 3, 2, 3, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    2 (by decide +kernel)

/-- Canonical signed word at certificate node 462. -/
abbrev word462 : Word := decode [0, 0, 0, 3, 2, 2, 3, 2, 3, 0, 3, 0, 3, 3]

/-- Node 462 holds in the exact M11 presentation group. -/
theorem word462_eq_one : eval word462 = 1 := by
  have hl : eval (decode [2, 2, 2, 1, 1, 2, 1, 0, 1, 0, 1, 2, 2, 3, 0, 1, 2]) = 1 :=
    variant_eq_one word369_eq_one true
      14 (by decide +kernel)
  have hr : eval (decode [0, 3, 2, 1, 0, 0, 3, 2, 3, 2, 2, 1, 0, 1, 0, 0, 1]) = 1 :=
    variant_eq_one word416_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [2, 2, 2, 1, 1, 2, 1, 2, 1, 0, 1, 0, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 465. -/
abbrev word465 : Word := decode [0, 0, 3, 3, 3, 0, 1, 2, 1, 2, 1, 0, 1]

/-- Node 465 holds in the exact M11 presentation group. -/
theorem word465_eq_one : eval word465 = 1 := by
  have hl : eval (decode [3, 3, 3, 3, 0, 1, 2, 1, 0, 1, 0, 1, 2, 2, 3, 0, 1, 2]) = 1 :=
    variant_eq_one word391_eq_one true
      4 (by decide +kernel)
  have hr : eval (decode [0, 3, 2, 1, 0, 0, 3, 2, 3, 2, 2, 1, 0, 1, 0, 0, 1]) = 1 :=
    variant_eq_one word416_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [3, 3, 3, 0, 1, 2, 1, 2, 1, 0, 1, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [3])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 476. -/
abbrev word476 : Word := decode [0, 0, 3, 3, 0, 3, 3, 3, 2, 3, 3, 0, 3, 0, 1]

/-- Node 476 holds in the exact M11 presentation group. -/
theorem word476_eq_one : eval word476 = 1 := by
  have hl : eval (decode [3, 0, 1, 0, 0, 3, 0, 0, 3, 2, 1, 2, 2, 2, 2]) = 1 :=
    variant_eq_one word224_eq_one true
      0 (by decide +kernel)
  have hr : eval (decode [0, 0, 0, 0, 3, 0, 1, 2, 2, 3, 0, 3, 3, 3, 2, 3, 3, 0]) = 1 :=
    variant_eq_one word419_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [3, 0, 1, 0, 0, 3, 3, 0, 3, 3, 3, 2, 3, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    3 (by decide +kernel)

/-- Canonical signed word at certificate node 478. -/
abbrev word478 : Word := decode [0, 1, 1, 1, 2, 3, 3, 0, 3, 0, 3, 2, 1, 2, 1, 1]

/-- Node 478 holds in the exact M11 presentation group. -/
theorem word478_eq_one : eval word478 = 1 := by
  have hl : eval (decode [3, 0, 1, 2, 1, 2, 1, 1, 1, 0, 0, 3, 2, 1, 2, 2, 2, 2]) = 1 :=
    variant_eq_one word251_eq_one true
      0 (by decide +kernel)
  have hr : eval (decode [0, 0, 0, 0, 3, 0, 1, 2, 2, 3, 0, 3, 3, 3, 2, 3, 3, 0]) = 1 :=
    variant_eq_one word419_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [3, 0, 1, 2, 1, 2, 1, 1, 0, 3, 3, 3, 2, 3, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    3 (by decide +kernel)

/-- Canonical signed word at certificate node 482. -/
abbrev word482 : Word := decode [0, 0, 0, 3, 2, 2, 3, 0, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3]

/-- Node 482 holds in the exact M11 presentation group. -/
theorem word482_eq_one : eval word482 = 1 := by
  have hl : eval (decode [2, 2, 3, 0, 1, 2, 1, 2, 1, 1, 1, 0, 0, 3, 2, 1, 2, 2]) = 1 :=
    variant_eq_one word251_eq_one true
      16 (by decide +kernel)
  have hr : eval (decode [0, 0, 3, 0, 1, 2, 2, 3, 3, 2, 1, 2, 2, 3, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word420_eq_one false
      4 (by decide +kernel)
  have hc : eval (decode [2, 2, 3, 0, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 0, 0, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    14 (by decide +kernel)

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations
