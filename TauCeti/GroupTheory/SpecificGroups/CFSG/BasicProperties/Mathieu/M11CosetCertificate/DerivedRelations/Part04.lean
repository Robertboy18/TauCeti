/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.DerivedRelations.Part03

/-! Certified consequences of the exact M11 presentation relations. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations

/-- Canonical signed word at certificate node 337. -/
abbrev word337 : Word := decode [0, 0, 1, 0, 3, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1]

/-- Node 337 holds in the exact M11 presentation group. -/
theorem word337_eq_one : eval word337 = 1 := by
  have hl : eval (decode [2, 3, 2, 2, 3, 0, 3, 3, 0, 0, 1, 0, 0, 0, 3, 2, 1, 2]) = 1 :=
    variant_eq_one word302_eq_one false
      7 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 1, 2, 2, 2, 3, 3, 0, 0, 3, 3, 0, 0, 1]) = 1 :=
    variant_eq_one word259_eq_one true
      9 (by decide +kernel)
  have hc : eval (decode [2, 3, 2, 2, 3, 0, 3, 3, 0, 0, 3, 0, 0, 3, 3, 0, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 340. -/
abbrev word340 : Word := decode [0, 0, 1, 0, 1, 1, 1, 2, 2, 3, 0, 3, 2, 3, 3, 3, 2, 1]

/-- Node 340 holds in the exact M11 presentation group. -/
theorem word340_eq_one : eval word340 = 1 := by
  have hl : eval (decode [3, 2, 2, 3, 0, 1, 1, 1, 2, 3, 0, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word296_eq_one true
      12 (by decide +kernel)
  have hr : eval (decode [2, 1, 2, 1, 2, 1, 0, 0, 1, 2, 1, 0, 0, 3, 3, 3, 2]) = 1 :=
    variant_eq_one word309_eq_one true
      16 (by decide +kernel)
  have hc : eval (decode [3, 2, 2, 3, 0, 1, 1, 1, 0, 1, 2, 1, 0, 0, 3, 3, 3, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 342. -/
abbrev word342 : Word := decode [0, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 2, 3, 3, 3, 2, 1]

/-- Node 342 holds in the exact M11 presentation group. -/
theorem word342_eq_one : eval word342 = 1 := by
  have hl : eval (decode [3, 2, 2, 3, 0, 1, 1, 1, 2, 3, 0, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word296_eq_one true
      12 (by decide +kernel)
  have hr : eval (decode [2, 1, 2, 1, 2, 1, 0, 0, 1, 2, 1, 2, 1, 2, 1, 2]) = 1 :=
    variant_eq_one word311_eq_one false
      10 (by decide +kernel)
  have hc : eval (decode [3, 2, 2, 3, 0, 1, 1, 1, 0, 1, 2, 1, 2, 1, 2, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 344. -/
abbrev word344 : Word := decode [0, 0, 0, 1, 0, 0, 3, 3, 0, 3, 3, 3, 3, 2, 1, 1, 2, 3]

/-- Node 344 holds in the exact M11 presentation group. -/
theorem word344_eq_one : eval word344 = 1 := by
  have hl : eval (decode [3, 3, 3, 3, 2, 1, 1, 2, 3, 0, 3, 0, 1, 1, 0, 1, 0, 3]) = 1 :=
    variant_eq_one word262_eq_one false
      4 (by decide +kernel)
  have hr : eval (decode [1, 2, 3, 2, 3, 3, 2, 1, 0, 0, 1, 0, 0, 3, 3, 0]) = 1 :=
    variant_eq_one word313_eq_one false
      8 (by decide +kernel)
  have hc : eval (decode [3, 3, 3, 3, 2, 1, 1, 2, 3, 0, 0, 0, 1, 0, 0, 3, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 346. -/
abbrev word346 : Word := decode [0, 0, 0, 0, 0, 1, 1, 2, 3, 2, 2, 3, 2, 3, 0, 3, 3]

/-- Node 346 holds in the exact M11 presentation group. -/
theorem word346_eq_one : eval word346 = 1 := by
  have hl : eval (decode [3, 2, 2, 2, 2, 2, 1, 0, 0, 0, 1, 1, 2, 1, 0]) = 1 :=
    variant_eq_one word318_eq_one true
      9 (by decide +kernel)
  have hr : eval (decode [2, 3, 0, 3, 3, 2, 2, 2, 1, 2, 1, 0, 1, 0, 0, 1, 0, 3]) = 1 :=
    variant_eq_one word126_eq_one true
      10 (by decide +kernel)
  have hc : eval (decode [3, 2, 2, 2, 2, 2, 1, 1, 2, 1, 0, 1, 0, 0, 1, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 351. -/
abbrev word351 : Word := decode [0, 0, 0, 1, 1, 2, 2, 1, 2, 3, 0, 3, 3, 3, 0, 3, 2, 1]

/-- Node 351 holds in the exact M11 presentation group. -/
theorem word351_eq_one : eval word351 = 1 := by
  have hl : eval (decode [2, 1, 0, 0, 0, 1, 1, 2, 1, 0, 3, 2, 2, 2, 2]) = 1 :=
    variant_eq_one word318_eq_one true
      14 (by decide +kernel)
  have hr : eval (decode [0, 0, 0, 0, 1, 2, 3, 2, 1, 2, 3, 0, 3, 3, 3, 0, 3]) = 1 :=
    variant_eq_one word36_eq_one false
      0 (by decide +kernel)
  have hc : eval (decode [2, 1, 0, 0, 0, 1, 1, 2, 2, 1, 2, 3, 0, 3, 3, 3, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    2 (by decide +kernel)

/-- Canonical signed word at certificate node 358. -/
abbrev word358 : Word := decode [0, 0, 1, 2, 1, 2, 1, 0, 1, 2, 2, 3, 0, 3, 0, 3, 2, 3]

/-- Node 358 holds in the exact M11 presentation group. -/
theorem word358_eq_one : eval word358 = 1 := by
  have hl : eval (decode [3, 0, 3, 0, 3, 2, 3, 0, 0, 0, 3, 2, 2, 3, 0, 0, 3, 0]) = 1 :=
    variant_eq_one word321_eq_one false
      11 (by decide +kernel)
  have hr : eval (decode [2, 1, 2, 2, 1, 0, 0, 1, 2, 1, 2, 1, 2, 1, 0, 1, 2, 2]) = 1 :=
    variant_eq_one word323_eq_one true
      17 (by decide +kernel)
  have hc : eval (decode [3, 0, 3, 0, 3, 2, 3, 0, 0, 1, 2, 1, 2, 1, 0, 1, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 359. -/
abbrev word359 : Word := decode [0, 0, 0, 1, 2, 1, 1, 0, 3, 3, 3, 3, 2, 3, 3, 3, 0, 1]

/-- Node 359 holds in the exact M11 presentation group. -/
theorem word359_eq_one : eval word359 = 1 := by
  have hl : eval (decode [3, 0, 3, 2, 2, 2, 3, 2, 1, 1, 2, 1, 0, 0, 0, 0, 3, 0]) = 1 :=
    variant_eq_one word325_eq_one false
      6 (by decide +kernel)
  have hr : eval (decode [2, 1, 2, 2, 2, 2, 3, 0, 1, 0, 1, 1, 1, 1, 2, 3]) = 1 :=
    variant_eq_one word184_eq_one true
      10 (by decide +kernel)
  have hc : eval (decode [3, 0, 3, 2, 2, 2, 3, 2, 1, 1, 1, 0, 1, 1, 1, 1, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    12 (by decide +kernel)

/-- Canonical signed word at certificate node 361. -/
abbrev word361 : Word := decode [0, 0, 0, 1, 2, 3, 3, 0, 3, 0, 1, 2, 2, 3, 3, 3, 0, 1]

/-- Node 361 holds in the exact M11 presentation group. -/
theorem word361_eq_one : eval word361 = 1 := by
  have hl : eval (decode [3, 3, 0, 3, 0, 1, 2, 2, 3, 2, 1, 0, 0, 0, 0, 3, 0, 3]) = 1 :=
    variant_eq_one word244_eq_one false
      7 (by decide +kernel)
  have hr : eval (decode [1, 2, 1, 2, 2, 2, 2, 3, 0, 3, 3, 0, 1, 0, 0, 0, 1, 2]) = 1 :=
    variant_eq_one word325_eq_one true
      11 (by decide +kernel)
  have hc : eval (decode [3, 3, 0, 3, 0, 1, 2, 2, 3, 3, 3, 0, 1, 0, 0, 0, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    13 (by decide +kernel)

/-- Canonical signed word at certificate node 368. -/
abbrev word368 : Word := decode [0, 0, 0, 0, 1, 1, 2, 2, 1, 2, 3, 0, 1, 2, 3, 3, 3, 3]

/-- Node 368 holds in the exact M11 presentation group. -/
theorem word368_eq_one : eval word368 = 1 := by
  have hl : eval (decode [0, 3, 2, 1, 0, 3, 0, 0, 3, 3, 2, 2, 2, 3, 0, 0, 0]) = 1 :=
    variant_eq_one word330_eq_one false
      3 (by decide +kernel)
  have hr : eval (decode [2, 2, 2, 1, 2, 1, 1, 1, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [0, 3, 2, 1, 0, 3, 0, 0, 3, 3, 2, 2, 2, 2, 1, 1, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    4 (by decide +kernel)

/-- Canonical signed word at certificate node 369. -/
abbrev word369 : Word := decode [0, 0, 0, 0, 3, 2, 1, 0, 0, 3, 2, 3, 2, 3, 0, 3, 3]

/-- Node 369 holds in the exact M11 presentation group. -/
theorem word369_eq_one : eval word369 = 1 := by
  have hl : eval (decode [2, 3, 0, 1, 2, 2, 2, 2, 1, 0, 0, 0, 1, 1, 2, 2, 1]) = 1 :=
    variant_eq_one word330_eq_one true
      9 (by decide +kernel)
  have hr : eval (decode [3, 0, 0, 3, 3, 2, 2, 2, 1, 2, 1, 0, 1, 0, 1, 2]) = 1 :=
    variant_eq_one word91_eq_one true
      8 (by decide +kernel)
  have hc : eval (decode [2, 3, 0, 1, 2, 2, 2, 2, 1, 1, 2, 1, 0, 1, 0, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 373. -/
abbrev word373 : Word := decode [0, 0, 0, 1, 1, 1, 1, 0, 0, 3, 2, 3, 2, 3, 3, 2, 2, 3]

/-- Node 373 holds in the exact M11 presentation group. -/
theorem word373_eq_one : eval word373 = 1 := by
  have hl : eval (decode [3, 2, 2, 3, 0, 0, 0, 1, 1, 2, 2, 2, 1, 1, 2, 3, 0, 0]) = 1 :=
    variant_eq_one word197_eq_one false
      14 (by decide +kernel)
  have hr : eval (decode [2, 2, 1, 0, 3, 3, 0, 0, 0, 1, 1, 0, 0, 3, 2, 3, 2, 3]) = 1 :=
    variant_eq_one word333_eq_one false
      12 (by decide +kernel)
  have hc : eval (decode [3, 2, 2, 3, 0, 0, 0, 1, 1, 1, 1, 0, 0, 3, 2, 3, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    4 (by decide +kernel)

/-- Canonical signed word at certificate node 375. -/
abbrev word375 : Word := decode [0, 0, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 1, 0, 3]

/-- Node 375 holds in the exact M11 presentation group. -/
theorem word375_eq_one : eval word375 = 1 := by
  have hl : eval (decode [0, 3, 3, 0, 0, 3, 0, 0, 3, 3, 0, 0, 1, 2, 3, 2, 2, 3]) = 1 :=
    variant_eq_one word337_eq_one true
      1 (by decide +kernel)
  have hr : eval (decode [1, 0, 0, 1, 0, 3, 2, 3, 2, 2, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word48_eq_one true
      4 (by decide +kernel)
  have hc : eval (decode [0, 3, 3, 0, 0, 3, 0, 0, 3, 3, 0, 3, 2, 2, 1, 2, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    4 (by decide +kernel)

/-- Canonical signed word at certificate node 376. -/
abbrev word376 : Word := decode [0, 0, 0, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3]

/-- Node 376 holds in the exact M11 presentation group. -/
theorem word376_eq_one : eval word376 = 1 := by
  have hl : eval (decode [0, 3, 3, 0, 0, 3, 0, 0, 3, 3, 0, 0, 1, 2, 3, 2, 2, 3]) = 1 :=
    variant_eq_one word337_eq_one true
      1 (by decide +kernel)
  have hr : eval (decode [1, 0, 0, 1, 0, 3, 2, 3, 0, 3, 2, 2, 2, 1]) = 1 :=
    variant_eq_one word125_eq_one true
      1 (by decide +kernel)
  have hc : eval (decode [0, 3, 3, 0, 0, 3, 0, 0, 3, 3, 0, 3, 0, 3, 2, 2, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 378. -/
abbrev word378 : Word := decode [0, 0, 0, 3, 0, 1, 2, 3, 0, 3, 2, 3, 3, 3, 2, 1, 0, 1]

/-- Node 378 holds in the exact M11 presentation group. -/
theorem word378_eq_one : eval word378 = 1 := by
  have hl : eval (decode [2, 3, 0, 1, 1, 1, 0, 1, 2, 1, 0, 0, 3, 3, 3, 2, 3, 2]) = 1 :=
    variant_eq_one word340_eq_one true
      17 (by decide +kernel)
  have hr : eval (decode [0, 1, 0, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3]) = 1 :=
    variant_eq_one word178_eq_one true
      1 (by decide +kernel)
  have hc : eval (decode [2, 3, 0, 1, 1, 1, 0, 1, 2, 1, 0, 3, 2, 1, 2, 2, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 379. -/
abbrev word379 : Word := decode [0, 0, 0, 1, 2, 3, 2, 3, 3, 3, 2, 1, 0, 1, 1, 2, 1]

/-- Node 379 holds in the exact M11 presentation group. -/
theorem word379_eq_one : eval word379 = 1 := by
  have hl : eval (decode [2, 3, 0, 1, 1, 1, 0, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2]) = 1 :=
    variant_eq_one word342_eq_one true
      16 (by decide +kernel)
  have hr : eval (decode [0, 1, 0, 3, 0, 3, 0, 3, 0, 0, 3, 2, 2, 2, 3, 0, 3, 3]) = 1 :=
    variant_eq_one word254_eq_one true
      4 (by decide +kernel)
  have hc : eval (decode [2, 3, 0, 1, 1, 1, 0, 1, 0, 3, 2, 2, 2, 3, 0, 3, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    4 (by decide +kernel)

/-- Canonical signed word at certificate node 380. -/
abbrev word380 : Word := decode [0, 0, 0, 1, 0, 0, 3, 3, 2, 2, 1, 2, 2, 1, 1, 2, 3]

/-- Node 380 holds in the exact M11 presentation group. -/
theorem word380_eq_one : eval word380 = 1 := by
  have hl : eval (decode [2, 1, 1, 2, 3, 0, 0, 0, 1, 0, 0, 3, 3, 0, 3, 3, 3, 3]) = 1 :=
    variant_eq_one word344_eq_one false
      13 (by decide +kernel)
  have hr : eval (decode [1, 1, 1, 1, 2, 2, 2, 1, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      2 (by decide +kernel)
  have hc : eval (decode [2, 1, 1, 2, 3, 0, 0, 0, 1, 0, 0, 3, 3, 2, 2, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 385. -/
abbrev word385 : Word := decode [0, 0, 3, 2, 3, 2, 3, 0, 3, 3, 0, 1, 2, 1, 1, 1, 2, 1]

/-- Node 385 holds in the exact M11 presentation group. -/
theorem word385_eq_one : eval word385 = 1 := by
  have hl : eval (decode [1, 2, 1, 0, 1, 0, 1, 2, 3, 0, 0, 3, 3, 2, 2, 2]) = 1 :=
    variant_eq_one word91_eq_one true
      0 (by decide +kernel)
  have hr : eval (decode [0, 0, 0, 1, 1, 2, 2, 1, 2, 3, 0, 3, 3, 3, 0, 3, 2, 1]) = 1 :=
    variant_eq_one word351_eq_one false
      0 (by decide +kernel)
  have hc : eval (decode [1, 2, 1, 0, 1, 0, 1, 2, 2, 3, 0, 3, 3, 3, 0, 3, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 388. -/
abbrev word388 : Word := decode [0, 0, 0, 1, 0, 3, 2, 2, 3, 2, 3, 0, 0, 1, 2, 1, 2, 3]

/-- Node 388 holds in the exact M11 presentation group. -/
theorem word388_eq_one : eval word388 = 1 := by
  have hl : eval (decode [3, 2, 3, 0, 0, 1, 2, 1, 2, 1, 0, 1, 2, 2, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word358_eq_one false
      15 (by decide +kernel)
  have hr : eval (decode [2, 1, 2, 1, 0, 0, 3, 2, 3, 3, 0, 0, 0, 1, 0, 3, 2, 2]) = 1 :=
    variant_eq_one word207_eq_one false
      8 (by decide +kernel)
  have hc : eval (decode [3, 2, 3, 0, 0, 1, 2, 1, 2, 3, 0, 0, 0, 1, 0, 3, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    10 (by decide +kernel)

/-- Canonical signed word at certificate node 391. -/
abbrev word391 : Word := decode [0, 0, 3, 2, 3, 2, 3, 0, 3, 2, 1, 1, 1, 1, 0, 3, 2, 1]

/-- Node 391 holds in the exact M11 presentation group. -/
theorem word391_eq_one : eval word391 = 1 := by
  have hl : eval (decode [2, 3, 0, 1, 2, 3, 3, 3, 3, 0, 0, 0, 0, 1, 1, 2, 2, 1]) = 1 :=
    variant_eq_one word368_eq_one false
      9 (by decide +kernel)
  have hr : eval (decode [3, 0, 0, 3, 3, 2, 2, 2, 1, 2, 1, 0, 1, 0, 1, 2]) = 1 :=
    variant_eq_one word91_eq_one true
      8 (by decide +kernel)
  have hc : eval (decode [2, 3, 0, 1, 2, 3, 3, 3, 3, 0, 1, 2, 1, 0, 1, 0, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    17 (by decide +kernel)

/-- Canonical signed word at certificate node 394. -/
abbrev word394 : Word := decode [0, 0, 1, 1, 2, 2, 3, 3, 3, 3, 3, 0, 0, 3, 3, 0, 0, 3]

/-- Node 394 holds in the exact M11 presentation group. -/
theorem word394_eq_one : eval word394 = 1 := by
  have hl : eval (decode [3, 0, 0, 3, 3, 0, 0, 3, 0, 0, 3, 3, 0, 3, 2, 2, 1, 2]) = 1 :=
    variant_eq_one word375_eq_one true
      2 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 0, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3]) = 1 :=
    variant_eq_one word7_eq_one false
      14 (by decide +kernel)
  have hc : eval (decode [3, 0, 0, 3, 3, 0, 0, 3, 0, 0, 1, 1, 2, 2, 3, 3, 3, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 395. -/
abbrev word395 : Word := decode [0, 0, 3, 3, 0, 3, 0, 3, 3, 2, 1, 1, 1, 2, 1, 2, 3, 3]

/-- Node 395 holds in the exact M11 presentation group. -/
theorem word395_eq_one : eval word395 = 1 := by
  have hl : eval (decode [3, 0, 0, 3, 3, 0, 3, 0, 3, 2, 2, 2, 1, 0, 3, 3, 0, 0]) = 1 :=
    variant_eq_one word376_eq_one true
      6 (by decide +kernel)
  have hr : eval (decode [2, 2, 1, 1, 2, 3, 0, 0, 0, 3, 2, 1, 1, 1, 2, 1, 2, 3]) = 1 :=
    variant_eq_one word293_eq_one false
      12 (by decide +kernel)
  have hc : eval (decode [3, 0, 0, 3, 3, 0, 3, 0, 3, 3, 2, 1, 1, 1, 2, 1, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 396. -/
abbrev word396 : Word := decode [0, 0, 0, 3, 0, 3, 2, 3, 2, 2, 1, 0, 1, 2, 2, 1, 0, 1]

/-- Node 396 holds in the exact M11 presentation group. -/
theorem word396_eq_one : eval word396 = 1 := by
  have hl : eval (decode [0, 3, 2, 3, 0, 0, 1, 0, 1, 1, 2, 3, 0, 3, 2, 3, 3, 3]) = 1 :=
    variant_eq_one word266_eq_one false
      14 (by decide +kernel)
  have hr : eval (decode [1, 1, 1, 0, 1, 2, 1, 0, 3, 2, 1, 2, 2, 2, 3, 2, 3, 0]) = 1 :=
    variant_eq_one word378_eq_one true
      4 (by decide +kernel)
  have hc : eval (decode [0, 3, 2, 3, 0, 0, 1, 0, 1, 2, 1, 2, 2, 2, 3, 2, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    4 (by decide +kernel)

/-- Canonical signed word at certificate node 397. -/
abbrev word397 : Word := decode [0, 0, 3, 2, 1, 0, 3, 3, 3, 3, 2, 1, 0, 1, 1, 2, 1]

/-- Node 397 holds in the exact M11 presentation group. -/
theorem word397_eq_one : eval word397 = 1 := by
  have hl : eval (decode [2, 2, 3, 0, 3, 3, 2, 3, 0, 1, 1, 1, 0, 1, 0, 3, 2]) = 1 :=
    variant_eq_one word379_eq_one true
      15 (by decide +kernel)
  have hr : eval (decode [0, 1, 2, 3, 2, 1, 2, 3, 0, 1]) = 1 :=
    variant_eq_one word1_eq_one false
      2 (by decide +kernel)
  have hc : eval (decode [2, 2, 3, 0, 3, 3, 2, 3, 0, 1, 1, 1, 1, 2, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 398. -/
abbrev word398 : Word := decode [0, 0, 3, 0, 0, 3, 0, 1, 2, 2, 3, 0, 3, 3, 2, 3]

/-- Node 398 holds in the exact M11 presentation group. -/
theorem word398_eq_one : eval word398 = 1 := by
  have hl : eval (decode [2, 2, 3, 0, 3, 3, 2, 3, 0, 1, 1, 1, 0, 1, 0, 3, 2]) = 1 :=
    variant_eq_one word379_eq_one true
      15 (by decide +kernel)
  have hr : eval (decode [0, 1, 2, 3, 2, 3, 3, 3, 0, 3, 0, 0, 3, 0, 1]) = 1 :=
    variant_eq_one word30_eq_one false
      5 (by decide +kernel)
  have hc : eval (decode [2, 2, 3, 0, 3, 3, 2, 3, 0, 0, 3, 0, 0, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 399. -/
abbrev word399 : Word := decode [0, 0, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 1, 1, 2, 1]

/-- Node 399 holds in the exact M11 presentation group. -/
theorem word399_eq_one : eval word399 = 1 := by
  have hl : eval (decode [2, 1, 0, 1, 1, 2, 1, 0, 0, 0, 1, 2, 3, 2, 3, 3, 3]) = 1 :=
    variant_eq_one word379_eq_one false
      10 (by decide +kernel)
  have hr : eval (decode [1, 1, 1, 0, 1, 0, 3, 3, 2, 3, 2, 1, 2, 1, 2]) = 1 :=
    variant_eq_one word146_eq_one true
      4 (by decide +kernel)
  have hc : eval (decode [2, 1, 0, 1, 1, 2, 1, 0, 0, 0, 3, 2, 3, 2, 1, 2, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 400. -/
abbrev word400 : Word := decode [0, 0, 0, 3, 3, 2, 3, 2, 1, 1, 2, 2, 1, 0, 1, 1, 2, 1]

/-- Node 400 holds in the exact M11 presentation group. -/
theorem word400_eq_one : eval word400 = 1 := by
  have hl : eval (decode [2, 1, 0, 1, 1, 2, 1, 0, 0, 0, 1, 2, 3, 2, 3, 3, 3]) = 1 :=
    variant_eq_one word379_eq_one false
      10 (by decide +kernel)
  have hr : eval (decode [1, 1, 1, 0, 1, 0, 3, 3, 3, 2, 3, 2, 1, 1, 2]) = 1 :=
    variant_eq_one word175_eq_one true
      3 (by decide +kernel)
  have hc : eval (decode [2, 1, 0, 1, 1, 2, 1, 0, 0, 0, 3, 3, 2, 3, 2, 1, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 401. -/
abbrev word401 : Word := decode [0, 0, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 1, 2, 3, 3]

/-- Node 401 holds in the exact M11 presentation group. -/
theorem word401_eq_one : eval word401 = 1 := by
  have hl : eval (decode [1, 0, 3, 0, 3, 3, 3, 0, 1, 2, 2, 2, 1, 0, 3, 3, 0, 0]) = 1 :=
    variant_eq_one word293_eq_one true
      6 (by decide +kernel)
  have hr : eval (decode [2, 2, 1, 1, 2, 3, 0, 0, 0, 1, 0, 0, 3, 3, 2, 2, 1]) = 1 :=
    variant_eq_one word380_eq_one false
      11 (by decide +kernel)
  have hc : eval (decode [1, 0, 3, 0, 3, 3, 3, 0, 1, 1, 0, 0, 3, 3, 2, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 402. -/
abbrev word402 : Word := decode [0, 0, 1, 0, 3, 2, 2, 3, 2, 3, 0, 0, 1, 1, 0, 3, 2, 3]

/-- Node 402 holds in the exact M11 presentation group. -/
theorem word402_eq_one : eval word402 = 1 := by
  have hl : eval (decode [0, 0, 1, 0, 3, 2, 2, 3, 2, 3, 0, 0, 1, 2, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word388_eq_one false
      1 (by decide +kernel)
  have hr : eval (decode [2, 1, 0, 3, 0, 1, 0, 3, 2, 3]) = 1 :=
    variant_eq_one word1_eq_one true
      9 (by decide +kernel)
  have hc : eval (decode [0, 0, 1, 0, 3, 2, 2, 3, 2, 3, 0, 0, 1, 1, 0, 3, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    0 (by decide +kernel)

/-- Canonical signed word at certificate node 403. -/
abbrev word403 : Word := decode [0, 0, 1, 1, 0, 3, 3, 2, 2, 3, 0, 0, 1, 2, 1, 2, 3, 3]

/-- Node 403 holds in the exact M11 presentation group. -/
theorem word403_eq_one : eval word403 = 1 := by
  have hl : eval (decode [3, 0, 0, 1, 1, 0, 3, 3, 2, 1, 0, 0, 1, 2, 3, 2, 2, 2]) = 1 :=
    variant_eq_one word329_eq_one true
      0 (by decide +kernel)
  have hr : eval (decode [0, 0, 0, 1, 0, 3, 2, 2, 3, 2, 3, 0, 0, 1, 2, 1, 2, 3]) = 1 :=
    variant_eq_one word388_eq_one false
      0 (by decide +kernel)
  have hc : eval (decode [3, 0, 0, 1, 1, 0, 3, 3, 2, 2, 3, 0, 0, 1, 2, 1, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 408. -/
abbrev word408 : Word := decode [0, 0, 0, 0, 3, 2, 3, 2, 3, 0, 0, 1, 1, 2, 2, 3, 3, 3]

/-- Node 408 holds in the exact M11 presentation group. -/
theorem word408_eq_one : eval word408 = 1 := by
  have hl : eval (decode [0, 1, 0, 1, 2, 2, 2, 2, 3, 3, 0, 0, 3, 3, 0, 0]) = 1 :=
    variant_eq_one word231_eq_one true
      8 (by decide +kernel)
  have hr : eval (decode [2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 0, 3, 3, 2, 2, 1]) = 1 :=
    variant_eq_one word394_eq_one true
      1 (by decide +kernel)
  have hc : eval (decode [0, 1, 0, 1, 2, 2, 2, 2, 1, 1, 1, 0, 0, 3, 3, 2, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    10 (by decide +kernel)

/-- Canonical signed word at certificate node 410. -/
abbrev word410 : Word := decode [0, 0, 0, 3, 2, 3, 2, 2, 3, 0, 3, 3, 2, 1, 1, 1, 2, 1]

/-- Node 410 holds in the exact M11 presentation group. -/
theorem word410_eq_one : eval word410 = 1 := by
  have hl : eval (decode [3, 0, 3, 3, 3, 0, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 0]) = 1 :=
    variant_eq_one word395_eq_one true
      3 (by decide +kernel)
  have hr : eval (decode [2, 3, 3, 0, 0, 3, 3, 0, 0, 0, 1, 0, 1, 2, 2, 2]) = 1 :=
    variant_eq_one word231_eq_one true
      15 (by decide +kernel)
  have hc : eval (decode [3, 0, 3, 3, 3, 0, 1, 1, 2, 1, 0, 0, 1, 0, 1, 2, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    0 (by decide +kernel)

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations
