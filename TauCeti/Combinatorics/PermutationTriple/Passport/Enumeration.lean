/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.Basic

/-!
# Connected permutation triples in small degree, counted

Connectedness of a permutation triple is decidable and the isomorphism classes of connected
triples of a given degree form a computable `Fintype`, so the number of isomorphism classes of
connected triples — equivalently, of connected dessins d'enfants with a given number of edges —
can be established in small degree by kernel computation. This file records the counts in
degrees one to three:

```text
degree               1   2   3
connected classes    1   3   7
```

The three degree-two classes are the double cover of the sphere branched at two of the three
branch points, one class for each choice of the unbranched point. The seven degree-three classes
are the cyclic cover `z ↦ z³` in its three orderings of the branch points (monodromy `C₃`, one
branch point unramified), the `S₃`-cover `TauCeti.PermutationTriple.s3Triple` in its three
orderings (monodromy `S₃`), and the genus-one cover with a three-cycle at every branch point
(monodromy `C₃`). The count in degree four is `26`; its kernel check takes several minutes, so
no theorem records it.

## Main results

* `TauCeti.ConnectedIsoClass.card_one`, `TauCeti.ConnectedIsoClass.card_two`,
  `TauCeti.ConnectedIsoClass.card_three`: the number of isomorphism classes of connected
  permutation triples of degree one, two, and three.
-/

public section

namespace TauCeti

namespace ConnectedIsoClass

/-- There is one isomorphism class of connected permutation triples of degree one. -/
theorem card_one : Fintype.card (ConnectedIsoClass 1) = 1 := by decide

/-- There are three isomorphism classes of connected permutation triples of degree two. -/
theorem card_two : Fintype.card (ConnectedIsoClass 2) = 3 := by decide

/-- There are seven isomorphism classes of connected permutation triples of degree three. -/
theorem card_three : Fintype.card (ConnectedIsoClass 3) = 7 := by decide +kernel

end ConnectedIsoClass

end TauCeti
