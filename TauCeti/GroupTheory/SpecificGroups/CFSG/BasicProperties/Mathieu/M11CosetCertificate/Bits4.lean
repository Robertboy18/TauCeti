/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.TableBits

/-!
# M11 coset certificate: Bits4

Literal checkpoints: four natural-number masks at each stage.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def bits064row0 : ℕ :=
  0xfbffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefbfff6d9ebd2efab7fff7ff7f7feffffffffff7fffffbfffdffffd7ffff * 2 ^ 240 +
  0x7ff5b3bf77f777fee377bdf6fb5dfe55fe937c3a7ff6ebefabbffab3fdff * 2 ^ 480 +
  0x90e99418d4a13792b93f30685eeee66ca4236af7ee7b9ed698b7e7fb5ffb * 2 ^ 720 +
  0x22669857 * 2 ^ 960

@[expose]
def bits064row1 : ℕ :=
  0xfafffefffffefffffdffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbfdff3df9ddeebfdfedfefffffbfbfebfe5fff9f7ffe67fff * 2 ^ 240 +
  0xbb237bd3ffedf5b7a6eb8bdbddc4bed33fdbdb8dfbe8ccf9fd7fd7357b9d * 2 ^ 480 +
  0x8be8ebfc4032f4e28eec9bb22beb9ab46d07775bdfebdcc910bfcdf591fa * 2 ^ 720 +
  0x42a299b * 2 ^ 960

@[expose]
def bits064row2 : ℕ :=
  0x9f3ffbffffeffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbbff7b7f5fefdffffffefddfefef6fff9ff777feffbfffffffffdffbff * 2 ^ 240 +
  0xff6b8fdff5d3de6e3b77bef9beff7ffae8df7779eff2d7ad2faadfe77ff9 * 2 ^ 480 +
  0x3fed920a99b13dd54cdd3eefe275e769abc8ac50e27f8d9ca1ffd52cbbfa * 2 ^ 720 +
  0x112b4b61 * 2 ^ 960

@[expose]
def bits064row3 : ℕ :=
  0xeffbffaffefff77ffffffeffffffffbffffffffffffffeffffffffffffff * 2 ^ 0 +
  0xefe6bffeadff7ff77d6fffedf6efdf7bbfefffffbfffdfffff77fed5ffff * 2 ^ 240 +
  0x7e7a9bbd7c33cebc71d7ffa5937f76f9e378e2ff5bf3d40f8b5ff89d7fb6 * 2 ^ 480 +
  0x4a572703ea5d3d4c06b8c625d5e84357ba908e3b8f4aecf747dbcd88efde * 2 ^ 720 +
  0x8d92e03 * 2 ^ 960

@[expose]
def bits064 : Vector ℕ 4 := #v[bits064row0, bits064row1, bits064row2, bits064row3]

@[expose]
def bits065row0 : ℕ :=
  0xfbffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefbfff7dbebd2efab7fff7ff7f7feffffffffff7fffffbfffdffffd7ffff * 2 ^ 240 +
  0xfff5b3bf77f777fef377bdf6fb5dff5dfe977c3a7ff6ebefabbffaf3fdff * 2 ^ 480 +
  0x90ed9418d4a13fd6b93f3868deeee66da4236af7ee7f9ede98b7e7fb5ffb * 2 ^ 720 +
  0x22679857 * 2 ^ 960

@[expose]
def bits065row1 : ℕ :=
  0xfafffefffffefffffdffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbfdff3df9ddeebfdfedfefffffbfbfebfe5fff9f7ffe67fff * 2 ^ 240 +
  0xbb237bd3ffedf5b7a6eb8bdbddc4bed33fdbdb8dfbe8ccf9fd7fd7357b9d * 2 ^ 480 +
  0x8be8ebfc4032f4e28eec9bb22beb9ab46d07775bdfebdcc910bfcdf591fa * 2 ^ 720 +
  0x42a299b * 2 ^ 960

@[expose]
def bits065row2 : ℕ :=
  0xdf3fffffffeffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbfff7b7f7fefdffffffefddfefef6fff9fff77feffbfffffffffdffbff * 2 ^ 240 +
  0xff6b8fdff5d3de7e3b77bef9beff7ffae8df7779eff2d7adafaadfe77ff9 * 2 ^ 480 +
  0x3fed920ad9b13dd55dfd3eefe275e769abc8ac50e27f8d9cb1ffd5acbbfa * 2 ^ 720 +
  0x112f4b61 * 2 ^ 960

@[expose]
def bits065row3 : ℕ :=
  0xeffbffaffefff77ffffffeffffffffbffffffffffffffeffffffffffffff * 2 ^ 0 +
  0xefe6bffeadff7ff77d6fffedf6efdf7bbfefffffbfffdfffff77fed5ffff * 2 ^ 240 +
  0x7e7a9bbd7c33cebc71d7ffa5937f76f9e378e2ff5bf3d40f8b5ff89d7fb6 * 2 ^ 480 +
  0x4a572703ea5d3d4c06b8c625d5e84357ba908e3b8f4aecf747dbcd88efde * 2 ^ 720 +
  0x8d92e03 * 2 ^ 960

@[expose]
def bits065 : Vector ℕ 4 := #v[bits065row0, bits065row1, bits065row2, bits065row3]

@[expose]
def bits066row0 : ℕ :=
  0xfbffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefbfff7dbebd2efab7fff7ffff7feffffffffff7fffffbfffdffffd7ffff * 2 ^ 240 +
  0xfff5b3bf77f777fef777bdf6fb5dff5dfe97fc3a7ff6ebefabbffaf3fdff * 2 ^ 480 +
  0x90ed9418d4a13fd6b93f3868deeee76da4236af7ef7f9efe98b7e7fb5ffb * 2 ^ 720 +
  0x2267985f * 2 ^ 960

@[expose]
def bits066row1 : ℕ :=
  0xfefffefffffefffffdffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbfdff3df9ddeebfdfedfefffffbfbfebff7fff9ffffe67fff * 2 ^ 240 +
  0xbb237bd3ffedf5b7a6ef8bfbddc4bed33fdbdbadfbe8ccfbfd7fd7377b9d * 2 ^ 480 +
  0x8be8ebfc4032f4e28eec9bb22bef9ab46d07777bdfebdcc910bfcdf591fa * 2 ^ 720 +
  0x42a299b * 2 ^ 960

@[expose]
def bits066row2 : ℕ :=
  0xdf3ffffffffffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbfff7b7f7fefdffffffefddfefef6fff9fff77feffbfffffffffdffbff * 2 ^ 240 +
  0xff6b8fdff5d3defe3b77bef9beff7ffae9df7779eff6d7adafaadfe77ff9 * 2 ^ 480 +
  0xbfed920ad9b13dd55dfd3eefe2fde769abc8ac50e27f8d9cb1ffd5acbbfa * 2 ^ 720 +
  0x192f4b61 * 2 ^ 960

@[expose]
def bits066row3 : ℕ :=
  0xeffbffbffefff77ffffffeffffffffbffffffffffffffeffffffffffffff * 2 ^ 0 +
  0xefe6bffeadff7ff77d6fffedf6efdf7bbfefffffbfffdfffff77fed5ffff * 2 ^ 240 +
  0x7e7a9bbd7c33cebc71d7ffa5937f76f9e378e2ff5ff3d40f8b5ff89d7fb6 * 2 ^ 480 +
  0x4e572703ea5d3d4c06b8c625d5e84357ba908e3b8f4becf747dbcd88efde * 2 ^ 720 +
  0x8d93e43 * 2 ^ 960

@[expose]
def bits066 : Vector ℕ 4 := #v[bits066row0, bits066row1, bits066row2, bits066row3]

@[expose]
def bits067row0 : ℕ :=
  0xfbffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefbfff7dbebd2efab7fff7ffff7feffffffffff7fffffbfffdffffd7ffff * 2 ^ 240 +
  0xfff5b3bf77f777fef777bdf6fb5dff5dfe97fc3a7ff6ebefabbffaf3fdff * 2 ^ 480 +
  0x90ed9418d4a13fd6b93f3868deeee76da4236af7ef7f9efe98b7e7fb5ffb * 2 ^ 720 +
  0x2267985f * 2 ^ 960

@[expose]
def bits067row1 : ℕ :=
  0xfefffefffffefffffdffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbfdff3df9ddeebfdfedfefffffbfbfebff7fff9ffffe67fff * 2 ^ 240 +
  0xbb237bd3ffedf5b7a6ef8bfbddc4bed33fdbdbadfbe8ccfbfd7fd7377b9d * 2 ^ 480 +
  0x8be8ebfc4032f4e29eec9bb22bef9ab46d07777bdfebdcc910bfcdf591fa * 2 ^ 720 +
  0x242a299b * 2 ^ 960

@[expose]
def bits067row2 : ℕ :=
  0xffbffffffffffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbffffb7ffffffffffffefddfefef6fffbfff77feffffffffffffdffbff * 2 ^ 240 +
  0xff6b9fdff5d3defe3b77bff9beff7ffae9df777deff7d7efafaedfef7ffd * 2 ^ 480 +
  0xbfed920ad9b13dd55ffd3eefe2fde769abc8ac52f27f8d9cb1ffd5acfbfe * 2 ^ 720 +
  0x196f4b65 * 2 ^ 960

@[expose]
def bits067row3 : ℕ :=
  0xeffbffbffefff77ffffffeffffffffbffffffffffffffeffffffffffffff * 2 ^ 0 +
  0xefe6bffeadff7ff77d6ffffdf6efdf7bffefffffbfffdfffff77fed5ffff * 2 ^ 240 +
  0x7efa9bbdfc33cebc71d7ffa593ff76f9e378e2ff5ff3d40f8b5ff89d7fb6 * 2 ^ 480 +
  0x4e572703ea5d3d4c06bcc625d5e84357ba908e3b8f4becf747dbcd88efde * 2 ^ 720 +
  0x8d93e43 * 2 ^ 960

@[expose]
def bits067 : Vector ℕ 4 := #v[bits067row0, bits067row1, bits067row2, bits067row3]

@[expose]
def bits068row0 : ℕ :=
  0xfbffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefbfff7dbebd2efab7fff7ffff7ffffffffffff7fffffbfffdffffd7ffff * 2 ^ 240 +
  0xfff5b3bff7f777fef777bdf6fb5dff5dfed7fc3b7ff7efefabbffaf3fdff * 2 ^ 480 +
  0x90ed9618dca13fd6b93f3868deefe76da6236af7ef7f9efe9ab7e7fb5ffb * 2 ^ 720 +
  0x2a67985f * 2 ^ 960

@[expose]
def bits068row1 : ℕ :=
  0xfefffffffffefffffdffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbfdff3dfbddeebfdfedfefffffbfbfebff7fff9ffffe67fff * 2 ^ 240 +
  0xbb237bd3ffedf5b7a6efabfbddc5bef33fdbdbadfbe8ccfbfd7fd7b77f9d * 2 ^ 480 +
  0x8be8ebfc4032f4e29eec9bb22bef9ab46d07777bdfebdcc910bfcdf599fa * 2 ^ 720 +
  0x242b29bb * 2 ^ 960

@[expose]
def bits068row2 : ℕ :=
  0xffbffffffffffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbffffb7ffffffffffffefddfefef6fffbfff77feffffffffffffdffbff * 2 ^ 240 +
  0xff6b9fdff5d3defe3b77bff9beff7ffae9df777deff7d7efafaedfef7ffd * 2 ^ 480 +
  0xbffd920ad9b13dd55ffd3eefe2fde769abc8ac52f27f8d9cb1ffd5acfbfe * 2 ^ 720 +
  0x196f4b65 * 2 ^ 960

@[expose]
def bits068row3 : ℕ :=
  0xeffbffbffefff77ffffffeffffffffbffffffffffffffeffffffffffffff * 2 ^ 0 +
  0xefe6bffebdff7ff77d6ffffdf6efdf7bffefffffbfffdfffff77fed5ffff * 2 ^ 240 +
  0x7efa9fbdfc33cebc71d7ffa793ff76f9eb7ce2ff5ff3d60f8b7ff89d7fb6 * 2 ^ 480 +
  0x4e57a703ea5d3d4c06bcc625d5e94357ba908e3b8f4becf747dbcd88efde * 2 ^ 720 +
  0x8d93e43 * 2 ^ 960

@[expose]
def bits068 : Vector ℕ 4 := #v[bits068row0, bits068row1, bits068row2, bits068row3]

@[expose]
def bits069row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefbfff7fbebd2efab7fff7fffffffffffffffff7fffffbfffdffffd7ffff * 2 ^ 240 +
  0xfff5b7bffff777fef777bdf6fb5dff5ffed7fc3b7fffefefabbffefbffff * 2 ^ 480 +
  0x91ed9718dca1bfd7b93f3868dfefe76da6236af7ef7f9ffe9ab7e7fb5ffb * 2 ^ 720 +
  0x2a67dc5f * 2 ^ 960

@[expose]
def bits069row1 : ℕ :=
  0xfefffffffffefffffdffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbffff3dfbddeebfdfedfefffffbfbfebff7fff9ffffe67fff * 2 ^ 240 +
  0xbb237bd3ffedf5b7a6efabfbddc5bef37fdbdbbdfbf8ccfbfd7fd7b77f9d * 2 ^ 480 +
  0x8bf8ebfc4032f4e29eec9bb22bef9ab46d07f77bffebdcc910bfcdf599fa * 2 ^ 720 +
  0x242b29bb * 2 ^ 960

@[expose]
def bits069row2 : ℕ :=
  0xffbffffffffffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbffffb7ffffffffffffefddfefef6fffbfff77feffffffffffffdffbff * 2 ^ 240 +
  0xff6b9fdff5d3defe3b77bff9beff7ffae9df777deff7d7efafaedfef7ffd * 2 ^ 480 +
  0xbffd920ad9b13dd55ffd3eefe2fde769abc8ac52f27f8d9cb1ffd5acfbfe * 2 ^ 720 +
  0x196f4b65 * 2 ^ 960

@[expose]
def bits069row3 : ℕ :=
  0xeffbffbffeffff7ffffffeffffffffbffffffffffffffeffffffffffffff * 2 ^ 0 +
  0xefe6bffebdff7fff7d7ffffdf6efdf7bffefffffbfffffffff77fed7ffff * 2 ^ 240 +
  0x7efa9fbdfc33cebc71d7ffa793ff76f9eb7ce2ff5ff3d60f8b7ff89d7fb6 * 2 ^ 480 +
  0x4e57a703ea5d3d4c06bcc625d5e94357ba908e3b8f4becf747dbcd8cffde * 2 ^ 720 +
  0x8d93e43 * 2 ^ 960

@[expose]
def bits069 : Vector ℕ 4 := #v[bits069row0, bits069row1, bits069row2, bits069row3]

@[expose]
def bits070row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefbfff7fbebdaefab7fff7fffffffffffffffff7fffffbfffdffffd7ffff * 2 ^ 240 +
  0xfff5b7bffff777fef777bdf6fbddff5ffed7fc3bffffefefabbffefbffff * 2 ^ 480 +
  0x91ed9718dca1bfd7bf3f3ce8dfefe76da7236af7ef7fdffe9ab7e7fb7ffb * 2 ^ 720 +
  0x2a67dc5f * 2 ^ 960

@[expose]
def bits070row1 : ℕ :=
  0xfefffffffffefffffdffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbffff3dfbddeebfdfedfefffffbfbfebff7fff9ffffe67fff * 2 ^ 240 +
  0xbb237bd3ffedf5b7a6efabfbddc5bef37fdbdbbdfbf8ccfbfd7fd7b77f9d * 2 ^ 480 +
  0x8bf8ebfc4032f4e29eec9bb22bef9ab46d07f77bffebdcc910bfcdf599fa * 2 ^ 720 +
  0x242b29bb * 2 ^ 960

@[expose]
def bits070row2 : ℕ :=
  0xffbffffffffffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbffffb7ffffffffffffefddfefef6fffbfff77feffffffffffffdffbff * 2 ^ 240 +
  0xff6b9fdff5d3defe3b77bff9beff7ffae9df777deff7d7efafaedfef7ffd * 2 ^ 480 +
  0xbffd920ad9b13dd55ffd3eefe2fde769abc8ac52f27f8d9cb1ffd5acfbfe * 2 ^ 720 +
  0x196f4b65 * 2 ^ 960

@[expose]
def bits070row3 : ℕ :=
  0xeffbffbffeffff7ffffffeffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefeefffebdff7fff7d7ffffdf6efff7fffefffffbffffffffff7fed7ffff * 2 ^ 240 +
  0x7efa9fbdfc33cfbc71d7ffa793ff7ef9fb7ce2ff5ff3d68f8bfff89d7fbf * 2 ^ 480 +
  0x4e57e70bea5d3d4c06bcc625d7e9435fba90ae3b8f4becf747dbcd8cffff * 2 ^ 720 +
  0x8f93e43 * 2 ^ 960

@[expose]
def bits070 : Vector ℕ 4 := #v[bits070row0, bits070row1, bits070row2, bits070row3]

@[expose]
def bits071row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefbfff7fbebdaefab7fff7fffffffffffffffff7fffffbfffdffffd7ffff * 2 ^ 240 +
  0xfff5b7bffff777fef777bdf6fbddff5ffed7fc3bffffefefabbffefbffff * 2 ^ 480 +
  0x91ed9718dca1bfd7bf3f3ce8dfefe76da7236af7ef7fdffe9ab7e7fb7ffb * 2 ^ 720 +
  0x2a67dc5f * 2 ^ 960

@[expose]
def bits071row1 : ℕ :=
  0xfefffffffffefffffdffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbffff3ffbddeebfdfedfefffffbfbfebff7fff9ffffe67fff * 2 ^ 240 +
  0xbb237bd3ffedf5b7a6ffabfbddc5bef37fdbdfbdfbf8ecfbfd7fd7b77f9d * 2 ^ 480 +
  0x8bf8ebfc4033f4e29eec9bb22bef9ab46d07ff7bffebdcc910bfcdf599fa * 2 ^ 720 +
  0x242b29bb * 2 ^ 960

@[expose]
def bits071row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbffffb7ffffffffffffeffffefef6fffbfff77feffffffffffffdffbff * 2 ^ 240 +
  0xff6f9ffff5d7defe3b77bff9beff7ffaf9df777feff7d7efafaedfff7ffd * 2 ^ 480 +
  0xbffd920ad9b13dd55ffd3eeff2ffe769abc8aedaf77f9d9cb1ffd5bdfbff * 2 ^ 720 +
  0x196f4b65 * 2 ^ 960

@[expose]
def bits071row3 : ℕ :=
  0xeffbffbffeffff7ffffffeffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefeefffebdff7fff7d7ffffdf6efff7fffefffffbffffffffff7fed7ffff * 2 ^ 240 +
  0x7efa9fbdfc33cfbc71d7ffa793ff7ef9fb7ce2ff5ff3d68f8bfffa9dffbf * 2 ^ 480 +
  0xce57e70bea5d3d4c06bcc625d7e9635fba90ae3b8f4becf747dbed8cffff * 2 ^ 720 +
  0x8f93e47 * 2 ^ 960

@[expose]
def bits071 : Vector ℕ 4 := #v[bits071row0, bits071row1, bits071row2, bits071row3]

@[expose]
def bits072row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefbfff7fbebdaefab7fff7fffffffffffffffff7fffffbfffdffffd7ffff * 2 ^ 240 +
  0xfff5f7bffff777fef777bdf6fbfdff5ffed7fc3bffffefefabbffefbffff * 2 ^ 480 +
  0x91ed9718dca1bfd7bf3f3ce8dfefe76da7236af7ef7fdffe9ab7e7fb7ffb * 2 ^ 720 +
  0x2a67dc5f * 2 ^ 960

@[expose]
def bits072row1 : ℕ :=
  0xfefffffffffefffffdffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbffff3ffbddeebfdfedfefffffbfbfebff7fff9ffffe67fff * 2 ^ 240 +
  0xbb237bd3ffedf5b7a6ffabfbddc5bef37fdbdfbdfbf8ecfbfd7fd7b77f9d * 2 ^ 480 +
  0x8bf8ebfc4033f4e29eec9bb22bef9ab46d07ff7bffebdcc910bfcdf599fa * 2 ^ 720 +
  0x242b29bb * 2 ^ 960

@[expose]
def bits072row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbffffb7ffffffffffffeffffefef6fffbfff77feffffffffffffdffbff * 2 ^ 240 +
  0xff6fdffff5d7deffbb7fbffbfeff7ffaf9df777feff7d7efffaedfff7ffd * 2 ^ 480 +
  0xbffdf21ad9b13dd55fff3feff2fff769abc8aedaf77f9d9cb1ffd5bdfbff * 2 ^ 720 +
  0x196f4b65 * 2 ^ 960

@[expose]
def bits072row3 : ℕ :=
  0xeffbffbffeffff7ffffffeffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffeefffebdff7fff7d7fffffffffff7fffefffffbffffffffff7fed7ffff * 2 ^ 240 +
  0xfefadfbdfc33cfbc71dfffa793ff7ef9ff7ce2ff5ff3df8fcbfffa9dffbf * 2 ^ 480 +
  0xce57e70bea5d3d4c06bcc625f7e9e35fba90ae3bcf4becf747dbedccffff * 2 ^ 720 +
  0x8f93e47 * 2 ^ 960

@[expose]
def bits072 : Vector ℕ 4 := #v[bits072row0, bits072row1, bits072row2, bits072row3]

@[expose]
def bits073row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefbfff7fbebdaefab7fff7fffffffffffffffff7fffffbfffdffffd7ffff * 2 ^ 240 +
  0xfff5f7bffff777fef777bdf6fbfdff5ffed7fc3bffffefefabbffefbffff * 2 ^ 480 +
  0x91ed9718dca1bfd7bf3f3ce8dfefe76da7236af7ef7fdffe9ab7e7fb7ffb * 2 ^ 720 +
  0x2a67dc5f * 2 ^ 960

@[expose]
def bits073row1 : ℕ :=
  0xfefffffffffefffffdffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbffff3ffbddeebfdfedfefffffbfbfebff7fff9ffffe67fff * 2 ^ 240 +
  0xbb237bd3ffedf5b7a6ffabfbddc5bef37fdbdfbdfbf8ecfbfd7fd7b77f9d * 2 ^ 480 +
  0x8bf8ebfc4033f4e29eec9bb22bef9ab46d07ff7bffebdcc910bfcdf599fa * 2 ^ 720 +
  0x242b29bb * 2 ^ 960

@[expose]
def bits073row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbffffb7ffffffffffffeffffefef6fffbfff77feffffffffffffdffbff * 2 ^ 240 +
  0xff6fdffff5d7deffbb7fbffbfeff7ffaf9df777feff7d7efffaedfff7ffd * 2 ^ 480 +
  0xbffdf21ad9b13dd55fff3feff2fff769abc8aedaf77f9d9cb1ffd5bdfbff * 2 ^ 720 +
  0x196f4b65 * 2 ^ 960

@[expose]
def bits073row3 : ℕ :=
  0xeffbffbfffffff7fffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfffffffebdffffff7dffffffffffffffffeffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffadfbffc33effc71dfffb793ff7efbff7ce6ffdff3df8fcffffa9fffbf * 2 ^ 480 +
  0xcf5fe70bea5d3d4c16bcc625f7ebe35fba90bf7bef4bfcf747fbedccffff * 2 ^ 720 +
  0x8fb3ec7 * 2 ^ 960

@[expose]
def bits073 : Vector ℕ 4 := #v[bits073row0, bits073row1, bits073row2, bits073row3]

@[expose]
def bits074row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbfffffbefdbefab7fff7fffffffffffffffff7fffffbffffffffd7ffff * 2 ^ 240 +
  0xfff5f7fffff777fef777bdf6fbfdff5ffed7fc3fffffefefabbffffbffff * 2 ^ 480 +
  0x93ed9718dca1ffd7bf3f3ee8dfefe76de7237af7efffdffe9ab7e7fb7fff * 2 ^ 720 +
  0x2a67dc5f * 2 ^ 960

@[expose]
def bits074row1 : ℕ :=
  0xfefffffffffefffffdffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbffff3ffbddeebfdfedfefffffbfbfebff7fff9ffffe67fff * 2 ^ 240 +
  0xbb237bd3ffedf5b7a6ffabfbddc5bef37fdbdfbdfbf8ecfbfd7fd7b77f9d * 2 ^ 480 +
  0x8bf8ebfc4033f4e29eec9bb22bef9ab46d07ff7bffebdcc910bfcdf599fa * 2 ^ 720 +
  0x242b29bb * 2 ^ 960

@[expose]
def bits074row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbffffb7ffffffffffffeffffefef6fffbfff77feffffffffffffdffbff * 2 ^ 240 +
  0xff6fdffff5d7deffbb7fbffbfeff7ffaf9df777feff7d7efffaedfff7ffd * 2 ^ 480 +
  0xbffdf21ad9b13dd55fff3feff2fff769abc8aedaf77f9d9cb1ffd5bdfbff * 2 ^ 720 +
  0x196f4b65 * 2 ^ 960

@[expose]
def bits074row3 : ℕ :=
  0xffffffbfffffff7fffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfffffffebdffffff7dffffffffffffffffeffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffadfbffcb3effc75dfffb7b3ff7efbff7cf6ffdff3df8fdffffa9fffff * 2 ^ 480 +
  0xcf7fe70bea5d3d4c16bcc6a5f7fbe37fba92bf7bef4ffdff47fbfdccffff * 2 ^ 720 +
  0x8fb3ec7 * 2 ^ 960

@[expose]
def bits074 : Vector ℕ 4 := #v[bits074row0, bits074row1, bits074row2, bits074row3]

@[expose]
def bits075row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbfffffbefdbefaf7fffffffffffffffffffff7fffffbffffffffd7ffff * 2 ^ 240 +
  0xfff5f7fffff777fef7f7bdf6fbfdff5ffed7fcbfffffffefabffffffffff * 2 ^ 480 +
  0x93ed9719dca1ffd7bfbf3ee8dfefe76ff7a37af7efffdffe9ab7e7fb7fff * 2 ^ 720 +
  0x2a67dc5f * 2 ^ 960

@[expose]
def bits075row1 : ℕ :=
  0xfeffffffffffffffffffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfedb894fbffff3ffbddeebfdffdfefffffbfbfebff7fff9fffff67fff * 2 ^ 240 +
  0xbb237bd3ffedf5b7a6ffabfbddc5bef37fdbdfbdfbf8edfbfd7fd7b77f9d * 2 ^ 480 +
  0x8bf8ebfc4033f4e29eec9bb22bef9ab46d07ff7bffebdcc910bfcdf59bfa * 2 ^ 720 +
  0x242b29bb * 2 ^ 960

@[expose]
def bits075row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbffffb7ffffffffffffeffffefef6fffbfff77feffffffffffffdffbff * 2 ^ 240 +
  0xff6fdffff5d7deffbb7fbffbfeff7ffaf9df777feff7d7efffaedfff7ffd * 2 ^ 480 +
  0xbffdf21ad9b13dd55fff3feff2fff769abc8aedaf77f9d9cb1ffd5bdfbff * 2 ^ 720 +
  0x196f4b65 * 2 ^ 960

@[expose]
def bits075row3 : ℕ :=
  0xffffffbfffffff7fffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbdffffff7dffffffffffffffffeffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffadfbffcb7effc75dfffb7b7ff7efbfffdf6fffff7df9fdffffa9fffff * 2 ^ 480 +
  0xcf7fe71beadd3d6c16bcc6a5f7fbe37fbab2bf7befcffdff47fbfdccffff * 2 ^ 720 +
  0x8fb3ec7 * 2 ^ 960

@[expose]
def bits075 : Vector ℕ 4 := #v[bits075row0, bits075row1, bits075row2, bits075row3]

@[expose]
def bits076row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbfffffbefdbefaf7fffffffffffffffffffff7fffffbffffffffd7ffff * 2 ^ 240 +
  0xfff5f7fffff7f7fff7f7bdf6fffdff7ffed7fcbfffffffffabffffffffff * 2 ^ 480 +
  0x93ed975bdca1ffd7bfffbee8dfffe76ff7a37af7efffdffe9ab7e7fb7fff * 2 ^ 720 +
  0x2a67dc5f * 2 ^ 960

@[expose]
def bits076row1 : ℕ :=
  0xfeffffffffffffffffffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfedba94fbffffbffbdfeebfdffffefffffbfbfebffffff9fffff6ffff * 2 ^ 240 +
  0xbf237fd3ffeff5b7a6ffaffbddc5bef37fdbdfbdfbf8edfbfd7fdfb77f9f * 2 ^ 480 +
  0x8bf9ebfc6833f4e29eec9bb22beffaf46d07ff7bffebdccd10ffcdf59bfa * 2 ^ 720 +
  0x252b29fb * 2 ^ 960

@[expose]
def bits076row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbffffb7ffffffffffffeffffefef6fffbfff77feffffffffffffdffbff * 2 ^ 240 +
  0xff6fdffff5d7deffbb7fbffbfeff7ffaf9df777feff7d7efffaedfff7ffd * 2 ^ 480 +
  0xbffdf21ad9b13dd55fff3feff2fff769abc8aedaf77f9d9cb1ffd5bdfbff * 2 ^ 720 +
  0x196f4b65 * 2 ^ 960

@[expose]
def bits076row3 : ℕ :=
  0xffffffbfffffff7fffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbdffffff7dffffffffffffffffeffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffadfbffcb7effc75dfffb7b7ff7efbfffdf6fffff7df9fdffffa9fffff * 2 ^ 480 +
  0xcf7fe71beadd3d6c16bcc6a5f7fbe37fbab2bf7befcffdff47fbfdccffff * 2 ^ 720 +
  0x8fb3ec7 * 2 ^ 960

@[expose]
def bits076 : Vector ℕ 4 := #v[bits076row0, bits076row1, bits076row2, bits076row3]

@[expose]
def bits077row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbfffffbeffbefaf7fffffffffffffffffffff7fffffbffffffffd7ffff * 2 ^ 240 +
  0xfff5f7fffff7f7fff7f7bdf6fffdff7ffed7fdbfffffffffabffffffffff * 2 ^ 480 +
  0x93edb77bdca1ffdfbfffbee8dfffe7eff7a37af7ffffdffe9eb7e7ff7fff * 2 ^ 720 +
  0x2e67dc5f * 2 ^ 960

@[expose]
def bits077row1 : ℕ :=
  0xfeffffffffffffffffffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfedba94fbffffbffbdfeebfdffffefffffbfbfebffffff9fffff6ffff * 2 ^ 240 +
  0xbf237fd3ffeff5b7a6ffaffbddc5bef37fdbdfbdfbf8edfbfd7fdfb77f9f * 2 ^ 480 +
  0x8bf9ebfc6833f4e29eec9bb22beffaf46d07ff7bffebdccd10ffcdf59bfa * 2 ^ 720 +
  0x252b29fb * 2 ^ 960

@[expose]
def bits077row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbffffb7ffffffffffffeffffefef6fffbfff77feffffffffffffdffbff * 2 ^ 240 +
  0xff6fdffff5d7deffbb7fbffbfeff7ffaf9df777feff7d7efffaedfff7ffd * 2 ^ 480 +
  0xbffdf21ad9b13dd55fff3feff2fff769abc8aedaf77f9d9cb1ffd5bdfbff * 2 ^ 720 +
  0x196f4b65 * 2 ^ 960

@[expose]
def bits077row3 : ℕ :=
  0xffffffbfffffff7fffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbdffffff7dfffffffffffffffffffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffadffffcb7effd75dfffb7b7ff7efbfffdf7fffff7df9fdffffabfffff * 2 ^ 480 +
  0xdf7fe71bfadd7d7d16bcd6a7f7fbf3fffab2bf7befdffdff77fbffecffff * 2 ^ 720 +
  0x28ff3ec7 * 2 ^ 960

@[expose]
def bits077 : Vector ℕ 4 := #v[bits077row0, bits077row1, bits077row2, bits077row3]

@[expose]
def bits078row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbfffffbeffbefaf7fffffffffffffffffffff7fffffbffffffffd7ffff * 2 ^ 240 +
  0xfff5f7fffff7f7fff7f7bdf6fffdff7ffed7fdbfffffffffabffffffffff * 2 ^ 480 +
  0x93edb77bdca1ffdfbfffbee8dfffe7eff7a37af7ffffdffe9eb7e7ff7fff * 2 ^ 720 +
  0x2e67dc5f * 2 ^ 960

@[expose]
def bits078row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xffdfedba97fbfffffffbdfeebffffffefffffbfbffbffffffbfffff6ffff * 2 ^ 240 +
  0xbf237fd3ffeff5bfe6ffbffbffc5bef77fdbffbdfbf8edfbfd7fdfb77f9f * 2 ^ 480 +
  0x8bf9ebfc6833f6ea9eecbbb22feffaf46d07ff7fffebdccd10ffcdfddbfa * 2 ^ 720 +
  0x252b29fb * 2 ^ 960

@[expose]
def bits078row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbffffb7ffffffffffffeffffefef6fffbfff77feffffffffffffdffbff * 2 ^ 240 +
  0xff6fdffff5d7deffbb7fbffbfeff7ffafbdf777feff7d7efffaedfff7ffd * 2 ^ 480 +
  0xfffdf21ad9b13dd55fff7feff2fff769abc8aedaf77f9d9cb1ffd5bdfbff * 2 ^ 720 +
  0x196f6b65 * 2 ^ 960

@[expose]
def bits078row3 : ℕ :=
  0xffffffbfffffff7fffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbdffffff7dfffffffffffffffffffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffadffffcb7effd75ffffb7b7ff7efbfffdf7fffff7df9fdffffabfffff * 2 ^ 480 +
  0xdf7fe71bfadd7d7d1ebdd6a7f7fbf3fffaf2ff7befdffdff77fbffecffff * 2 ^ 720 +
  0x28ff3ee7 * 2 ^ 960

@[expose]
def bits078 : Vector ℕ 4 := #v[bits078row0, bits078row1, bits078row2, bits078row3]

@[expose]
def bits079row0 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbfffffbeffbefaf7fffffffffffffffffffff7fffffbffffffffd7ffff * 2 ^ 240 +
  0xfff5f7fffff7f7fff7f7bdf6fffdff7ffed7fdbfffffffffabffffffffff * 2 ^ 480 +
  0x93edb77bdca1ffdfbfffbee8dfffe7eff7a37af7ffffdffe9eb7e7ff7fff * 2 ^ 720 +
  0x2e67dc5f * 2 ^ 960

@[expose]
def bits079row1 : ℕ :=
  0xffffffffffffffffffffffffffffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffedba97fbfffffffbdfeebffffffefffffbfbffbffffffbfffff6ffff * 2 ^ 240 +
  0xbf237fd3ffeff5bfe7ffbffbffcdbef77fdbffbffff8edfbff7fffbf7f9f * 2 ^ 480 +
  0x8bf9ebfe6873f6ea9eecbbb2bfeffaf4ed07ff7fffebdecd10ffefffdbfe * 2 ^ 720 +
  0x252b29fb * 2 ^ 960

@[expose]
def bits079row2 : ℕ :=
  0xffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffbffffb7ffffffffffffeffffefff6fffbfff77feffffffffffffdfffff * 2 ^ 240 +
  0xff6ffffff7d7deffbb7fbffbfeff7ffbfbff777feff7d7efffafdfff7ffd * 2 ^ 480 +
  0xfffdf21ad9b13dd55fff7feff2fff7e9bbc8afdaf77f9ddcb1ffd5bdfbff * 2 ^ 720 +
  0x196f6b65 * 2 ^ 960

@[expose]
def bits079row3 : ℕ :=
  0xffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xffffffffbfffffff7dfffffffffffffffffffffffffffffffff7fff7ffff * 2 ^ 240 +
  0xfffadffffcb7effd75ffffb7b7ff7efbfffdf7fffff7df9fdffffabfffff * 2 ^ 480 +
  0xdf7fe71bfadd7d7d1ebdd6a7f7fbf3fffaf2ff7befdffdff77fbffecffff * 2 ^ 720 +
  0x28ff3ee7 * 2 ^ 960

@[expose]
def bits079 : Vector ℕ 4 := #v[bits079row0, bits079row1, bits079row2, bits079row3]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
