/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.TableBits

/-!
# M11 coset certificate: Bits3

Literal checkpoints: four natural-number masks at each stage.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def bits048row0 : ℕ :=
  0x3bfffffedefd9fffffdfdfffff3fffffffeffffffdffffffffffffffffff * 2 ^ 0 +
  0xa7bf8d6d9aad2abab2b7d3f62d5da5fff6fffef7f75afbb6fdf9ff57ffff * 2 ^ 240 +
  0x21d4222a73f673da22271c76f35ca655f6835c2a5766abefa9b7faa3b5be * 2 ^ 480 +
  0x90e11418d4203702b91720685a8a842c802348b60e321ac69837e2734df9 * 2 ^ 720 +
  0x22469014 * 2 ^ 960

@[expose]
def bits048row1 : ℕ :=
  0xfa7ff2fbfff4bfbffdffffff5bffef7fddf7ff7f7ffffefff9ffffffffff * 2 ^ 0 +
  0xfd5eacb8901bfdfe3d91ddae3edfeddcefff2afbbe9ee5bfd9f6a7e67fef * 2 ^ 240 +
  0x33035353df697597a6a9095b5d443e913f9bdb8d3bc8c8d9fd6fd531398d * 2 ^ 480 +
  0x89e0e9e44032e4a28ee09b922b4b18b44d07735bdd88ccc010bfc5a510da * 2 ^ 720 +
  0x420299a * 2 ^ 960

@[expose]
def bits048row2 : ℕ :=
  0x9f0ffbfd7f6fefff5b7ef7fffffffffffffdffffffffbfffffffffffffff * 2 ^ 0 +
  0xf4b353787f5feb9dabf774ddcfe7cb6ffb1f3777b4ffbefa6ffff35dc9f7 * 2 ^ 240 +
  0xb66b87dff5d2ce660b73acd918f55b5aa8df6659ce72d7ad2fa2df672859 * 2 ^ 480 +
  0x374d920089b1301544d42eaca235e1212bc88400a2158d98a17355203a9a * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits048row3 : ℕ :=
  0xeffaed8dbe3ff75ffff6feffff9fffbf7ffffbfffefffefff5fffffbffff * 2 ^ 0 +
  0xaf46aff6adff7df75d6c7bedd68fde7a3fe7ffffbfdfcfff6b37cad5f7fd * 2 ^ 240 +
  0x7e329abd7c33ce9c71d55f25935f56300378c2f74be3d406815ff81d7b36 * 2 ^ 480 +
  0x4a522503ea5c284c02b8c22544e0435712900e3b854a6cf746534d88ee1e * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits048 : Vector ℕ 4 := #v[bits048row0, bits048row1, bits048row2, bits048row3]

@[expose]
def bits049row0 : ℕ :=
  0x3bfffffedffdbfffffdfdfffff3fffffffeffffffdffffffffffffffffff * 2 ^ 0 +
  0xa7bf8d6d9aad2afab6b7d3f62f5da5fff6fffef7f75afbb6fdf9ff57ffff * 2 ^ 240 +
  0x21d4222a73f673da22271c76f35ca655f6835c2a5766ebefa9b7faa3b5be * 2 ^ 480 +
  0x90e11418d4203702b91720685e8a842c802348b64e321ac69837e2734df9 * 2 ^ 720 +
  0x22469014 * 2 ^ 960

@[expose]
def bits049row1 : ℕ :=
  0xfa7ff2fbfff4bfbffdffffff5bffef7fddf7ff7ffffffefffdffffffffff * 2 ^ 0 +
  0xfd5eacb8901bfdfe3d91ddaebedfedfcefff2afbbe9ee5bfd9f7a7e67fff * 2 ^ 240 +
  0x33035353df697597a6a9095b5d443e913f9bdb8d7bc8c8d9fd6fd531398d * 2 ^ 480 +
  0x89e0e9e44032e4e28ee89b922b4b18b44d07735bdd88ccc010bfc5a510da * 2 ^ 720 +
  0x420299a * 2 ^ 960

@[expose]
def bits049row2 : ℕ :=
  0x9f0ffbfd7f6fefff7b7ef7ffffffffffffffffffffffbfffffffffffffff * 2 ^ 0 +
  0xf4b35b787f5feb9dabf774ddcfe7cb6ffb1f3777b4ffbefa6ffff3ddd9f7 * 2 ^ 240 +
  0xf66b87dff5d2ce660b73acd918f55bdaa8df6659ce72d7ad2fa2df672859 * 2 ^ 480 +
  0x374d920089b1301544d42eaca235e1212bc88400a2158d98a1f355203a9a * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits049row3 : ℕ :=
  0xeffafd8dbebff75ffff6feffff9fffbf7ffffbfffefffefff5fffffbffff * 2 ^ 0 +
  0xaf46aff6adff7df75d6c7bedd68fde7a3fe7ffffbfdfcfff7b37cad5f7ff * 2 ^ 240 +
  0x7e329abd7c33ce9c71d55fa5935f56300378c2f74be3d406815ff81d7bb6 * 2 ^ 480 +
  0x4a522503ea5c284c02b8c62544e0435712900e3b854a6cf746534d88ee1e * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits049 : Vector ℕ 4 := #v[bits049row0, bits049row1, bits049row2, bits049row3]

@[expose]
def bits050row0 : ℕ :=
  0x3bffffffdffdbfffffdfdfffff3fffffffeffffffdffffffffffffffffff * 2 ^ 0 +
  0xa7bf8d6d9aad2afab6b7d3f62f5fa5fff6fffef7f75afbb6fdfdff57ffff * 2 ^ 240 +
  0x61d4222a73f673de22271c76f35da655f6835c2a5766ebefa9b7faa3b5be * 2 ^ 480 +
  0x90e11418d4203702b91720685e8a842c802348b64e329ac69837e2734df9 * 2 ^ 720 +
  0x22469014 * 2 ^ 960

@[expose]
def bits050row1 : ℕ :=
  0xfa7ff2fbfff6ffbffdffffffdbffefffddf7fffffffffefffdffffffffff * 2 ^ 0 +
  0xfd5eacb8901bfdfe3d91ddaebedfedfcefff3afbbe9ee5bfd9f7b7e67fff * 2 ^ 240 +
  0x3b035353df697597a6a9095b5d443ed13f9bdb8d7bc8c8d9fd6fd531398d * 2 ^ 480 +
  0x89e0ebe44032e4e28ee89b922b4b18b44d07735bdd88ccc010bfcda590da * 2 ^ 720 +
  0x420299a * 2 ^ 960

@[expose]
def bits050row2 : ℕ :=
  0x9f0ffbfd7f6fefff7b7ef7ffffffffffffffffffffffbfffffffffffffff * 2 ^ 0 +
  0xf4b35b787f5feb9dabf774ddcfe7cb6ffb1f3777b4ffbefa6ffff3dfd9f7 * 2 ^ 240 +
  0xf66b87dff5d2ce660b73acd938f55bdaa8df6659cef2d7ad2fa2df672859 * 2 ^ 480 +
  0x374d920089b1341544d42eaca235e1212bc88400a2158d98a1f355203a9a * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits050row3 : ℕ :=
  0xeffbfd8dbebff75ffff6feffff9fffbf7ffffffffffffefff7ffffffffff * 2 ^ 0 +
  0xef46aff6adff7df75d6c7bedd68fde7a3fe7ffffbfdfcfff7b37cad5f7ff * 2 ^ 240 +
  0x7e329abd7c33cebc71d55fa5935f56380378c2f74be3d406815ff81d7bb6 * 2 ^ 480 +
  0x4a522503ea5d284c02b8c62544e0435712900e3b854a6cf746534d88ee1e * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits050 : Vector ℕ 4 := #v[bits050row0, bits050row1, bits050row2, bits050row3]

@[expose]
def bits051row0 : ℕ :=
  0x3bffffffdffdffffffdfdfffff3fffffffefffffffffffffffffffffffff * 2 ^ 0 +
  0xa7bf8d6d9aad2afab6b7d3f62f5fa5fff7fffef7f75efbb6fdffff57ffff * 2 ^ 240 +
  0x69d4222a73f673de22271c76f35da655f6935c2a77e6ebefa9b7faa3b5be * 2 ^ 480 +
  0x90e91418d4203702b91720685e8a842c802348b64e329ec69837e6734df9 * 2 ^ 720 +
  0x22469016 * 2 ^ 960

@[expose]
def bits051row1 : ℕ :=
  0xfa7ffafbfff6ffbffdffffffdbffefffddf7fffffffffefffdffffffffff * 2 ^ 0 +
  0xfd5eacb8901bfdfe3db1ddaebedfedfcefff3afbbe9ee5bfd9f7b7e67fff * 2 ^ 240 +
  0x3b035353df697597a6a9095b5d443ed13f9bdb8d7bc8ccd9fd6fd531398d * 2 ^ 480 +
  0x89e0ebe44032e4e28ee89b922b4b18b44d07735bdd88ccc010bfcda590da * 2 ^ 720 +
  0x420299a * 2 ^ 960

@[expose]
def bits051row2 : ℕ :=
  0x9f0ffbfd7f6fefff7b7ef7ffffffffffffffffffffffbfffffffffffffff * 2 ^ 0 +
  0xf4b35b787f5feb9dabf774ddcfe7cf6ffb1f3777b4ffbefa6ffff7dfd9ff * 2 ^ 240 +
  0xf66b87dff5d3ce660b73acd938f55bdaa8df7659cef2d7ad2fa2df672859 * 2 ^ 480 +
  0x374d920089b1341544d42eaca235e1212bc88400a2158d98a1fb55203a9a * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits051row3 : ℕ :=
  0xeffbfd8dfebff75ffff6feffff9fffbf7ffffffffffffefff7ffffffffff * 2 ^ 0 +
  0xef46aff6adff7df75d6c7bedd6cfde7a3fe7ffffbfdfcfff7b37cad5f7ff * 2 ^ 240 +
  0x7e329abd7c33cebc71d55fa5935f56f80378c2f74be3d406815ff81d7bb6 * 2 ^ 480 +
  0x4a522503ea5d2c4c02b8c62544e0435732900e3b854a6cf746d3cd88ef5e * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits051 : Vector ℕ 4 := #v[bits051row0, bits051row1, bits051row2, bits051row3]

@[expose]
def bits052row0 : ℕ :=
  0x3bffffffdffdffffffdfdfffff3fffffffefffffffffffffffffffffffff * 2 ^ 0 +
  0xa7bf8d6d9ead2afab6b7d3f62f5fa5fff7fffef7f75efbb6fdffff57ffff * 2 ^ 240 +
  0x69d4322a73f673de22271c76f35db655f6935c2a77e6ebefa9b7faa3b5be * 2 ^ 480 +
  0x90e91418d4203702b91720685e8a842c802348b64e329ec69837e6734df9 * 2 ^ 720 +
  0x22469016 * 2 ^ 960

@[expose]
def bits052row1 : ℕ :=
  0xfa7ffafbfff6ffbffdfffffffbffefffddf7fffffffffeffffffffffffff * 2 ^ 0 +
  0xfd5eecb8941bfdfe3db1ddaebedfedfcefff7afbfe9ee5bfd9f7bfe67fff * 2 ^ 240 +
  0x3b235353df697597a6a9095bdd443ed13f9bdb8d7bc8ccd9fd7fd731398d * 2 ^ 480 +
  0x89e0ebf44032e4e28ee89b922b4b98b44d07735bdd8accc010bfcda590da * 2 ^ 720 +
  0x420299a * 2 ^ 960

@[expose]
def bits052row2 : ℕ :=
  0x9f0ffbfd7f6fefff7b7ef7ffffffffffffffffffffffbfffffffffffffff * 2 ^ 0 +
  0xfcb35b787f5feb9dbbf774ddcfe7cf6fff1f3777b4ffbefa6ffff7dfd9ff * 2 ^ 240 +
  0xf66b87dff5d3ce660b73acd938f55bdaa8df7659cef2d7ad2fa2df6728d9 * 2 ^ 480 +
  0x374d920289b1341544dc2eaca235e1612bc88400a2178d98a1fb55203a9a * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits052row3 : ℕ :=
  0xeffbfd8dfebff75ffff6feffff9fffbffffffffffffffefff7ffffffffff * 2 ^ 0 +
  0xef46bff6adff7df75d6c7bedf6cfde7a3fe7ffffbfdfcfff7b37cad5f7ff * 2 ^ 240 +
  0x7e329abd7c33cebc71d55fa5937f56f90378c2f74bf3d406815ff81d7bb6 * 2 ^ 480 +
  0x4a522503ea5d3c4c02b8c62544e0435732900e3b854a6cf746d3cd88ef5e * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits052 : Vector ℕ 4 := #v[bits052row0, bits052row1, bits052row2, bits052row3]

@[expose]
def bits053row0 : ℕ :=
  0xbbffffffdffdffffffdfffffff7fffffffefffffffffffffffffffffffff * 2 ^ 0 +
  0xa7bf8d6d9ead2afab6b7d3f62f5fa5fff7fffff7f75efbb6fdffff57ffff * 2 ^ 240 +
  0x69f4322a73f673de22271c76f35db655f6935c2a77e6ebefa9b7faa3b5be * 2 ^ 480 +
  0x90e91418d4203702b91f20685e8a842c802348b64e739ec69837e6734df9 * 2 ^ 720 +
  0x22469016 * 2 ^ 960

@[expose]
def bits053row1 : ℕ :=
  0xfa7ffafbfff6ffbffdfffffffbffefffddf7fffffffffeffffffffffffff * 2 ^ 0 +
  0xfd5eecb8941bfdfe3db1ddaebedfedfcefff7afbfe9ee5bfd9f7bfe67fff * 2 ^ 240 +
  0x3b235353df697597a6ab095bdd443ed13f9bdb8d7be8ccd9fd7fd731398d * 2 ^ 480 +
  0x89e0ebf44032e4e28ee89b922b4b98b44d07735bdd8accc010bfcda591da * 2 ^ 720 +
  0x420299a * 2 ^ 960

@[expose]
def bits053row2 : ℕ :=
  0x9f1ffbfd7f6ffffffb7ef7ffffffffffffffffffffffbfffffffffffffff * 2 ^ 0 +
  0xfcb35b787f5feb9dfbf774fdcfe7cf6fff1f3777f4ffbeff6ffff7dfd9ff * 2 ^ 240 +
  0xf66b87dff5d3ce660b73acd9b8f57bdaa8df7759cef2d7ad2fa2df6728d9 * 2 ^ 480 +
  0x374d920289b1341544dc3eaca235e3612bc88410a2178d98a1fb55203a9a * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits053row3 : ℕ :=
  0xeffbfd8dfebff75ffffefeffff9fffbffffffffffffffefff7ffffffffff * 2 ^ 0 +
  0xef46bff6adff7df75d6d7bedf6cfde7a3fe7ffffbfdfcfff7b37cad5f7ff * 2 ^ 240 +
  0x7e329abd7c33cebc71d55fa5937f56f90378c2f75bf3d40f815ff81d7bb6 * 2 ^ 480 +
  0x4a522503ea5d3c4c02b8c62544e04357b2900e3b874a6cf746d3cd88ef5e * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits053 : Vector ℕ 4 := #v[bits053row0, bits053row1, bits053row2, bits053row3]

@[expose]
def bits054row0 : ℕ :=
  0xbbffffffdffdffffffdfffffffffffffffefffffffffffffffffffffffff * 2 ^ 0 +
  0xa7bf8d6d9ebd2afab6b7d3f62f5fa5fff7fffff7f75ffbb6fdffff57ffff * 2 ^ 240 +
  0x69f4322b73f673fe22271c76f35db655f6935c2a77e6ebefa9bffaa3b5be * 2 ^ 480 +
  0x90e91418d4203702b91f20685e8a842c802348b74e739ec69837e6734df9 * 2 ^ 720 +
  0x22469016 * 2 ^ 960

@[expose]
def bits054row1 : ℕ :=
  0xfa7ffafffff6ffbffdfffffffbffefffddf7fffffffffeffffffffffffff * 2 ^ 0 +
  0xfddeecb8941bfdfe3db1ddaebedfedfcefff7afbfebee5bfd9f7bfe67fff * 2 ^ 240 +
  0x3b235353df6975b7a6ab095bdd443ed13f9bdb8dfbe8ccd9fd7fd731398d * 2 ^ 480 +
  0x89e8ebf44032e4e28ee89b922b6b9ab44d07735bdd8accc010bfcda591da * 2 ^ 720 +
  0x428299a * 2 ^ 960

@[expose]
def bits054row2 : ℕ :=
  0x9f1ffbfd7f6ffffffb7ef7ffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfcb3db787f5feb9ffbf774fdcfe7cf6fff1f3777f4ffbeffeffff7dfdbff * 2 ^ 240 +
  0xf66b87dff5d3ce660b73acd9b8f57bdaa8df7759cef2d7ad2fa2df6728d9 * 2 ^ 480 +
  0x374d920289b1341544dc3eada235e3612bc88410a2178d98a1fb55203ada * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits054row3 : ℕ :=
  0xeffbfd8ffebff75ffffefeffffffffbffffffffffffffefff7ffffffffff * 2 ^ 0 +
  0xef66bff6adff7df77d6d7bedf6cfde7b3fe7ffffbfdfcfff7b77cad5f7ff * 2 ^ 240 +
  0x7e329abd7c33cebc71d55fa5937f56f94378c2f75bf3d40f815ff81d7bb6 * 2 ^ 480 +
  0x4a522503ea5d3c4c02b8c62544e04357b2900e3b8f4a6cf746d3cd88ef5e * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits054 : Vector ℕ 4 := #v[bits054row0, bits054row1, bits054row2, bits054row3]

@[expose]
def bits055row0 : ℕ :=
  0xbbffffffdffdffffffdfffffffffffffffefffffffffffffffffffffffff * 2 ^ 0 +
  0xe7bf8d6d9ebd2efab6b7d7f62f5fa5fff7fffff7f75ffbb6fdffff57ffff * 2 ^ 240 +
  0x69f432af73f673fea2271cf6f35db655f6935c2a77e6ebefa9bffaa3b5be * 2 ^ 480 +
  0x90e91418d4203702b91f20685e8a862c802348f74e739ec69837e6734df9 * 2 ^ 720 +
  0x22469016 * 2 ^ 960

@[expose]
def bits055row1 : ℕ :=
  0xfa7ffafffff6ffbffdfffffffbffefffddf7fffffffffeffffffffffffff * 2 ^ 0 +
  0xfddeecb8941bfdfe3db1ddaebedfedfcefff7afbfebfe5bfd9f7bfe67fff * 2 ^ 240 +
  0x3b235b53dfe975b7a6ab09dbdd443ed13f9bdb8dfbe8ccd9fd7fd731399d * 2 ^ 480 +
  0x89e8ebf44032e4e28ee89b922b6b9ab44d07735bdd8accc810bfcda591da * 2 ^ 720 +
  0x42a299a * 2 ^ 960

@[expose]
def bits055row2 : ℕ :=
  0x9f1ffbfd7feffffffb7ef7ffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfcb3db787f5feb9ffbf7fefdcfe7cf6fff1f3777f4ffbfffeffff7dfdbff * 2 ^ 240 +
  0xf66b8fdff5d3ce660b73acd9b8f57bfaa8df7759cef2d7ad2fa2df6738d9 * 2 ^ 480 +
  0x374d920289b1349544dc3eada235e3612bc88c10a2578d98a1fb55203ada * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits055row3 : ℕ :=
  0xeffbfd8ffebff75ffffefeffffffffbffffffffffffffefff7ffffffffff * 2 ^ 0 +
  0xef66bff6adff7df77d6ffbedf6cfde7b3fe7ffffbfffcfff7b77ced5f7ff * 2 ^ 240 +
  0x7e329abd7c33cebc71d55fa5937f56f94378c2f75bf3d40f815ff81d7bb6 * 2 ^ 480 +
  0x4a522503ea5d3d4c02b8c62544e04357b2900e3b8f4a6cf746d3cd88ef5e * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits055 : Vector ℕ 4 := #v[bits055row0, bits055row1, bits055row2, bits055row3]

@[expose]
def bits056row0 : ℕ :=
  0xbbffffffdffdffffffdfffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xe7bf8d6d9ebd2efab6b7d7f62f5fe5fff7fffff7f75ffbb6fdffff57ffff * 2 ^ 240 +
  0x79f432af73f673fee3371cf6f35df655f6935c2a7fe6ebefa9bffaa3b5be * 2 ^ 480 +
  0x90e91418d4203702b91f20685ecae62c802348f74e739ec69837e7734df9 * 2 ^ 720 +
  0x22469016 * 2 ^ 960

@[expose]
def bits056row1 : ℕ :=
  0xfa7ffafffff6ffbffdfffffffbffefffddf7fffffffffeffffffffffffff * 2 ^ 0 +
  0xfddeecb8941bfdfe3db1ddeebedfedfcefff7afbfebfe5bfd9f7bfe67fff * 2 ^ 240 +
  0x3b235b53dfe975b7a6ab09dbdd443ed13f9bdb8dfbe8ccd9fd7fd731399d * 2 ^ 480 +
  0x89e8ebf44032f4e28ee89b922beb9ab44d07735bdd8bccc810bfcda591da * 2 ^ 720 +
  0x42a299a * 2 ^ 960

@[expose]
def bits056row2 : ℕ :=
  0x9f3ffbfdffeffffffb7ef7ffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfcb3db787f5fef9ffbf7fefdcfe7cf6fff1f3777f4ffbffffffff7dfdbff * 2 ^ 240 +
  0xff6b8fdff5d3ce660b73acd9b8f57bfaa8df7759cef2d7ad2fa2df673cd9 * 2 ^ 480 +
  0x374d920289b1349544dc3eafa235e7612bc88c50a25f8d98a1fb5520bada * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits056row3 : ℕ :=
  0xeffbfd8ffebff75ffffffeffffffffbffffffffffffffefff7ffffffffff * 2 ^ 0 +
  0xef66bff6adff7ff77d6ffbedf6cfde7b3fe7ffffbfffcfff7b77ced5f7ff * 2 ^ 240 +
  0x7e329abd7c33cebc71d55fa5937f56f94378c2f75bf3d40f815ff81d7bb6 * 2 ^ 480 +
  0x4a532503ea5d3d4c06b8c62544e04357b2900e3b8f4a6cf746d3cd88ef5e * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits056 : Vector ℕ 4 := #v[bits056row0, bits056row1, bits056row2, bits056row3]

@[expose]
def bits057row0 : ℕ :=
  0xbbffffffdffdffffffdfffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xe7bf8d6d9ebd2efab6b7d7f62f5fe5fff7fffff7f77ffbb7fdffff57ffff * 2 ^ 240 +
  0x7bf432af73f773fee3371cf6f35df655f6935c2a7fe6ebefa9bffaa3b5be * 2 ^ 480 +
  0x90e91418d4203702b91f20685ecae62c802348f74e739ec69837e7734df9 * 2 ^ 720 +
  0x22469016 * 2 ^ 960

@[expose]
def bits057row1 : ℕ :=
  0xfa7ffefffff6ffbffdfffffffbffffffddfffffffffffeffffffffffffff * 2 ^ 0 +
  0xfddfecb8941bfdfe3db9ddeebedfedfcefff7afbfebfe5bfd9f7bfe67fff * 2 ^ 240 +
  0x3b235b53ffe975b7a6ab09dbdd443ed13f9bdb8dfbe8ccd9fd7fd731399d * 2 ^ 480 +
  0x89e8ebf44032f4e28ee89b922beb9ab44d07735bdd8bccc810bfcda591fa * 2 ^ 720 +
  0x42a299a * 2 ^ 960

@[expose]
def bits057row2 : ℕ :=
  0x9f3ffbfdffeffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfcbbdf787f5fef9ffbfffefddfe7ef6fff1f7777f4ffbffffffff7dfdbff * 2 ^ 240 +
  0xff6b8fdff5d3ce663b73acd9b8f77ffae8df7759cef2d7ad2fa2df673dd9 * 2 ^ 480 +
  0x374d920289b13cd544dc3eafa235e7612bc88c50a25f8d98a1fb552cbada * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits057row3 : ℕ :=
  0xeffbfd8ffebff75ffffffeffffffffbffffffffffffffefff7ffffffffff * 2 ^ 0 +
  0xef66bffeadff7ff77d6ffbedf6cfde7b3fe7ffffbfffcfff7b77ced5ffff * 2 ^ 240 +
  0x7e329abd7c33cebc71d55fa5937f56f94378c2f75bf3d40f815ff81d7bb6 * 2 ^ 480 +
  0x4a532503ea5d3d4c06b8c62544e04357b2900e3b8f4a6cf746d3cd88ef5e * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits057 : Vector ℕ 4 := #v[bits057row0, bits057row1, bits057row2, bits057row3]

@[expose]
def bits058row0 : ℕ :=
  0xbbffffffdffdffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xe7bf8d6d9ebd2efab7b7d7f62f5fe5fff7fffff7f77ffbb7fdffff57ffff * 2 ^ 240 +
  0x7bf432af73f773fee3371cf6f35df655f6935c2a7fe6ebefa9bffaa3b5be * 2 ^ 480 +
  0x90e91418d4213702b91f20685ecae62c80234af74e739ec69837e7734df9 * 2 ^ 720 +
  0x22469017 * 2 ^ 960

@[expose]
def bits058row1 : ℕ :=
  0xfafffefffff6ffbffdfffffffbffffffddfffffffffffeffffffffffffff * 2 ^ 0 +
  0xfddfecb8947bfdff3df9ddeebedfedfceffffafbfebfe5bfd9f7bfe67fff * 2 ^ 240 +
  0x3b235bd3ffe9f5b7a6ab09dbdd443ed33f9bdb8dfbe8ccd9fd7fd735399d * 2 ^ 480 +
  0x89e8ebfc4032f4e28ee89b922beb9ab44d07735bddabccc810bfcda591fa * 2 ^ 720 +
  0x42a299a * 2 ^ 960

@[expose]
def bits058row2 : ℕ :=
  0x9f3ffbfdffeffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfcbbff787f5fef9ffbfffefddfe7ef6fff1f7777f4ffbffffffff7dfdbff * 2 ^ 240 +
  0xff6b8fdff5d3ce663b77acd9b8f77ffae8df7759cef2d7ad2faadf673dd9 * 2 ^ 480 +
  0x374d920289b13cd544dc3eafa275e7612bc88c50a25f8d98a1fb552cbada * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits058row3 : ℕ :=
  0xeffbfd8ffebff77ffffffeffffffffbffffffffffffffefff7ffffffffff * 2 ^ 0 +
  0xef66bffeadff7ff77d6ffbedf6cfde7b3fefffffbfffcffffb77ced5ffff * 2 ^ 240 +
  0x7e7a9abd7c33cebc71d5dfa5937f56f94378c2f75bf3d40f835ff81d7fb6 * 2 ^ 480 +
  0x4a532703ea5d3d4c06b8c62544e04357b2908e3b8f4a6cf746d3cd88efde * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits058 : Vector ℕ 4 := #v[bits058row0, bits058row1, bits058row2, bits058row3]

@[expose]
def bits059row0 : ℕ :=
  0xfbffffffdfffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xe7bfcd6d9ebd2efab7bfd7ff2f7fe5fffffffff7f77ffbb7fdffffd7ffff * 2 ^ 240 +
  0x7ff533af73f773fee3779df6f35dfe55f6935c3a7fe6ebefa9bffab3b5fe * 2 ^ 480 +
  0x90e91418d4a13702b91f20685ecae62c84236af74e739ec69837e77b4df9 * 2 ^ 720 +
  0x22469017 * 2 ^ 960

@[expose]
def bits059row1 : ℕ :=
  0xfafffefffff6ffbffdfffffffbffffffddfffffffffffeffffffffffffff * 2 ^ 0 +
  0xfddfecb8947bfdff3df9ddeebedfedfceffffafbfebfe5bfd9f7bfe67fff * 2 ^ 240 +
  0x3b235bd3ffe9f5b7a6ab09dbdd443ed33f9bdb8dfbe8ccd9fd7fd735399d * 2 ^ 480 +
  0x89e8ebfc4032f4e28ee89b922beb9ab44d07735bddabccc810bfcda591fa * 2 ^ 720 +
  0x42a299a * 2 ^ 960

@[expose]
def bits059row2 : ℕ :=
  0x9f3ffbffffeffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfcbbff787f5fef9ffbfffefddfe7ef6fff1f7777f4ffbffffffff7dfdbff * 2 ^ 240 +
  0xff6b8fdff5d3ce663b77acd9b8f77ffae8df7759eef2d7ad2faadf677dd9 * 2 ^ 480 +
  0x374d920289b13cd544dc3eafa275e7612bc88c50a25f8d98a1fb552cbada * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits059row3 : ℕ :=
  0xeffbfd8ffefff77ffffffeffffffffbffffffffffffffefff7ffffffffff * 2 ^ 0 +
  0xefe6bffeadff7ff77d6ffbedf6efde7b3fefffffbfffcfffff77ced5ffff * 2 ^ 240 +
  0x7e7a9abd7c33cebc71d7ffa5937f56f94378c2f75bf3d40f835ff81d7fb6 * 2 ^ 480 +
  0x4a532703ea5d3d4c06b8c62544e04357b2908e3b8f4a6cf746d3cd88efde * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits059 : Vector ℕ 4 := #v[bits059row0, bits059row1, bits059row2, bits059row3]

@[expose]
def bits060row0 : ℕ :=
  0xfbffffffdfffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xe7bfdd6d9ebd2efab7ffd7ff7f7fe5fffffffff7ff7ffbf7fdffffd7ffff * 2 ^ 240 +
  0x7ff5b3af73f773fee377bdf6f35dfe55fe937c3a7fe6ebefabbffab3fdfe * 2 ^ 480 +
  0x90e91418d4a13792b91f20685eeae66c84236af7ce7b9ec69837e77b4df9 * 2 ^ 720 +
  0x22469017 * 2 ^ 960

@[expose]
def bits060row1 : ℕ :=
  0xfafffefffffeffbffdfffffffbffffffddfffffffffffeffffffffffffff * 2 ^ 0 +
  0xfddfecb8947bfdff3df9ddeebfdfedfceffffafbfebfe5bfd9f7bfe67fff * 2 ^ 240 +
  0x3b235bd3ffe9f5b7a6ab09dbdd443ed33f9bdb8dfbe8ccd9fd7fd735399d * 2 ^ 480 +
  0x89e8ebfc4032f4e28ee89b922beb9ab44d07735bddabccc810bfcde591fa * 2 ^ 720 +
  0x42a299a * 2 ^ 960

@[expose]
def bits060row2 : ℕ :=
  0x9f3ffbffffeffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfcbbff787f5fef9ffffffefddfe7ef6fff9f7777f4ffbffffffff7dfdbff * 2 ^ 240 +
  0xff6b8fdff5d3ce6e3b77acd9bcf77ffae8df7759eff2d7ad2faadfe77fd9 * 2 ^ 480 +
  0x37cd920289b13cd544dc3eefa275e7612bc88c50a25f8d98a1ff552cbada * 2 ^ 720 +
  0x110a4b61 * 2 ^ 960

@[expose]
def bits060row3 : ℕ :=
  0xeffbfd8ffefff77ffffffeffffffffbffffffffffffffefff7ffffffffff * 2 ^ 0 +
  0xefe6bffeadff7ff77d6ffbedf6efde7b3fefffffbfffcfffff77ced5ffff * 2 ^ 240 +
  0x7e7a9abd7c33cebc71d7ffa5937f56f94378c2f75bf3d40f835ff81d7fb6 * 2 ^ 480 +
  0x4a532703ea5d3d4c06b8c62544e04357b2908e3b8f4a6cf746d3cd88efde * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits060 : Vector ℕ 4 := #v[bits060row0, bits060row1, bits060row2, bits060row3]

@[expose]
def bits061row0 : ℕ :=
  0xfbffffffdfffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xe7bfdd6d9ebd2efab7ffd7ff7f7fe5fffffffff7ff7ffbf7fdffffd7ffff * 2 ^ 240 +
  0x7ff5b3af77f773fee377bdf6fb5dfe55fe937c3a7fe6ebefabbffab3fdfe * 2 ^ 480 +
  0x90e91418d4a13792b93f20685eeae66c84236af7ce7b9ec69837e7fb4df9 * 2 ^ 720 +
  0x22669017 * 2 ^ 960

@[expose]
def bits061row1 : ℕ :=
  0xfafffefffffeffbffdfffffffbffffffddfffffffffffeffffffffffffff * 2 ^ 0 +
  0xfddfecb8947bfdff3df9ddeebfdfedfceffffafbfebfe5ffd9f7ffe67fff * 2 ^ 240 +
  0xbb235bd3ffe9f5b7a6eb09dbdd443ed33f9bdb8dfbe8ccd9fd7fd735399d * 2 ^ 480 +
  0x89e8ebfc4032f4e28ee89b922beb9ab44d07735bddabccc810bfcde591fa * 2 ^ 720 +
  0x42a299a * 2 ^ 960

@[expose]
def bits061row2 : ℕ :=
  0x9f3ffbffffeffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbbff787f5fefdffffffefddfe7ef6fff9ff777feffbffffffff7dffbff * 2 ^ 240 +
  0xff6b8fdff5d3de6e3b77acf9bcff7ffae8df7779eff2d7ad2faadfe77ff9 * 2 ^ 480 +
  0x3fed920289b13dd544dd3eefe275e7692bc88c50a25f8d98a1ffd52cbada * 2 ^ 720 +
  0x110b4b61 * 2 ^ 960

@[expose]
def bits061row3 : ℕ :=
  0xeffbfd8ffefff77ffffffeffffffffbffffffffffffffeffffffffffffff * 2 ^ 0 +
  0xefe6bffeadff7ff77d6ffbedf6efde7b3fefffffbfffcfffff77ded5ffff * 2 ^ 240 +
  0x7e7a9abd7c33cebc71d7ffa5937f56f94378c2f75bf3d40f835ff81d7fb6 * 2 ^ 480 +
  0x4a532703ea5d3d4c06b8c62544e84357b2908e3b8f4aecf746d3cd88efde * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits061 : Vector ℕ 4 := #v[bits061row0, bits061row1, bits061row2, bits061row3]

@[expose]
def bits062row0 : ℕ :=
  0xfbffffffdfffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xe7bfdd6d9ebd2efab7ffd7ff7f7fe5fffffffff7ff7ffbf7fdffffd7ffff * 2 ^ 240 +
  0x7ff5b3af77f773fee377bdf6fb5dfe55fe937c3a7fe6ebefabbffab3fdfe * 2 ^ 480 +
  0x90e91418d4a13792b93f20685eeae66c84236af7ce7b9ec69837e7fb4df9 * 2 ^ 720 +
  0x22669017 * 2 ^ 960

@[expose]
def bits062row1 : ℕ :=
  0xfafffefffffefffffdfffffffbffffffddfffffffffffeffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbfdff3df9ddeebfdfedfeeffffbfbfebfe5fff9f7ffe67fff * 2 ^ 240 +
  0xbb235bd3ffe9f5b7a6eb8bdbddc43ed33fdbdb8dfbe8ccd9fd7fd735799d * 2 ^ 480 +
  0x8be8ebfc4032f4e28ee89b922beb9ab46d07775bdfebccc910bfcde591fa * 2 ^ 720 +
  0x42a299b * 2 ^ 960

@[expose]
def bits062row2 : ℕ :=
  0x9f3ffbffffeffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbbff7b7f5fefdffffffefddfe7ef6fff9ff777feffbfffffffffdffbff * 2 ^ 240 +
  0xff6b8fdff5d3de6e3b77acf9bcff7ffae8df7779eff2d7ad2faadfe77ff9 * 2 ^ 480 +
  0x3fed920299b13dd544dd3eefe275e769abc8ac50a25f8d98a1ffd52cbbfa * 2 ^ 720 +
  0x110b4b61 * 2 ^ 960

@[expose]
def bits062row3 : ℕ :=
  0xeffbfdaffefff77ffffffeffffffffbffffffffffffffeffffffffffffff * 2 ^ 0 +
  0xefe6bffeadff7ff77d6ffbedf6efdf7bbfefffffbfffcfffff77fed5ffff * 2 ^ 240 +
  0x7e7a9abd7c33cebc71d7ffa5937f76f9c378c2f75bf3d40f835ff81d7fb6 * 2 ^ 480 +
  0x4a532703ea5d3d4c06b8c62545e84357b2908e3b8f4aecf746d3cd88efde * 2 ^ 720 +
  0x8d12603 * 2 ^ 960

@[expose]
def bits062 : Vector ℕ 4 := #v[bits062row0, bits062row1, bits062row2, bits062row3]

@[expose]
def bits063row0 : ℕ :=
  0xfbffffffdfffffffffffffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xefbfff6d9ebd2efab7ffd7ff7f7fe7fffffffff7ff7ffbfffdffffd7ffff * 2 ^ 240 +
  0x7ff5b3af77f777fee377bdf6fb5dfe55fe937c3a7ff6ebefabbffab3fdfe * 2 ^ 480 +
  0x90e91418d4a13792b93f30685eeae66c84236af7ee7b9ec698b7e7fb4df9 * 2 ^ 720 +
  0x22669017 * 2 ^ 960

@[expose]
def bits063row1 : ℕ :=
  0xfafffefffffefffffdfffffffbffffffddffffffffffffffffffffffffff * 2 ^ 0 +
  0xfddfecb894fbfdff3df9ddeebfdfedfeeffffbfbfebfe5fff9f7ffe67fff * 2 ^ 240 +
  0xbb235bd3ffe9f5b7a6eb8bdbddc43ed33fdbdb8dfbe8ccf9fd7fd735799d * 2 ^ 480 +
  0x8be8ebfc4032f4e28ee89b922beb9ab46d07775bdfebccc910bfcdf591fa * 2 ^ 720 +
  0x42a299b * 2 ^ 960

@[expose]
def bits063row2 : ℕ :=
  0x9f3ffbffffeffffffffeffffffffffffffffffffffffffffffffffffffff * 2 ^ 0 +
  0xfdbbff7b7f5fefdffffffefddfe7ef6fff9ff777feffbfffffffffdffbff * 2 ^ 240 +
  0xff6b8fdff5d3de6e3b77aef9bcff7ffae8df7779eff2d7ad2faadfe77ff9 * 2 ^ 480 +
  0x3fed920a99b13dd544dd3eefe275e769abc8ac50a25f8d98a1ffd52cbbfa * 2 ^ 720 +
  0x110b4b61 * 2 ^ 960

@[expose]
def bits063row3 : ℕ :=
  0xeffbffaffefff77ffffffeffffffffbffffffffffffffeffffffffffffff * 2 ^ 0 +
  0xefe6bffeadff7ff77d6fffedf6efdf7bbfefffffbfffdfffff77fed5ffff * 2 ^ 240 +
  0x7e7a9bbd7c33cebc71d7ffa5937f76f9e378e2ff5bf3d40f8b5ff89d7fb6 * 2 ^ 480 +
  0x4a572703ea5d3d4c06b8c625d5e84357ba908e3b8f4aecf747dbcd88efde * 2 ^ 720 +
  0x8d92e03 * 2 ^ 960

@[expose]
def bits063 : Vector ℕ 4 := #v[bits063row0, bits063row1, bits063row2, bits063row3]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
