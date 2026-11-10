/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.SipHashModel.Lemmas

/-!
# SipHash-1-3 and `ProtocolAddress` Hash Known-Answer Tests

Kernel-checked (`rfl` / `decide`) known-answer tests for `SipHasher13`, `hashAddr`, and SwissTable
`h1` / `h2` split (`SipHashModel`), cross-checked against Rust 1.98.1 `DefaultHasher`,
`siphasher::sip::SipHasher13`, and `libsignal_core::ProtocolAddress` (libsignal v0.105.4).
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.SipHashModel

def ascii16 : List UInt8 := asciiBytes "0123456789abcdef"

def seq16 : List UInt8 := (List.range 16).map UInt8.ofNat

def stdK0 : UInt64 := 0x0706050403020100

def stdK1 : UInt64 := 0x0f0e0d0c0b0a0908

/-- `DefaultHasher::new()` (`k0 = 0, k1 = 0`) raw `write` digests on `0..=16` ASCII bytes. -/
theorem kat_write_zero_keys_0_to_16 :
    (List.range 17).map (fun len => hashBytes 0 0 (ascii16.take len)) =
      [ 0xd1fba762150c532c, 0x49bc192c478bfc2e, 0x748af13ac9ed7bec, 0x27007a47f534b10c,
        0xe2614298a482dc84, 0xe2c4ef0f59d25695, 0xb95fd06b7c3d68ab, 0x810aaf7acf670379,
        0xda3dcedf84ea6cc6, 0xb79d8581f8552753, 0x52b62a4184e1c734, 0x7188f6617526617b,
        0x58ad1e5ac2bf1033, 0x6c5a77666b0b9ac0, 0x5aa577192a3435c6, 0x26f4d862282d8fcb,
        0x1d42b30f7e060c24 ] := rfl

/-- `DefaultHasher::new()` `str::hash` (`0xff`-terminated) digests on `0..=16` ASCII bytes. -/
theorem kat_writeStr_zero_keys_0_to_16 :
    (List.range 17).map (fun len => hashStr 0 0 (ascii16.take len)) =
      [ 0x30406ea523c53def, 0xfc6647014fb554e5, 0xfeb1fdde74b8c8ec, 0x9ec937f6301349ea,
        0xa2ac2dbeb0cf80e4, 0xd8c42706cb713c73, 0x6e484d505bd4e675, 0x73aba660808c83e2,
        0x5afa6202e1213f4d, 0x4ac3a8f2cb7e217a, 0x3a4f0b804ace0c65, 0xfffb5854410a89b3,
        0x362e9502c75547df, 0x67757398ce42914d, 0x1b54e376823f8f17, 0x8283e94c24e84630,
        0x3cdd3ee8e7c8d0cb ] := rfl

/-- `DefaultHasher::new()` `ProtocolAddress::hash` (`device_id = 1`) digests on `0..=16`-byte names. -/
theorem kat_hashAddr_zero_keys_0_to_16 :
    (List.range 17).map (fun len => hashAddr 0 0 (ascii16.take len) 1) =
      [ 0xdbed5a99ffd08739, 0x5b6f4c455b64b684, 0xf8b9739a554eddbf, 0x91e2368e50dbc2c9,
        0xf7681b021e950c39, 0xe3fdb389938b3433, 0x4559178af59fa971, 0x7118d66a3d597222,
        0xe37fc3cba1f85a79, 0xa59b1544e45060c1, 0x28857c8538ca366e, 0x388d695fd9e24bb8,
        0xe994f55c443c8cb4, 0x978a3d23663d44a7, 0x43496c2955417c53, 0xab1e9066d8d4c915,
        0x1af20600b3857831 ] := rfl

/-- Keyed `SipHasher13` digests under `(stdK0, stdK1)` on `0..=16` sequential bytes. -/
theorem kat_keyed_std_0_to_16 :
    (List.range 17).map (fun len => hashBytes stdK0 stdK1 (seq16.take len)) =
      [ 0xabac0158050fc4dc, 0xc9f49bf37d57ca93, 0x82cb9b024dc7d44d, 0x8bf80ab8e7ddf7fb,
        0xcf75576088d38328, 0xdef9d52f49533b67, 0xc50d2b50c59f22a7, 0xd3927d989bb11140,
        0x369095118d299a8e, 0x25a48eb36c063de4, 0x79de85ee92ff097f, 0x70c118c1f94dc352,
        0x78a384b157b4d9a2, 0x306f760c1229ffa7, 0x605aa111c0f95d34, 0xd320d86d2a519956,
        0xcc4fdd1a7d908b66 ] := rfl

/-- `DefaultHasher::new()` on `ALICE` (`"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b"`, device `1`). -/
theorem kat_alice_zero_keys :
    hashAddr 0 0 aliceName 1 = 0x9c76d8f4202f6e79 ∧
    h1 (hashAddr 0 0 aliceName 1) = 0x9c76d8f4202f6e79 ∧
    h2 (hashAddr 0 0 aliceName 1) = 0x4e ∧
    probeStart (hashAddr 0 0 aliceName 1) 3 = 1 := by
  decide

/-- `DefaultHasher::new()` on `BOB` (`"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6"`, device `1`). -/
theorem kat_bob_zero_keys :
    hashAddr 0 0 bobName 1 = 0xb9c61ac7b6ac4938 ∧
    h1 (hashAddr 0 0 bobName 1) = 0xb9c61ac7b6ac4938 ∧
    h2 (hashAddr 0 0 bobName 1) = 0x5c ∧
    probeStart (hashAddr 0 0 bobName 1) 3 = 0 := by
  decide

/-- Second `RandomState` on the same thread (`k0 = 1, k1 = 0` when initial keys are `(0, 0)`). -/
theorem kat_alice_bob_keys_1_0 :
    hashAddr 1 0 aliceName 1 = 0xbd00855072d88235 ∧
    h2 (hashAddr 1 0 aliceName 1) = 0x5e ∧
    hashAddr 1 0 bobName 1 = 0xab7b5538321ff555 ∧
    h2 (hashAddr 1 0 bobName 1) = 0x55 := by
  decide

theorem kat_alice_bob_std_keys :
    hashAddr stdK0 stdK1 aliceName 1 = 0x351e1c50d5653544 ∧
    h2 (hashAddr stdK0 stdK1 aliceName 1) = 0x1a ∧
    hashAddr stdK0 stdK1 bobName 1 = 0xe3be20e6e526fbe8 ∧
    h2 (hashAddr stdK0 stdK1 bobName 1) = 0x71 := by
  decide

theorem kat_alice_bob_custom_keys :
    hashAddr 0xdeadbeefcafebabe 0x0123456789abcdef aliceName 1 = 0x81564a2903fecb02 ∧
    h2 (hashAddr 0xdeadbeefcafebabe 0x0123456789abcdef aliceName 1) = 0x40 ∧
    hashAddr 0xdeadbeefcafebabe 0x0123456789abcdef bobName 1 = 0x93df30b5ce78a370 ∧
    h2 (hashAddr 0xdeadbeefcafebabe 0x0123456789abcdef bobName 1) = 0x49 := by
  decide

theorem kat_alice_bob_bv_zero_keys :
    hashAddrBv 0#64 0#64 (aliceName.map UInt8.toBitVec) 1#8 = 0x9c76d8f4202f6e79#64 ∧
    h2Bv (hashAddrBv 0#64 0#64 (aliceName.map UInt8.toBitVec) 1#8) = 0x4e#8 ∧
    hashAddrBv 0#64 0#64 (bobName.map UInt8.toBitVec) 1#8 = 0xb9c61ac7b6ac4938#64 ∧
    h2Bv (hashAddrBv 0#64 0#64 (bobName.map UInt8.toBitVec) 1#8) = 0x5c#8 := by
  decide

end CryptoVerification.E2E.InMem.SipHashModel
