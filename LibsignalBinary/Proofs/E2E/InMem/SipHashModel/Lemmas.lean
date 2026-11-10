/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.SipHashModel.Model

/-!
# Structural and Unrolling Lemmas for `SipHasher13`

Streaming invariants (`write_length`, `write_ntail_lt`), closed-form 5-block unrolling of
`hashAddr` for 36-byte UUID names (`hashAddr_of_length_eq_36`), symbolic-key specializations
for `aliceName` and `bobName`, and `hashbrown` control-tag bounds (`h2_lt_128`, `h2Bv_msb`).
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.SipHashModel

/-! ## `u8to64Le` Unrolling -/

@[simp]
theorem u8to64Le_zero (buf : List UInt8) (start : Nat) :
    u8to64Le buf start 0 = 0 := rfl

@[simp]
theorem u8to64Le_one (buf : List UInt8) (start : Nat) :
    u8to64Le buf start 1 = byteAt64 buf start := by
  change (0 : UInt64) ||| (byteAt64 buf (start + 0) <<< (0 : UInt64)) = byteAt64 buf start
  simp [Nat.add_zero]

theorem u8to64Le_two (buf : List UInt8) (start : Nat) :
    u8to64Le buf start 2 =
      byteAt64 buf start ||| (byteAt64 buf (start + 1) <<< 8) := by
  simp [u8to64Le]

theorem u8to64Le_four (buf : List UInt8) (start : Nat) :
    u8to64Le buf start 4 =
      byteAt64 buf start |||
      (byteAt64 buf (start + 1) <<< 8) |||
      (byteAt64 buf (start + 2) <<< 16) |||
      (byteAt64 buf (start + 3) <<< 24) := by
  simp [u8to64Le]

/-! ## `SipHasher13` Streaming Invariants -/

namespace SipHasher13

@[simp] theorem newWithKeys_k0 (k0 k1 : UInt64) : (newWithKeys k0 k1).k0 = k0 := rfl
@[simp] theorem newWithKeys_k1 (k0 k1 : UInt64) : (newWithKeys k0 k1).k1 = k1 := rfl
@[simp] theorem newWithKeys_length (k0 k1 : UInt64) : (newWithKeys k0 k1).length = 0 := rfl
@[simp] theorem newWithKeys_state (k0 k1 : UInt64) : (newWithKeys k0 k1).state = initState k0 k1 := rfl
@[simp] theorem newWithKeys_tail (k0 k1 : UInt64) : (newWithKeys k0 k1).tail = 0 := rfl
@[simp] theorem newWithKeys_ntail (k0 k1 : UInt64) : (newWithKeys k0 k1).ntail = 0 := rfl

@[simp]
theorem writeBlocks_zero (s : State) (msg : List UInt8) (i : Nat) :
    writeBlocks s msg i 0 = s := rfl

@[simp]
theorem writeBlocks_succ (s : State) (msg : List UInt8) (i count : Nat) :
    writeBlocks s msg i (count + 1) =
      writeBlocks (compressBlock s (loadU64Le msg i)) msg (i + 8) count := rfl

/-- Adding an offset `needed < 8` preserves strict inequality against multiples of 8. -/
theorem sip_loop_bound_iff (k m needed : Nat) (hneed : needed < 8) :
    8 * k + needed < 8 * m ↔ k < m := by
  omega

@[simp]
theorem write_length (h : SipHasher13) (msg : List UInt8) :
    (h.write msg).length = h.length + msg.length := by
  unfold write
  split
  · split <;> rfl
  · rfl

@[simp]
theorem writeU8_length (h : SipHasher13) (b : UInt8) :
    (h.writeU8 b).length = h.length + 1 := by
  simp [writeU8]

@[simp]
theorem writeStr_length (h : SipHasher13) (s : List UInt8) :
    (h.writeStr s).length = h.length + s.length + 1 := by
  simp [writeStr, Nat.add_assoc]

theorem write_ntail_lt (h : SipHasher13) (msg : List UInt8) (hnt : h.ntail < 8) :
    (h.write msg).ntail < 8 := by
  unfold write
  split
  · split <;> (dsimp; omega)
  · dsimp; omega

/-- From `ntail = 0`, `write` compresses `msg.length / 8` full blocks and buffers `msg.length % 8` tail bytes. -/
theorem write_of_ntail_zero (h : SipHasher13) (msg : List UInt8) (h0 : h.ntail = 0) :
    h.write msg =
      let len := msg.length
      let left := len % 8
      let nblocks := (len - left) / 8
      { h with
        length := h.length + len
        state := writeBlocks h.state msg 0 nblocks
        tail := u8to64Le msg (nblocks * 8) left
        ntail := left } := by
  unfold write
  simp [h0]

/-- When `0 < ntail < 7`, `writeU8` shifts the byte into `tail` without running a compression round. -/
theorem writeU8_of_ntail_between (h : SipHasher13) (b : UInt8)
    (hpos : 0 < h.ntail) (h7 : h.ntail < 7) :
    h.writeU8 b =
      { h with
        length := h.length + 1
        tail := h.tail ||| (b.toUInt64 <<< (UInt64.ofNat (8 * h.ntail)))
        ntail := h.ntail + 1 } := by
  have hne : (h.ntail != 0) = true := by
    cases hEq : h.ntail with
    | zero => omega
    | succ _ => rfl
  have hlt : 1 < 8 - h.ntail := by omega
  have hmin : min 1 (8 - h.ntail) = 1 := by omega
  unfold writeU8 write
  simp [hne, hlt, hmin, byteAt64]

end SipHasher13

/-! ## 36-Byte `ProtocolAddress` Unrolling -/

/-- SipHash state after compressing the four 8-byte blocks of a 36-byte `ProtocolAddress` name. -/
def stateAfterAddr36 (k0 k1 : UInt64) (name : List UInt8) : State :=
  let s0 := SipHasher13.initState k0 k1
  let s1 := compressBlock s0 (loadU64Le name 0)
  let s2 := compressBlock s1 (loadU64Le name 8)
  let s3 := compressBlock s2 (loadU64Le name 16)
  compressBlock s3 (loadU64Le name 24)

/-- Final length-padded word (`0x26` in byte 7, `dev` in byte 5, `0xff` in byte 4, `name[32..36]` in bytes 0..3). -/
def finalWordAddr36 (name : List UInt8) (dev : UInt8) : UInt64 :=
  (0x2600000000000000 : UInt64) |||
    ((u8to64Le name 32 4 ||| ((0xff : UInt64) <<< 32)) ||| (dev.toUInt64 <<< 40))

def finishWord (s : State) (b : UInt64) : UInt64 :=
  let s1 := compressBlock s b
  let s2 := { s1 with v2 := s1.v2 ^^^ 0xff }
  let s3 := dRounds s2
  s3.v0 ^^^ s3.v1 ^^^ s3.v2 ^^^ s3.v3

/-- Closed-form 5-block expression for `hashAddr` on a 36-byte name. -/
def hashAddr36 (k0 k1 : UInt64) (name : List UInt8) (dev : UInt8) : UInt64 :=
  finishWord (stateAfterAddr36 k0 k1 name) (finalWordAddr36 name dev)

theorem writeAddr_of_length_eq_36 (k0 k1 : UInt64) (name : List UInt8) (dev : UInt8)
    (hlen : name.length = 36) :
    ((SipHasher13.newWithKeys k0 k1).writeStr name).writeU8 dev =
      { k0 := k0
        k1 := k1
        length := 38
        state := stateAfterAddr36 k0 k1 name
        tail := (u8to64Le name 32 4 ||| ((0xff : UInt64) <<< 32)) ||| (dev.toUInt64 <<< 40)
        ntail := 6 } := by
  unfold SipHasher13.writeStr SipHasher13.writeU8 SipHasher13.write
  simp [hlen, byteAt64]
  rfl

/-- For any 36-byte `name`, `hashAddr` equals the unrolled 5-block computation `hashAddr36`. -/
theorem hashAddr_of_length_eq_36 (k0 k1 : UInt64) (name : List UInt8) (dev : UInt8)
    (hlen : name.length = 36) :
    hashAddr k0 k1 name dev = hashAddr36 k0 k1 name dev := by
  unfold hashAddr
  rw [writeAddr_of_length_eq_36 k0 k1 name dev hlen]
  unfold SipHasher13.finish hashAddr36 finishWord finalWordAddr36
  dsimp only []
  have h38 : (((UInt64.ofNat 38) &&& 0xff) <<< 56) = (0x2600000000000000 : UInt64) := rfl
  rw [h38]

/-! ## Party Constants and Symbolic-Key Unrollings -/

/-- UTF-8 bytes of Alice's 36-byte UUID service identifier. -/
def aliceName : List UInt8 := asciiBytes "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b"

/-- UTF-8 bytes of Bob's 36-byte UUID service identifier. -/
def bobName : List UInt8 := asciiBytes "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6"

theorem aliceName_length : aliceName.length = 36 := rfl
theorem bobName_length : bobName.length = 36 := rfl

theorem alice_block0 : loadU64Le aliceName 0 = 0x6532633166366138 := rfl
theorem alice_block1 : loadU64Le aliceName 8 = 0x65342d643462332d := rfl
theorem alice_block2 : loadU64Le aliceName 16 = 0x2d623061392d6635 := rfl
theorem alice_block3 : loadU64Le aliceName 24 = 0x6634653364326331 := rfl
theorem alice_final_dev1 : finalWordAddr36 aliceName 1 = 0x260001ff62366135 := rfl

theorem bob_block0 : loadU64Le bobName 0 = 0x3031663265336435 := rfl
theorem bob_block1 : loadU64Le bobName 8 = 0x63342d623861372d := rfl
theorem bob_block2 : loadU64Le bobName 16 = 0x2d663065382d6439 := rfl
theorem bob_block3 : loadU64Le bobName 24 = 0x3464336332623161 := rfl
theorem bob_final_dev1 : finalWordAddr36 bobName 1 = 0x260001ff36663565 := rfl

/-- Five-block unrolling of `hashAddr k0 k1 aliceName 1`. -/
theorem hashAddr_alice_dev1 (k0 k1 : UInt64) :
    hashAddr k0 k1 aliceName 1 =
      let s0 := SipHasher13.initState k0 k1
      let s1 := compressBlock s0 0x6532633166366138
      let s2 := compressBlock s1 0x65342d643462332d
      let s3 := compressBlock s2 0x2d623061392d6635
      let s4 := compressBlock s3 0x6634653364326331
      finishWord s4 0x260001ff62366135 := by
  rw [hashAddr_of_length_eq_36 k0 k1 aliceName 1 aliceName_length]
  unfold hashAddr36 stateAfterAddr36
  rw [alice_block0, alice_block1, alice_block2, alice_block3, alice_final_dev1]

/-- Five-block unrolling of `hashAddr k0 k1 bobName 1`. -/
theorem hashAddr_bob_dev1 (k0 k1 : UInt64) :
    hashAddr k0 k1 bobName 1 =
      let s0 := SipHasher13.initState k0 k1
      let s1 := compressBlock s0 0x3031663265336435
      let s2 := compressBlock s1 0x63342d623861372d
      let s3 := compressBlock s2 0x2d663065382d6439
      let s4 := compressBlock s3 0x3464336332623161
      finishWord s4 0x260001ff36663565 := by
  rw [hashAddr_of_length_eq_36 k0 k1 bobName 1 bobName_length]
  unfold hashAddr36 stateAfterAddr36
  rw [bob_block0, bob_block1, bob_block2, bob_block3, bob_final_dev1]

/-! ## `hashbrown` Control-Tag Lemmas -/

@[simp] theorem h1_eq (hash : UInt64) : h1 hash = hash := rfl
@[simp] theorem h1Bv_eq (hash : BitVec 64) : h1Bv hash = hash := rfl

/-- `h2` clears bit 7 (`< 128`), matching `hashbrown` `Tag::is_full`. -/
theorem h2_lt_128 (hash : UInt64) : (h2 hash).toNat < 128 := by
  change (hash >>> 57).toUInt8.toNat &&& 127 < 128
  exact Nat.and_lt_two_pow _ (n := 7) (by decide)

@[simp]
theorem h2Bv_msb (hash : BitVec 64) : (h2Bv hash).msb = false := by
  rw [BitVec.msb_eq_false_iff_two_mul_lt]
  have h := h2_lt_128 (UInt64.ofBitVec hash)
  change (h2Bv hash).toNat < 128 at h
  omega

end CryptoVerification.E2E.InMem.SipHashModel
