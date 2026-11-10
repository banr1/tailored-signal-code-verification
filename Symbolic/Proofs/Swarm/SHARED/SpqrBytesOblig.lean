/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.SHARED.SpqrBytesDefs

/-!
# First-Send Key and Preamble on Initial SPQR V1 State

Proves that a successful `spqrSendB` on a fresh `.a2b` state `spqrInitB F K mac k [0#8]` (for
32-byte `k`) derives the epoch-0 chain key at index `1#32` independently of `c` and `mac`, and
produces a message preamble with `index = 1#32`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.SHARED.SpqrBytes

open CryptoGames.HMAC (toBEBytes)
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
open Symbolic.Swarm.SHARED.HookAuth

private theorem spqrIdxOfBytes?_spqrLeBytes4 (idx : BitVec 32) :
    spqrIdxOfBytes? (spqrLeBytes4 idx) = some idx := by
  simp only [spqrLeBytes4, spqrIdxOfBytes?, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  have hlt : idx.toNat < 4294967296 := idx.isLt
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change (idx.toNat % 256 + idx.toNat / 256 % 256 * 256 +
    idx.toNat / 65536 % 256 * 65536 + idx.toNat / 16777216 % 256 * 16777216) % 4294967296 = idx.toNat
  have hd1 : idx.toNat / 65536 = idx.toNat / 256 / 256 := by rw [Nat.div_div_eq_div_mul]
  have hd2 : idx.toNat / 16777216 = idx.toNat / 65536 / 256 := by rw [Nat.div_div_eq_div_mul]
  have hm0 := Nat.mod_add_div idx.toNat 256
  have hm1 := Nat.mod_add_div (idx.toNat / 256) 256
  have hm2 := Nat.mod_add_div (idx.toNat / 65536) 256
  rw [ ← hd1] at hm1
  rw [← hd2] at hm2
  have hq3 : idx.toNat / 16777216 < 256 := by omega
  have hm3 : idx.toNat / 16777216 % 256 = idx.toNat / 16777216 := Nat.mod_eq_of_lt hq3
  rw [hm3]
  have hsum : idx.toNat % 256 + idx.toNat / 256 % 256 * 256 +
      idx.toNat / 65536 % 256 * 65536 + idx.toNat / 16777216 * 16777216 = idx.toNat := by
    omega
  rw [hsum, Nat.mod_eq_of_lt hlt]

private theorem hkdfToVecUnchecked_64_length (F : ShaCompress) (salt ikm info : Bytes) :
    (hkdfToVecUnchecked F salt ikm info 64).length = 64 := by
  unfold hkdfToVecUnchecked hkdfToSliceUnchecked hkdfExpand
  change ((CryptoGames.HKDF.hkdfBlocks F (hkdfExtractBytes F salt ikm) info 2).flatten.take 64).length = 64
  dsimp only [CryptoGames.HKDF.hkdfBlocks, List.nil_append, List.cons_append, List.flatten_cons, List.flatten_nil]
  simp only [List.length_take, List.length_append, List.length_nil, length_hmacWith]
  rfl

private theorem authenticator_update_eq (F : ShaCompress) (self : Authenticator) (ep : Epoch) (k : Bytes) :
    self.update F ep k =
      { rootKey := (hkdfToVecUnchecked F (List.replicate 32 0) (self.rootKey ++ k)
          (Authenticator.updateLabel ++ toBEBytes 8 ep) 64).take 32
        macKey := (hkdfToVecUnchecked F (List.replicate 32 0) (self.rootKey ++ k)
          (Authenticator.updateLabel ++ toBEBytes 8 ep) 64).drop 32 } := rfl

private theorem authenticator_update_lengths (F : ShaCompress) (self : Authenticator) (ep : Epoch) (k : Bytes) :
    (self.update F ep k).rootKey.length = 32 ∧
    (self.update F ep k).macKey.length = 32 := by
  rw [authenticator_update_eq]
  dsimp only
  rw [List.length_take, List.length_drop, hkdfToVecUnchecked_64_length]
  exact ⟨rfl, rfl⟩

private theorem authenticator_new_lengths (F : ShaCompress) (k : Bytes) (ep : Epoch) :
    (Authenticator.new F k ep).rootKey.length = 32 ∧
    (Authenticator.new F k ep).macKey.length = 32 :=
  authenticator_update_lengths F { rootKey := List.replicate 32 0, macKey := List.replicate 32 0 } ep k

private theorem proto_takeExact_append (xs ys : Bytes) :
    Proto.takeExact xs.length (xs ++ ys) = .ok (xs, ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.cons_append, Proto.takeExact, ih, Bind.bind, Except.bind]

private theorem proto_takeExact_of_length {n : Nat} {xs : Bytes} (h : xs.length = n) (ys : Bytes) :
    Proto.takeExact n (xs ++ ys) = .ok (xs, ys) := by
  subst h
  exact proto_takeExact_append xs ys

private theorem isEmpty_eq_false_of_length_eq_32 {xs : Bytes} (h : xs.length = 32) :
    xs.isEmpty = false := by
  cases xs with
  | nil => cases h
  | cons _ _ => rfl

private theorem encodeBytesField_1_of_length_32 {xs : Bytes} (h : xs.length = 32) :
    Proto.encodeBytesField 1#32 xs = [0x0a#8, 0x20#8] ++ xs := by
  simp only [Proto.encodeBytesField, isEmpty_eq_false_of_length_eq_32 h, Bool.false_eq_true,
    ↓reduceIte, Proto.encodeBytesUncond, h]
  rfl

private theorem encodeBytesField_2_of_length_32 {xs : Bytes} (h : xs.length = 32) :
    Proto.encodeBytesField 2#32 xs = [0x12#8, 0x20#8] ++ xs := by
  simp only [Proto.encodeBytesField, isEmpty_eq_false_of_length_eq_32 h, Bool.false_eq_true,
    ↓reduceIte, Proto.encodeBytesUncond, h]
  rfl

private theorem protoAuthenticator_encodeRaw_of_lengths (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) :
    ProtoAuthenticator.encodeRaw auth.intoPb =
      0x0a#8 :: 0x20#8 :: (auth.rootKey ++ (0x12#8 :: 0x20#8 :: auth.macKey)) := by
  unfold ProtoAuthenticator.encodeRaw Authenticator.intoPb
  rw [encodeBytesField_1_of_length_32 hrk, encodeBytesField_2_of_length_32 hmk]
  simp only [List.cons_append, List.nil_append]

private theorem protoAuthenticator_encodeRaw_length (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) :
    (ProtoAuthenticator.encodeRaw auth.intoPb).length = 68 := by
  rw [protoAuthenticator_encodeRaw_of_lengths auth hrk hmk]
  simp only [List.length_cons, List.length_append, hrk, hmk]

private theorem proto_mergeBytes_32 {xs : Bytes} (h : xs.length = 32) (after : Bytes) :
    Proto.mergeBytes .lengthDelimited (0x20#8 :: (xs ++ after)) = .ok (xs, after) := by
  unfold Proto.mergeBytes Proto.checkWireType
  have hd : Proto.decodeVarint (0x20#8 :: (xs ++ after)) = .ok (32#64, xs ++ after) := rfl
  dsimp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  rw [hd]; dsimp only
  exact proto_takeExact_of_length h after

private theorem mergeFieldsLoop_step {M : Type}
    (mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes))
    (fuel : Nat) (m m' : M) (b : BitVec 8) (rest rest' : Bytes) (depth : Nat)
    (tag : BitVec 32) (wt : WireType)
    (hkey : Proto.decodeKey (b :: rest) = .ok ((tag, wt), rest))
    (hfield : mergeField m tag wt rest depth = .ok (m', rest')) :
    Proto.mergeFieldsLoop mergeField (fuel + 1) m (b :: rest) depth =
      Proto.mergeFieldsLoop mergeField fuel m' rest' depth := by
  conv_lhs => unfold Proto.mergeFieldsLoop
  dsimp only [Bind.bind, Except.bind]
  rw [hkey]; dsimp only
  rw [hfield]

private theorem protoAuthenticator_mergeFieldsLoop (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) (depth : Nat) :
    Proto.mergeFieldsLoop ProtoAuthenticator.mergeField 68 default
      (ProtoAuthenticator.encodeRaw auth.intoPb) depth = .ok auth.intoPb := by
  rw [protoAuthenticator_encodeRaw_of_lengths auth hrk hmk]
  have hf1 : ProtoAuthenticator.mergeField default 1#32 .lengthDelimited
      (0x20#8 :: (auth.rootKey ++ (0x12#8 :: 0x20#8 :: auth.macKey))) depth =
      .ok ({ rootKey := auth.rootKey, macKey := [] }, 0x12#8 :: 0x20#8 :: auth.macKey) := by
    unfold ProtoAuthenticator.mergeField
    dsimp only [beq_self_eq_true, ↓reduceIte, Bind.bind, Except.bind]
    rw [proto_mergeBytes_32 hrk]; rfl
  have hf2 : ProtoAuthenticator.mergeField { rootKey := auth.rootKey, macKey := [] } 2#32 .lengthDelimited
      (0x20#8 :: (auth.macKey ++ [])) depth =
      .ok (auth.intoPb, []) := by
    unfold ProtoAuthenticator.mergeField
    dsimp only [ Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
    rw [proto_mergeBytes_32 hmk]; rfl
  rw [mergeFieldsLoop_step _ 67 _ _ 0x0a#8 _ _ depth 1#32 .lengthDelimited rfl hf1]
  rw [← List.append_nil auth.macKey]
  rw [mergeFieldsLoop_step _ 66 _ _ 0x12#8 _ _ depth 2#32 .lengthDelimited rfl hf2]
  rfl

private theorem proto_mergeMessage_of_length {M : Type}
    (mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes))
    (m m' : M) (raw after : Bytes) (n depth' : Nat) (b : BitVec 8)
    (hb : Proto.decodeVarint (b :: (raw ++ after)) = .ok (BitVec.ofNat 64 n, raw ++ after))
    (hn : (BitVec.ofNat 64 n).toNat = n)
    (hlen : raw.length = n)
    (hloop : Proto.mergeFieldsLoop mergeField n m raw depth' = .ok m') :
    Proto.mergeMessage mergeField .lengthDelimited m (b :: (raw ++ after)) (depth' + 1) =
      .ok (m', after) := by
  unfold Proto.mergeMessage Proto.checkWireType
  dsimp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  rw [hb]; dsimp only
  rw [hn, proto_takeExact_of_length hlen after]; dsimp only
  rw [hlen, hloop]; rfl

private theorem proto_mergeOptMessage_of_length {M : Type} [Inhabited M]
    (mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes))
    (m' : M) (raw after : Bytes) (n depth' : Nat) (b : BitVec 8)
    (hb : Proto.decodeVarint (b :: (raw ++ after)) = .ok (BitVec.ofNat 64 n, raw ++ after))
    (hn : (BitVec.ofNat 64 n).toNat = n)
    (hlen : raw.length = n)
    (hloop : Proto.mergeFieldsLoop mergeField n default raw depth' = .ok m') :
    Proto.mergeOptMessage mergeField .lengthDelimited none (b :: (raw ++ after)) (depth' + 1) =
      .ok (some m', after) := by
  unfold Proto.mergeOptMessage Option.getD
  rw [proto_mergeMessage_of_length mergeField default m' raw after n depth' b hb hn hlen hloop]
  rfl

private def vnInitPb (dir : Direction) (k : Bytes) : VersionNegotiationPB :=
  { authKey := k, direction := dir.toI32, minVersion := Version.v1.toI32,
    chainParams := some DEFAULT_CHAIN_PARAMS.intoPb }

private abbrev vnTailA2B : Bytes := [0x18#8, 0x01#8, 0x22#8, 0x00#8]

private theorem vnInitPb_a2b_encodeRaw {k : Bytes} (hk : k.length = 32) :
    VersionNegotiationPB.encodeRaw (vnInitPb .a2b k) = 0x0a#8 :: 0x20#8 :: (k ++ vnTailA2B) := by
  unfold VersionNegotiationPB.encodeRaw vnInitPb; rw [encodeBytesField_1_of_length_32 hk]
  change ([0x0a#8, 0x20#8] ++ k) ++ [] ++ [0x18#8, 0x01#8] ++ [0x22#8, 0x00#8] =
    0x0a#8 :: 0x20#8 :: (k ++ vnTailA2B)
  simp only [List.append_assoc, List.cons_append, List.nil_append]

private theorem vnInitPb_a2b_encodeRaw_length {k : Bytes} (hk : k.length = 32) :
    (VersionNegotiationPB.encodeRaw (vnInitPb .a2b k)).length = 38 := by
  rw [vnInitPb_a2b_encodeRaw hk]; simp only [List.length_cons, List.length_append, List.length_nil, hk]

private theorem vnInitPb_a2b_mergeFieldsLoop {k : Bytes} (hk : k.length = 32) (depth : Nat) :
    Proto.mergeFieldsLoop VersionNegotiationPB.mergeField 38 default
      (VersionNegotiationPB.encodeRaw (vnInitPb .a2b k)) (depth + 1) = .ok (vnInitPb .a2b k) := by
  rw [vnInitPb_a2b_encodeRaw hk]
  have hf1 : VersionNegotiationPB.mergeField default 1#32 .lengthDelimited
      (0x20#8 :: (k ++ vnTailA2B)) (depth + 1) =
      .ok ({ (default : VersionNegotiationPB) with authKey := k }, vnTailA2B) := by
    unfold VersionNegotiationPB.mergeField
    dsimp only [beq_self_eq_true, ↓reduceIte, Bind.bind, Except.bind]; rw [proto_mergeBytes_32 hk]; rfl
  rw [mergeFieldsLoop_step _ 37 _ _ 0x0a#8 _ _ (depth + 1) 1#32 .lengthDelimited rfl hf1]; rfl

private def ucKeysUnsampledPb (auth : Authenticator) : V1State.Unchunked.KeysUnsampled :=
  { epoch := 1#64, auth := some auth.intoPb }

private theorem ucKeysUnsampledPb_encodeRaw (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) :
    V1State.Unchunked.KeysUnsampled.encodeRaw (ucKeysUnsampledPb auth) =
      0x08#8 :: 0x01#8 :: 0x12#8 :: 0x44#8 :: (ProtoAuthenticator.encodeRaw auth.intoPb ++ []) := by
  unfold V1State.Unchunked.KeysUnsampled.encodeRaw ucKeysUnsampledPb
    Proto.encodeOptMessage Proto.encodeMessage; dsimp only
  rw [protoAuthenticator_encodeRaw_length auth hrk hmk, List.append_nil]; rfl

private theorem ucKeysUnsampledPb_encodeRaw_length (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) :
    (V1State.Unchunked.KeysUnsampled.encodeRaw (ucKeysUnsampledPb auth)).length = 72 := by
  rw [ucKeysUnsampledPb_encodeRaw auth hrk hmk, List.append_nil]
  simp only [List.length_cons, protoAuthenticator_encodeRaw_length auth hrk hmk]

private theorem ucKeysUnsampledPb_mergeFieldsLoop (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) (depth : Nat) :
    Proto.mergeFieldsLoop V1State.Unchunked.KeysUnsampled.mergeField 72 default
      (V1State.Unchunked.KeysUnsampled.encodeRaw (ucKeysUnsampledPb auth)) (depth + 1) =
        .ok (ucKeysUnsampledPb auth) := by
  rw [ucKeysUnsampledPb_encodeRaw auth hrk hmk]
  have hf2 : V1State.Unchunked.KeysUnsampled.mergeField { epoch := 1#64, auth := none } 2#32 .lengthDelimited
      (0x44#8 :: (ProtoAuthenticator.encodeRaw auth.intoPb ++ [])) (depth + 1) =
      .ok (ucKeysUnsampledPb auth, []) := by
    unfold V1State.Unchunked.KeysUnsampled.mergeField
    dsimp only [Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, Bind.bind, Except.bind]
    rw [proto_mergeOptMessage_of_length ProtoAuthenticator.mergeField auth.intoPb
      (ProtoAuthenticator.encodeRaw auth.intoPb) [] 68 depth 0x44#8 rfl rfl
      (protoAuthenticator_encodeRaw_length auth hrk hmk)
      (protoAuthenticator_mergeFieldsLoop auth hrk hmk depth)]; rfl
  rw [mergeFieldsLoop_step _ 71 _ { epoch := 1#64, auth := none } 0x08#8 _
    (0x12#8 :: 0x44#8 :: (ProtoAuthenticator.encodeRaw auth.intoPb ++ [])) (depth + 1) 1#32 .varint rfl rfl]
  rw [mergeFieldsLoop_step _ 70 _ _ 0x12#8 _ _ (depth + 1) 2#32 .lengthDelimited rfl hf2]; rfl

private def v1StateA0Pb (auth : Authenticator) : V1State :=
  { innerState := some (.keysUnsampled { uc := some (ucKeysUnsampledPb auth) }) }

private theorem chunkedKeysUnsampledPb_encodeRaw (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) :
    V1State.Chunked.KeysUnsampled.encodeRaw { uc := some (ucKeysUnsampledPb auth) } =
      0x0a#8 :: 0x48#8 :: (V1State.Unchunked.KeysUnsampled.encodeRaw (ucKeysUnsampledPb auth) ++ []) := by
  unfold V1State.Chunked.KeysUnsampled.encodeRaw Proto.encodeOptMessage Proto.encodeMessage; dsimp only
  rw [ucKeysUnsampledPb_encodeRaw_length auth hrk hmk, List.append_nil]; rfl

private theorem chunkedKeysUnsampledPb_encodeRaw_length (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) :
    (V1State.Chunked.KeysUnsampled.encodeRaw { uc := some (ucKeysUnsampledPb auth) }).length = 74 := by
  rw [chunkedKeysUnsampledPb_encodeRaw auth hrk hmk, List.append_nil]
  simp only [List.length_cons, ucKeysUnsampledPb_encodeRaw_length auth hrk hmk]

private theorem chunkedKeysUnsampledPb_mergeFieldsLoop (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) (depth : Nat) :
    Proto.mergeFieldsLoop V1State.Chunked.KeysUnsampled.mergeField 74 default
      (V1State.Chunked.KeysUnsampled.encodeRaw { uc := some (ucKeysUnsampledPb auth) }) (depth + 2) =
        .ok { uc := some (ucKeysUnsampledPb auth) } := by
  rw [chunkedKeysUnsampledPb_encodeRaw auth hrk hmk]
  have hf1 : V1State.Chunked.KeysUnsampled.mergeField default 1#32 .lengthDelimited
      (0x48#8 :: (V1State.Unchunked.KeysUnsampled.encodeRaw (ucKeysUnsampledPb auth) ++ [])) (depth + 2) =
      .ok ({ uc := some (ucKeysUnsampledPb auth) }, []) := by
    change V1State.Chunked.KeysUnsampled.mergeField { uc := none } 1#32 .lengthDelimited _ ((depth + 1) + 1) = _
    unfold V1State.Chunked.KeysUnsampled.mergeField
    dsimp only [beq_self_eq_true, ↓reduceIte, Bind.bind, Except.bind]
    rw [proto_mergeOptMessage_of_length V1State.Unchunked.KeysUnsampled.mergeField (ucKeysUnsampledPb auth)
      (V1State.Unchunked.KeysUnsampled.encodeRaw (ucKeysUnsampledPb auth)) [] 72 (depth + 1) 0x48#8 rfl rfl
      (ucKeysUnsampledPb_encodeRaw_length auth hrk hmk)
      (ucKeysUnsampledPb_mergeFieldsLoop auth hrk hmk depth)]; rfl
  rw [mergeFieldsLoop_step _ 73 _ _ 0x0a#8 _ _ (depth + 2) 1#32 .lengthDelimited rfl hf1]; rfl

private theorem v1State_mergeField_1 (bs : Bytes) (depth : Nat)
    (v : V1State.Chunked.KeysUnsampled) (bs' : Bytes)
    (h : Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField .lengthDelimited default bs depth = .ok (v, bs')) :
    V1State.mergeField default 1#32 .lengthDelimited bs depth =
    .ok ({ innerState := some (.keysUnsampled v) }, bs') := by
  unfold V1State.mergeField V1State.InnerState.merge
  change (do
    let (is', bs'') ← (do
      let (v, bs') ← Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField .lengthDelimited default bs depth
      Except.ok (some (V1State.InnerState.keysUnsampled v), bs'))
    Except.ok ({ innerState := is' : V1State }, bs'')) = _
  rw [h]; rfl

private theorem pqRatchetState_mergeField_3 (vn : Option VersionNegotiationPB)
    (bs : Bytes) (depth : Nat) (v : V1State) (bs' : Bytes)
    (h : Proto.mergeMessage V1State.mergeField .lengthDelimited default bs depth = .ok (v, bs')) :
    PqRatchetState.mergeField { versionNegotiation := vn, chain := none, inner := none }
      3#32 .lengthDelimited bs depth =
    .ok ({ versionNegotiation := vn, chain := none, inner := some (.v1 v) }, bs') := by
  unfold PqRatchetState.mergeField PqRatchetState.Inner.merge
  change (do
    let (i', bs'') ← (do
      let (v, bs') ← Proto.mergeMessage V1State.mergeField .lengthDelimited default bs depth
      Except.ok (some (PqRatchetState.Inner.v1 v), bs'))
    Except.ok ({ versionNegotiation := vn, chain := none, inner := i' : PqRatchetState }, bs'')) = _
  rw [h]; rfl

private theorem v1StateA0Pb_encodeRaw (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) :
    V1State.encodeRaw (v1StateA0Pb auth) =
      0x0a#8 :: 0x4a#8 :: (V1State.Chunked.KeysUnsampled.encodeRaw { uc := some (ucKeysUnsampledPb auth) } ++ []) := by
  unfold V1State.encodeRaw v1StateA0Pb V1State.InnerState.encode Proto.encodeMessage; dsimp only
  rw [chunkedKeysUnsampledPb_encodeRaw_length auth hrk hmk, List.append_nil]; rfl

private theorem v1StateA0Pb_encodeRaw_length (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) :
    (V1State.encodeRaw (v1StateA0Pb auth)).length = 76 := by
  rw [v1StateA0Pb_encodeRaw auth hrk hmk, List.append_nil]
  simp only [List.length_cons, chunkedKeysUnsampledPb_encodeRaw_length auth hrk hmk]

private theorem v1StateA0Pb_mergeFieldsLoop (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) (depth : Nat) :
    Proto.mergeFieldsLoop V1State.mergeField 76 default
      (V1State.encodeRaw (v1StateA0Pb auth)) (depth + 3) = .ok (v1StateA0Pb auth) := by
  rw [v1StateA0Pb_encodeRaw auth hrk hmk]
  have hf1 := v1State_mergeField_1
    (0x4a#8 :: (V1State.Chunked.KeysUnsampled.encodeRaw { uc := some (ucKeysUnsampledPb auth) } ++ []))
    (depth + 3) { uc := some (ucKeysUnsampledPb auth) } []
    (proto_mergeMessage_of_length V1State.Chunked.KeysUnsampled.mergeField default
      { uc := some (ucKeysUnsampledPb auth) }
      (V1State.Chunked.KeysUnsampled.encodeRaw { uc := some (ucKeysUnsampledPb auth) }) [] 74 (depth + 2) 0x4a#8 rfl rfl
      (chunkedKeysUnsampledPb_encodeRaw_length auth hrk hmk)
      (chunkedKeysUnsampledPb_mergeFieldsLoop auth hrk hmk depth))
  rw [mergeFieldsLoop_step _ 75 _ _ 0x0a#8 _ _ (depth + 3) 1#32 .lengthDelimited rfl hf1]; rfl

private def pqRatchetStateA0 (k : Bytes) (auth : Authenticator) : PqRatchetState :=
  { versionNegotiation := some (vnInitPb .a2b k), chain := none, inner := some (.v1 (v1StateA0Pb auth)) }

private theorem pqRatchetStateA0_encode {k : Bytes} (hk : k.length = 32) (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) :
    PqRatchetState.encode (pqRatchetStateA0 k auth) =
      0x0a#8 :: 0x26#8 :: (VersionNegotiationPB.encodeRaw (vnInitPb .a2b k) ++
        (0x1a#8 :: 0x4c#8 :: (V1State.encodeRaw (v1StateA0Pb auth) ++ []))) := by
  unfold PqRatchetState.encode PqRatchetState.encodeRaw pqRatchetStateA0
    PqRatchetState.Inner.encode Proto.encodeOptMessage Proto.encodeMessage; dsimp only
  rw [vnInitPb_a2b_encodeRaw_length hk, v1StateA0Pb_encodeRaw_length auth hrk hmk]
  change ([0x0a#8, 0x26#8] ++ VersionNegotiationPB.encodeRaw (vnInitPb .a2b k)) ++ [] ++
    ([0x1a#8, 0x4c#8] ++ V1State.encodeRaw (v1StateA0Pb auth)) =
    0x0a#8 :: 0x26#8 :: (VersionNegotiationPB.encodeRaw (vnInitPb .a2b k) ++
      (0x1a#8 :: 0x4c#8 :: (V1State.encodeRaw (v1StateA0Pb auth) ++ [])))
  simp only [List.cons_append, List.nil_append, List.append_nil]

private theorem pqRatchetStateA0_encode_length {k : Bytes} (hk : k.length = 32) (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) :
    (PqRatchetState.encode (pqRatchetStateA0 k auth)).length = 118 := by
  rw [pqRatchetStateA0_encode hk auth hrk hmk, List.append_nil]
  simp only [List.length_cons, List.length_append, vnInitPb_a2b_encodeRaw_length hk,
    v1StateA0Pb_encodeRaw_length auth hrk hmk]

private theorem proto_decodeState_pqRatchetStateA0 {k : Bytes} (hk : k.length = 32) (auth : Authenticator)
    (hrk : auth.rootKey.length = 32) (hmk : auth.macKey.length = 32) :
    Proto.decodeState (Proto.encodeState (pqRatchetStateA0 k auth)) = .ok (pqRatchetStateA0 k auth) := by
  unfold Proto.decodeState PqRatchetState.decode Proto.decodeTopLevelMessage Proto.mergeTopLevelMessage Proto.encodeState Proto.RECURSION_LIMIT
  rw [pqRatchetStateA0_encode_length hk auth hrk hmk, pqRatchetStateA0_encode hk auth hrk hmk]
  have hf1 : PqRatchetState.mergeField default 1#32 .lengthDelimited
      (0x26#8 :: (VersionNegotiationPB.encodeRaw (vnInitPb .a2b k) ++
        (0x1a#8 :: 0x4c#8 :: (V1State.encodeRaw (v1StateA0Pb auth) ++ [])))) 100 =
      .ok ({ versionNegotiation := some (vnInitPb .a2b k), chain := none, inner := none },
        0x1a#8 :: 0x4c#8 :: (V1State.encodeRaw (v1StateA0Pb auth) ++ [])) := by
    change PqRatchetState.mergeField { versionNegotiation := none, chain := none, inner := none } 1#32 .lengthDelimited _ (99 + 1) = _
    unfold PqRatchetState.mergeField
    dsimp only [beq_self_eq_true, ↓reduceIte, Bind.bind, Except.bind]
    rw [proto_mergeOptMessage_of_length VersionNegotiationPB.mergeField (vnInitPb .a2b k)
      (VersionNegotiationPB.encodeRaw (vnInitPb .a2b k))
      (0x1a#8 :: 0x4c#8 :: (V1State.encodeRaw (v1StateA0Pb auth) ++ []))
      38 99 0x26#8 rfl rfl (vnInitPb_a2b_encodeRaw_length hk)
      (vnInitPb_a2b_mergeFieldsLoop hk 98)]; rfl
  have hf3 := pqRatchetState_mergeField_3 (some (vnInitPb .a2b k))
    (0x4c#8 :: (V1State.encodeRaw (v1StateA0Pb auth) ++ [])) 100 (v1StateA0Pb auth) []
    (proto_mergeMessage_of_length V1State.mergeField default (v1StateA0Pb auth)
      (V1State.encodeRaw (v1StateA0Pb auth)) [] 76 99 0x4c#8 rfl rfl
      (v1StateA0Pb_encodeRaw_length auth hrk hmk)
      (v1StateA0Pb_mergeFieldsLoop auth hrk hmk 96))
  rw [mergeFieldsLoop_step _ 117 _ _ 0x0a#8 _ _ 100 1#32 .lengthDelimited rfl hf1]
  rw [mergeFieldsLoop_step _ 116 _ _ 0x1a#8 _ _ 100 3#32 .lengthDelimited rfl hf3]; rfl

private theorem spqrInitB_a2b_eq (F : ShaCompress) (K : MlKem) (mac : HmacFn) (k : Bytes) :
    spqrInitB F K mac k [0#8] =
      Proto.encodeState (pqRatchetStateA0 k (Authenticator.new F k 1#64)) := rfl

private theorem decodeState_spqrInitB_a2b (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    {k : Bytes} (hk : k.length = 32) :
    decodeState (spqrDepsWithMac F K mac) (spqrInitB F K mac k [0#8]) =
      .ok (pqRatchetStateToPb (pqRatchetStateA0 k (Authenticator.new F k 1#64))) := by
  have ⟨hrk, hmk⟩ := authenticator_new_lengths F k 1#64
  rw [spqrInitB_a2b_eq]
  generalize Authenticator.new F k 1#64 = auth at hrk hmk ⊢
  unfold decodeState
  have hemp : (Proto.encodeState (pqRatchetStateA0 k auth)).isEmpty = false := by
    unfold Proto.encodeState
    rw [pqRatchetStateA0_encode hk auth hrk hmk]
    rfl
  rw [hemp]
  dsimp only [Bool.false_eq_true, ↓reduceIte, spqrDepsWithMac]
  rw [proto_decodeState_pqRatchetStateA0 hk auth hrk hmk]; rfl

private def firstA2BMk (F : ShaCompress) (k : Bytes) : Bytes :=
  let genr8r := spqrHkdfWith F (List.replicate 32 0#8) k chainStartInfo 96
  let next0 := (genr8r.drop 32).take 32
  let genNext := spqrHkdfWith F (List.replicate 32 0#8) next0 (toBEBytes 4 1#32 ++ chainNextInfo) 64
  (genNext.drop 32).take 32

private theorem firstA2BMk_length (F : ShaCompress) (k : Bytes) :
    (firstA2BMk F k).length = 32 := by
  simp [firstA2BMk, length_spqrHkdfWith]

private theorem ced0_a2b_next_length (F : ShaCompress) (k : Bytes) :
    ((spqrHkdfWith F (List.replicate 32 0#8) k chainStartInfo 96).drop 32 |>.take 32).length = 32 := by
  simp [length_spqrHkdfWith]

private theorem ced0_a2b_nextKeyInternal (F : ShaCompress) (k : Bytes) :
    ChainEpochDirection.nextKeyInternal (spqrHkdfWith F)
      ((spqrHkdfWith F (List.replicate 32 0#8) k chainStartInfo 96).drop 32 |>.take 32) 0#32 =
      .ok ((spqrHkdfWith F (List.replicate 32 0#8)
        ((spqrHkdfWith F (List.replicate 32 0#8) k chainStartInfo 96).drop 32 |>.take 32)
        (toBEBytes 4 1#32 ++ chainNextInfo) 64).take 32, 1#32, (1#32, firstA2BMk F k)) := by
  unfold ChainEpochDirection.nextKeyInternal firstA2BMk
  rw [ced0_a2b_next_length F k]
  rfl

private def chain0 (F : ShaCompress) (k : Bytes) (dir : Direction) : Chain :=
  let genr8r := spqrHkdfWith F (List.replicate 32 0#8) k chainStartInfo 96
  { dir := dir
    currentEpoch := 0#64
    sendEpoch := 0#64
    links := [{ send := Chain.cedForDirection genr8r dir
                recv := Chain.cedForDirection genr8r dir.switch }]
    nextRoot := genr8r.take 32
    params := DEFAULT_CHAIN_PARAMS.intoPb }

private theorem spqrChainKeyB_a2b (F : ShaCompress) (k : Bytes) (idx : BitVec 32) :
    spqrChainKeyB F k [0#8] (spqrLeBytes4 idx) =
      match (chain0 F k .b2a).recvKey (spqrHkdfWith F) 0#64 idx with
      | .ok (_, key) => key
      | .error _ => [] := by
  unfold spqrChainKeyB
  rw [show spqrDirOfParams? [0#8] = some .a2b from rfl, spqrIdxOfBytes?_spqrLeBytes4]
  rfl

private theorem keyAdvanceLoop_zero_one (F : ShaCompress) (next0 : Bytes) :
    ChainEpochDirection.keyAdvanceLoop (spqrHkdfWith F)
      { ctr := 0#32, next := next0, prev := KeyHistory.new } 1#32 DEFAULT_CHAIN_PARAMS.intoPb =
      .ok { ctr := 0#32, next := next0, prev := KeyHistory.new } := by
  unfold ChainEpochDirection.keyAdvanceLoop
  rfl

private theorem chain0_b2a_recvKey_one (F : ShaCompress) (k : Bytes) :
    ∃ c', (chain0 F k .b2a).recvKey (spqrHkdfWith F) 0#64 1#32 = .ok (c', firstA2BMk F k) := by
  let next0 := (spqrHkdfWith F (List.replicate 32 0#8) k chainStartInfo 96).drop 32 |>.take 32
  have hkey :
      ChainEpochDirection.key (spqrHkdfWith F)
        { ctr := 0#32, next := next0, prev := KeyHistory.new } 1#32 DEFAULT_CHAIN_PARAMS.intoPb =
      .ok ({ ctr := 1#32
             next := (spqrHkdfWith F (List.replicate 32 0#8) next0 (toBEBytes 4 1#32 ++ chainNextInfo) 64).take 32
             prev := KeyHistory.new }, firstA2BMk F k) := by
    unfold ChainEpochDirection.key
    have h1 : ¬ (1#32 < 0#32) := by decide
    have h2 : (1#32 == 0#32) = false := rfl
    have h3 : ¬ (1#32 - 0#32 > DEFAULT_CHAIN_PARAMS.intoPb.maxJumpOrDefault) := by decide
    have h4 : ¬ ((0#32).toNat + DEFAULT_CHAIN_PARAMS.intoPb.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) := by decide
    have h5 : ¬ (1#32 > 0#32 + DEFAULT_CHAIN_PARAMS.intoPb.maxOooKeysOrDefault) := by decide
    simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
    rw [keyAdvanceLoop_zero_one F next0]
    dsimp only [KeyHistory.gc, KeyHistory.new, ChainResult.ofPanic, Pure.pure, Except.pure, ↓reduceIte]
    rw [ced0_a2b_nextKeyInternal F k]
    rfl
  unfold Chain.recvKey
  have h0 : (0#64 == 0#64 && 1#32 == 0#32) = false := rfl
  have hep : (chain0 F k .b2a).epochIdx 0#64 = .ok 0 := by
    unfold Chain.epochIdx chain0
    simp
  have hlink : (chain0 F k .b2a).links[0]? =
      some { send := Chain.cedForDirection (spqrHkdfWith F (List.replicate 32 0#8) k chainStartInfo 96) .b2a
             recv := { ctr := 0#32, next := next0, prev := KeyHistory.new } } := rfl
  have hparams : (chain0 F k .b2a).params = DEFAULT_CHAIN_PARAMS.intoPb := rfl
  simp only [h0, hep, Bool.false_eq_true, ↓reduceIte, ChainResult.ofError, Bind.bind, Except.bind]
  rw [hlink]
  dsimp only
  rw [hparams, hkey]
  exact ⟨_, rfl⟩

private theorem spqrChainKeyB_a2b_one (F : ShaCompress) (k : Bytes) :
    spqrChainKeyB F k [0#8] (spqrLeBytes4 1#32) = firstA2BMk F k := by
  rw [spqrChainKeyB_a2b]
  obtain ⟨c', hc'⟩ := chain0_b2a_recvKey_one F k
  rw [hc']

private theorem firstA2BMk_isEmpty (F : ShaCompress) (k : Bytes) :
    (firstA2BMk F k).isEmpty = false := by
  rw [List.isEmpty_eq_false_iff, ← List.length_pos_iff, firstA2BMk_length]
  decide

private theorem messageKeyToSalt?_firstA2BMk (F : ShaCompress) (k : Bytes) :
    messageKeyToSalt? (some (firstA2BMk F k)) =
      some (some ⟨firstA2BMk F k, firstA2BMk_length F k⟩) := by
  simp only [messageKeyToSalt?, firstA2BMk_length, ↓reduceDIte]

private theorem msgPreamble_serialize_hdr_one (chunk : Chunk) :
    msgPreamble (Message.serialize (P := spqrPolyApi) { epoch := 1#64, payload := .hdr chunk } 1#32) =
      .ok { version := 1#8, epoch := 1#64, index := 1#32
            remaining := 1#8 :: encodeVarintLoop 10 (chunk.index.zeroExtend 64) ++ chunk.data.toList } := by
  dsimp only [Message.serialize, spqrPolyApi, encode_chunk, encode_varint,
    List.cons_append, List.nil_append]; rfl

private theorem chain0_a2b_sendKey_zero (F : ShaCompress) (k : Bytes) :
    ∃ c', (chain0 F k .a2b).sendKey (spqrHkdfWith F) 0#64 = .ok (c', (1#32, firstA2BMk F k)) := by
  let next0 := (spqrHkdfWith F (List.replicate 32 0#8) k chainStartInfo 96).drop 32 |>.take 32
  have hnk :
      ChainEpochDirection.nextKey (spqrHkdfWith F) { ctr := 0#32, next := next0, prev := KeyHistory.new } =
      .ok ({ ctr := 1#32
             next := (spqrHkdfWith F (List.replicate 32 0#8) next0 (toBEBytes 4 1#32 ++ chainNextInfo) 64).take 32
             prev := KeyHistory.new }, (1#32, firstA2BMk F k)) := by
    unfold ChainEpochDirection.nextKey
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]; rw [ced0_a2b_nextKeyInternal F k]
  unfold Chain.sendKey
  have hlt : ¬ (0#64 < (chain0 F k .a2b).sendEpoch) := by change ¬ (0#64 < 0#64); decide
  have hep : (chain0 F k .a2b).epochIdx 0#64 = .ok 0 := by unfold Chain.epochIdx chain0; simp
  have hne : ((chain0 F k .a2b).sendEpoch != 0#64) = false := rfl
  have hlink : (chain0 F k .a2b).links[0]? =
      some { send := { ctr := 0#32, next := next0, prev := KeyHistory.new }
             recv := Chain.cedForDirection (spqrHkdfWith F (List.replicate 32 0#8) k chainStartInfo 96) .b2a } := rfl
  simp only [hlt, hep, hne, Bool.false_eq_true, ↓reduceIte, ChainResult.ofError, Bind.bind, Except.bind]
  rw [hlink]; dsimp only [ChainResult.ofPanic, Bind.bind, Except.bind]; rw [hnk]; exact ⟨_, rfl⟩

private theorem sendAfterStates_pqRatchetStateA0 (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (k : Bytes) (auth : Authenticator) (chunk : Chunk)
    (st1 : States spqrPolyApi (spqrAuthApiWithMac F mac)) :
    ∃ newStateBytes,
      sendAfterStates (spqrDepsWithMac F K mac) (spqrHkdfWith F)
        (pqRatchetStateToPb (pqRatchetStateA0 k auth))
        { epoch := 1#64, payload := .hdr chunk } none st1 =
      .ok { state := newStateBytes
            msg := Message.serialize (P := spqrPolyApi) { epoch := 1#64, payload := .hdr chunk } 1#32
            key := some (firstA2BMk F k) } := by
  obtain ⟨c2, hc2⟩ := chain0_a2b_sendKey_zero F k
  unfold sendAfterStates
  have hchain : (pqRatchetStateToPb (pqRatchetStateA0 k auth)).chain = none := rfl
  have hvn : (pqRatchetStateToPb (pqRatchetStateA0 k auth)).versionNegotiation = some (vnInitPb .a2b k) := rfl
  have hslt : (Version.v0.toI32.slt (vnInitPb .a2b k).minVersion) = true := rfl
  have hcf : chainFromVersionNegotiation (spqrHkdfWith F) (vnInitPb .a2b k) = .ok (chain0 F k .a2b) := rfl
  have hep : (spqrDepsWithMac F K mac).msgEpoch { epoch := 1#64, payload := .hdr chunk } = 1#64 := rfl
  have hser : (spqrDepsWithMac F K mac).msgSerialize { epoch := 1#64, payload := .hdr chunk } 1#32 =
    Message.serialize (P := spqrPolyApi) { epoch := 1#64, payload := .hdr chunk } 1#32 := rfl
  have hep0 : (1#64 == 0#64) = false := rfl
  have hsub : (1#64 - 1#64 : BitVec 64) = 0#64 := rfl
  simp only [hchain, hvn, hslt, hcf, hep, hep0, hsub, hc2, hser, firstA2BMk_isEmpty F k,
    Bool.false_eq_true, ↓reduceIte, SpqrApiResult.ofError, SpqrApiResult.ofChainResult,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨_, rfl⟩

private theorem send_spqrInitB_a2b (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (k c : Bytes) (hk : k.length = 32) :
    (send (spqrDepsWithMac F K mac) (spqrHkdfWith F) (spqrInitB F K mac k [0#8]) c).1 =
      let auth := Authenticator.new F k 1#64
      match Chunked.SendEk.KeysUnsampled.send_hdr_chunk K spqrPolyApi
          ({ uc := { epoch := 1#64, auth := auth } } :
            Chunked.SendEk.KeysUnsampled (spqrAuthApiWithMac F mac)) c with
      | .error _ => .error (.panic .v1)
      | .ok (state', chunk, _) =>
        sendAfterStates (spqrDepsWithMac F K mac) (spqrHkdfWith F)
          (pqRatchetStateToPb (pqRatchetStateA0 k auth))
          { epoch := 1#64, payload := .hdr chunk } none (.keysSampled state') := by
  unfold send; rw [decodeState_spqrInitB_a2b F K mac hk]
  generalize Authenticator.new F k 1#64 = auth
  generalize sendAfterStates (spqrDepsWithMac F K mac) (spqrHkdfWith F)
    (pqRatchetStateToPb (pqRatchetStateA0 k auth)) = afterFn
  have hinner : (pqRatchetStateToPb (pqRatchetStateA0 k auth)).inner = some (v1StateA0Pb auth) := rfl
  have hfrom : (spqrDepsWithMac F K mac).statesFromPb (v1StateA0Pb auth) =
      .ok (.keysUnsampled { uc := { epoch := 1#64, auth := auth } }) := rfl
  dsimp only; rw [hinner]; dsimp only; rw [hfrom]
  dsimp only [spqrDepsWithMac, States.send, StatesResult.ofPanic, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases Chunked.SendEk.KeysUnsampled.send_hdr_chunk K spqrPolyApi
      ({ uc := { epoch := 1#64, auth := auth } } :
        Chunked.SendEk.KeysUnsampled (spqrAuthApiWithMac F mac)) c with
  | error e => cases e <;> rfl
  | ok val => rcases val with ⟨state', chunk, tape'⟩; rfl

/-- If `spqrSendB` succeeds on `spqrInitB F K mac k [0#8]` with `k.length = 32`, the returned key
equals `spqrChainKeyB F k [0#8] (spqrLeBytes4 1#32)` (independent of `c` and `mac`) and
`msgPreamble msg` has `index = 1#32`. -/
theorem spqrSendB_fresh_first_of_some (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (k c st' key msg : Bytes) (hk : k.length = 32)
    (hsend : spqrSendB F K mac (spqrInitB F K mac k [0#8]) c = some (st', key, msg)) :
    key = spqrChainKeyB F k [0#8] (spqrLeBytes4 1#32) ∧
    ∃ p, msgPreamble msg = .ok p ∧ p.index = 1#32 := by
  unfold spqrSendB spqrV1WithMac toSpqrModel at hsend
  dsimp only at hsend; rw [send_spqrInitB_a2b F K mac k c hk] at hsend
  generalize Authenticator.new F k 1#64 = auth at hsend; dsimp only at hsend
  cases hhdr : Chunked.SendEk.KeysUnsampled.send_hdr_chunk K spqrPolyApi
      ({ uc := { epoch := 1#64, auth := auth } } : Chunked.SendEk.KeysUnsampled (spqrAuthApiWithMac F mac)) c with
  | error p => rw [hhdr] at hsend; nomatch hsend
  | ok val =>
    rcases val with ⟨state', chunk, tape'⟩
    rw [hhdr] at hsend; dsimp only at hsend
    obtain ⟨newStateBytes, hafter⟩ := sendAfterStates_pqRatchetStateA0 F K mac k auth chunk (.keysSampled state')
    rw [hafter] at hsend; dsimp only at hsend
    rw [messageKeyToSalt?_firstA2BMk F k] at hsend; dsimp only at hsend
    injection hsend with htuple
    rcases Prod.mk.inj htuple with ⟨_, htuple2⟩
    rcases Prod.mk.inj htuple2 with ⟨hkey, hmsg⟩
    subst hkey hmsg
    refine ⟨(spqrChainKeyB_a2b_one F k).symm, _, msgPreamble_serialize_hdr_one chunk, rfl⟩

end Symbolic.Swarm.SHARED.SpqrBytes
