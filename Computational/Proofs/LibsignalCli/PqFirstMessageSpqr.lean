/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSpqrWindowHonest
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhCorrectModel
import LibsignalBinary.Proofs.SpqrV1.InitFacts
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs

/-!
# SPQR V1 First-Message Roundtrip Helpers

Proves protobuf state roundtrips, first-chunk polynomial and wire roundtrips, panic-freedom, and
the end-to-end SPQR V1 first-message send/receive step (`spqrPq_firstMessage_send_recv`) used by
`PqCliFirstMessageRoundtrip`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.FirstMessage

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

private def expandList : Nat → Bytes → Bytes
  | 0, _ => []
  | n + 1, l => l.headD 0#8 :: expandList n l.tail

private theorem expandList_eq {n : Nat} {l : Bytes} (h : l.length = n) :
    l = expandList n l := by
  induction n generalizing l with
  | zero =>
    cases l with
    | nil => rfl
    | cons _ _ => contradiction
  | succ n ih =>
    cases l with
    | nil => contradiction
    | cons x xs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      exact congrArg (x :: ·) (ih h)

private def initPbA (ak rk mk : Bytes) :
    LibsignalSpqrV1.PqRatchetStatePB LibsignalSpqrV1.V1State :=
  { inner := some { innerState := some (.keysUnsampled
      { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } }) }
    versionNegotiation := some {
      authKey := ak, direction := 0#32, minVersion := 1#32,
      chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } }
    chain := none }

private def initPd0 : LibsignalSpqrV1.PolynomialDecoder :=
  { ptsNeeded := 48#32, polys := 16#32, pts := List.replicate 16 [], isComplete := false }

private def initPbB (ak rk mk : Bytes) :
    LibsignalSpqrV1.PqRatchetStatePB LibsignalSpqrV1.V1State :=
  { inner := some { innerState := some (.noHeaderReceived {
      uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } }
      receivingHdr := some initPd0 }) }
    versionNegotiation := some {
      authKey := ak, direction := 1#32, minVersion := 1#32,
      chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } }
    chain := none }

private theorem isEmpty_false_of_length_32 {bs : Bytes} (h : bs.length = 32) :
    bs.isEmpty = false := by cases bs with | nil => contradiction | cons _ _ => rfl

private theorem encodeBytesField_of_length_32 {tag : BitVec 32} {bs : Bytes} (h : bs.length = 32) :
    LibsignalSpqrV1.Proto.encodeBytesField tag bs =
      LibsignalSpqrV1.Proto.encodeKey tag .lengthDelimited ++ [0x20#8] ++ bs := by
  simp only [LibsignalSpqrV1.Proto.encodeBytesField, isEmpty_false_of_length_32 h,
    Bool.false_eq_true, ↓reduceIte, LibsignalSpqrV1.Proto.encodeBytesUncond, h]; rfl

private theorem takeExact_append :
    ∀ (xs ys : Bytes), LibsignalSpqrV1.Proto.takeExact xs.length (xs ++ ys) = .ok (xs, ys)
  | [], _ => rfl
  | _ :: xs, ys => by
    simp [LibsignalSpqrV1.Proto.takeExact, takeExact_append xs ys, Bind.bind, Except.bind]

private theorem mergeBytes_of_length_32 {bs : Bytes} (h : bs.length = 32) (after : Bytes) :
    LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited (0x20#8 :: (bs ++ after)) =
      .ok (bs, after) := by
  unfold LibsignalSpqrV1.Proto.mergeBytes LibsignalSpqrV1.Proto.checkWireType
  have hvar : LibsignalSpqrV1.Proto.decodeVarint (0x20#8 :: (bs ++ after)) =
      .ok (0x20#64, bs ++ after) := rfl
  rw [hvar]; dsimp only [Bind.bind, Except.bind]
  rw [show (0x20#64 : BitVec 64).toNat = bs.length from h.symm]
  exact takeExact_append bs after

private theorem decodeVarint_cons_of_lt_128 (b : BitVec 8) (rest : Bytes) (hb : b < 0x80#8) :
    LibsignalSpqrV1.Proto.decodeVarint (b :: rest) = .ok (b.zeroExtend 64, rest) := by
  have hacc : (0#64 ||| ((b &&& 0x7f#8).zeroExtend 64 <<< 0)) = b.zeroExtend 64 := by
    revert b hb; decide
  change (if b < 0x80#8 then
      Except.ok (0#64 ||| ((b &&& 0x7f#8).zeroExtend 64 <<< 0), rest) else _) = _
  simp only [hb, ↓reduceIte, hacc]

private theorem toNat_zeroExtend_64_8 (b : BitVec 8) : (b.zeroExtend 64).toNat = b.toNat := by
  revert b; decide

private theorem mergeMessage_of_lt_128 {M : Type}
    (mergeField : M → BitVec 32 → LibsignalSpqrV1.Proto.WireType → Bytes → Nat →
      Except LibsignalSpqrV1.Proto.DecodeErr (M × Bytes))
    (m m' : M) (b : BitVec 8) (sub after : Bytes) (depth depth' : Nat) (hdepth : depth = depth' + 1)
    (hb : b < 0x80#8) (hlen : sub.length = b.toNat)
    (hloop : LibsignalSpqrV1.Proto.mergeFieldsLoop mergeField b.toNat m sub depth' = .ok m') :
    LibsignalSpqrV1.Proto.mergeMessage mergeField .lengthDelimited m (b :: (sub ++ after))
      depth = .ok (m', after) := by
  subst hdepth; unfold LibsignalSpqrV1.Proto.mergeMessage LibsignalSpqrV1.Proto.checkWireType
  have hwt : (LibsignalSpqrV1.Proto.WireType.lengthDelimited !=
      LibsignalSpqrV1.Proto.WireType.lengthDelimited) = false := rfl
  simp only [hwt, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  rw [decodeVarint_cons_of_lt_128 b (sub ++ after) hb]; dsimp only
  rw [(toNat_zeroExtend_64_8 b).trans hlen.symm, takeExact_append sub after]; dsimp only
  rw [hlen, hloop]

private theorem chunked_keysUnsampled_default_uc :
    (default : LibsignalSpqrV1.V1State.Chunked.KeysUnsampled).uc = none := rfl
private theorem chunked_noHdr_default_uc :
    (default : LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived).uc = none := rfl
private theorem chunked_noHdr_default_hdr :
    (default : LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived).receivingHdr = none := rfl
private theorem v1State_default_innerState :
    (default : LibsignalSpqrV1.V1State).innerState = none := rfl
private theorem pqRatchetState_default_vn :
    (default : LibsignalSpqrV1.PqRatchetState).versionNegotiation = none := rfl
private theorem pqRatchetState_default_inner :
    (default : LibsignalSpqrV1.PqRatchetState).inner = none := rfl

private theorem decode_encode_auth {rk mk : Bytes} (hrk : rk.length = 32) (hmk : mk.length = 32)
    (d : Nat) :
    let raw := 0x0a#8 :: 0x20#8 :: (rk ++ (0x12#8 :: 0x20#8 :: mk))
    LibsignalSpqrV1.ProtoAuthenticator.encodeRaw { rootKey := rk, macKey := mk } = raw ∧
      raw.length = 68 ∧
      LibsignalSpqrV1.Proto.mergeFieldsLoop LibsignalSpqrV1.ProtoAuthenticator.mergeField
        68 default raw d = .ok { rootKey := rk, macKey := mk } := by
  intro raw; refine ⟨?_, by simp [raw, hrk, hmk], ?_⟩
  · have hk1 : LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl
    have hk2 : LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] := rfl
    simp [LibsignalSpqrV1.ProtoAuthenticator.encodeRaw, encodeBytesField_of_length_32 hrk,
      encodeBytesField_of_length_32 hmk, hk1, hk2, raw]
  · dsimp only [raw]; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk1 : LibsignalSpqrV1.Proto.decodeKey
        (0x0a#8 :: 0x20#8 :: (rk ++ (0x12#8 :: 0x20#8 :: mk))) =
        .ok ((1#32, .lengthDelimited), 0x20#8 :: (rk ++ (0x12#8 :: 0x20#8 :: mk))) := rfl
    rw [hk1]; dsimp only [Bind.bind, Except.bind, LibsignalSpqrV1.ProtoAuthenticator.mergeField]
    simp only [show (1#32 == (1#32 : BitVec 32)) = true from rfl, ↓reduceIte,
      mergeBytes_of_length_32 hrk]
    unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk2 : LibsignalSpqrV1.Proto.decodeKey (0x12#8 :: 0x20#8 :: mk) =
        .ok ((2#32, .lengthDelimited), 0x20#8 :: (mk ++ [])) := by simp [List.append_nil]; rfl
    rw [hk2]; dsimp only [Bind.bind, Except.bind, LibsignalSpqrV1.ProtoAuthenticator.mergeField]
    simp only [show (2#32 == (1#32 : BitVec 32)) = false from rfl,
      show (2#32 == (2#32 : BitVec 32)) = true from rfl, Bool.false_eq_true, ↓reduceIte,
      mergeBytes_of_length_32 hmk]; rfl

private theorem decode_encode_vn0 {ak : Bytes} (hak : ak.length = 32) :
    let vn : LibsignalSpqrV1.VersionNegotiationPB :=
      { authKey := ak, direction := 0#32, minVersion := 1#32,
        chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } }
    let raw := 0x0a#8 :: 0x20#8 :: (ak ++ [0x18#8, 0x01#8, 0x22#8, 0x00#8])
    LibsignalSpqrV1.VersionNegotiationPB.encodeRaw vn = raw ∧
      raw.length = 38 ∧
      LibsignalSpqrV1.Proto.mergeFieldsLoop LibsignalSpqrV1.VersionNegotiationPB.mergeField
        38 default raw 99 = .ok vn := by
  intro vn raw; refine ⟨?_, by simp [raw, hak], ?_⟩
  · have hk1 : LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl
    have hdir : LibsignalSpqrV1.Proto.encodeInt32Field 2#32 0#32 = [] := rfl
    have htail_enc : LibsignalSpqrV1.Proto.encodeInt32Field 3#32 1#32 ++
        LibsignalSpqrV1.Proto.encodeOptMessage LibsignalSpqrV1.ChainParamsPB.encodeRaw 4#32
          (some { maxJump := 0#32, maxOooKeys := 0#32 }) = [0x18#8, 0x01#8, 0x22#8, 0x00#8] := rfl
    simp [LibsignalSpqrV1.VersionNegotiationPB.encodeRaw, encodeBytesField_of_length_32 hak,
      hk1, hdir, htail_enc, vn, raw]
  · dsimp only [raw]; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk1 : LibsignalSpqrV1.Proto.decodeKey
        (0x0a#8 :: 0x20#8 :: (ak ++ [0x18#8, 0x01#8, 0x22#8, 0x00#8])) =
        .ok ((1#32, .lengthDelimited), 0x20#8 :: (ak ++ [0x18#8, 0x01#8, 0x22#8, 0x00#8])) := rfl
    rw [hk1]; dsimp only [Bind.bind, Except.bind, LibsignalSpqrV1.VersionNegotiationPB.mergeField]
    simp only [show (1#32 == (1#32 : BitVec 32)) = true from rfl, ↓reduceIte,
      mergeBytes_of_length_32 hak]; rfl

private theorem decode_encode_vn {ak : Bytes} (hak : ak.length = 32)
    (dir : BitVec 32) (dir8 : BitVec 8)
    (hdir : LibsignalSpqrV1.Proto.encodeInt32Field 2#32 dir = [0x10#8, dir8])
    (hmerge : LibsignalSpqrV1.Proto.mergeFieldsLoop LibsignalSpqrV1.VersionNegotiationPB.mergeField
      39 { (default : LibsignalSpqrV1.VersionNegotiationPB) with authKey := ak }
      [0x10#8, dir8, 0x18#8, 0x01#8, 0x22#8, 0x00#8] 99 =
      .ok { authKey := ak, direction := dir, minVersion := 1#32,
            chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } }) :
    let vn : LibsignalSpqrV1.VersionNegotiationPB :=
      { authKey := ak, direction := dir, minVersion := 1#32,
        chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } }
    let raw := 0x0a#8 :: 0x20#8 :: (ak ++ [0x10#8, dir8, 0x18#8, 0x01#8, 0x22#8, 0x00#8])
    LibsignalSpqrV1.VersionNegotiationPB.encodeRaw vn = raw ∧
      raw.length = 40 ∧
      LibsignalSpqrV1.Proto.mergeFieldsLoop LibsignalSpqrV1.VersionNegotiationPB.mergeField
        40 default raw 99 = .ok vn := by
  intro vn raw; refine ⟨?_, by simp [raw, hak], ?_⟩
  · have hk1 : LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl
    have htail_enc : LibsignalSpqrV1.Proto.encodeInt32Field 3#32 1#32 ++
        LibsignalSpqrV1.Proto.encodeOptMessage LibsignalSpqrV1.ChainParamsPB.encodeRaw 4#32
          (some { maxJump := 0#32, maxOooKeys := 0#32 }) = [0x18#8, 0x01#8, 0x22#8, 0x00#8] := rfl
    simp [LibsignalSpqrV1.VersionNegotiationPB.encodeRaw, encodeBytesField_of_length_32 hak,
      hk1, hdir, htail_enc, vn, raw]
  · dsimp only [raw]; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk1 : LibsignalSpqrV1.Proto.decodeKey
        (0x0a#8 :: 0x20#8 :: (ak ++ [0x10#8, dir8, 0x18#8, 0x01#8, 0x22#8, 0x00#8])) =
        .ok ((1#32, .lengthDelimited),
          0x20#8 :: (ak ++ [0x10#8, dir8, 0x18#8, 0x01#8, 0x22#8, 0x00#8])) := rfl
    rw [hk1]; dsimp only [Bind.bind, Except.bind, LibsignalSpqrV1.VersionNegotiationPB.mergeField]
    simp only [show (1#32 == (1#32 : BitVec 32)) = true from rfl, ↓reduceIte,
      mergeBytes_of_length_32 hak]; exact hmerge

private theorem decodeState_encodeState_initPbA (F : ShaCompress) (K : LibsignalSpqrV1.MlKem)
    (ak rk mk : Bytes) (hak : ak.length = 32) (hrk : rk.length = 32) (hmk : mk.length = 32) :
    LibsignalSpqrV1.decodeState (LibsignalSpqrV1.spqrDeps F K)
      ((LibsignalSpqrV1.spqrDeps F K).encodeState (initPbA ak rk mk)) =
      .ok (initPbA ak rk mk) := by
  obtain ⟨hAuthEnc, hAuthLen, hAuthLoop⟩ := decode_encode_auth hrk hmk 96
  obtain ⟨hVnEnc, hVnLen, hVnLoop⟩ := decode_encode_vn0 hak
  let authRaw := 0x0a#8 :: 0x20#8 :: (rk ++ (0x12#8 :: 0x20#8 :: mk))
  let ucRaw := 0x08#8 :: 0x01#8 :: 0x12#8 :: 0x44#8 :: (authRaw ++ [])
  have hUcEnc : LibsignalSpqrV1.V1State.Unchunked.KeysUnsampled.encodeRaw
      { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } = ucRaw := by
    simp [LibsignalSpqrV1.V1State.Unchunked.KeysUnsampled.encodeRaw,
      LibsignalSpqrV1.Proto.encodeOptMessage, LibsignalSpqrV1.Proto.encodeMessage,
      hAuthEnc, hAuthLen, ucRaw, authRaw]; rfl
  have hUcLen : ucRaw.length = 72 := by simp [ucRaw, authRaw, hrk, hmk]
  have hUcLoop : LibsignalSpqrV1.Proto.mergeFieldsLoop
      LibsignalSpqrV1.V1State.Unchunked.KeysUnsampled.mergeField 72 default ucRaw 97 =
      .ok { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } := by
    dsimp only [ucRaw]; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk1 : LibsignalSpqrV1.Proto.decodeKey
        (0x08#8 :: 0x01#8 :: 0x12#8 :: 0x44#8 :: (authRaw ++ [])) =
        .ok ((1#32, .varint), 0x01#8 :: 0x12#8 :: 0x44#8 :: (authRaw ++ [])) := rfl
    have hm1 : LibsignalSpqrV1.V1State.Unchunked.KeysUnsampled.mergeField default 1#32 .varint
        (0x01#8 :: 0x12#8 :: 0x44#8 :: (authRaw ++ [])) 97 =
        .ok ({ epoch := 1#64, auth := none }, 0x12#8 :: 0x44#8 :: (authRaw ++ [])) := rfl
    rw [hk1]; dsimp only [Bind.bind, Except.bind]; rw [hm1]; dsimp only [Bind.bind, Except.bind]
    unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk2 : LibsignalSpqrV1.Proto.decodeKey (0x12#8 :: 0x44#8 :: (authRaw ++ [])) =
        .ok ((2#32, .lengthDelimited), 0x44#8 :: (authRaw ++ [])) := rfl
    rw [hk2]; dsimp only [Bind.bind, Except.bind,
      LibsignalSpqrV1.V1State.Unchunked.KeysUnsampled.mergeField,
      LibsignalSpqrV1.Proto.mergeOptMessage, Option.getD]
    simp only [show (2#32 == (1#32 : BitVec 32)) = false from rfl,
      show (2#32 == (2#32 : BitVec 32)) = true from rfl, Bool.false_eq_true, ↓reduceIte]
    rw [mergeMessage_of_lt_128 LibsignalSpqrV1.ProtoAuthenticator.mergeField default
      { rootKey := rk, macKey := mk } 0x44#8 authRaw [] 97 96 rfl (by decide) hAuthLen hAuthLoop]
    rfl
  let chkRaw := 0x0a#8 :: 0x48#8 :: (ucRaw ++ [])
  have hChkEnc : LibsignalSpqrV1.V1State.Chunked.KeysUnsampled.encodeRaw
      { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } } = chkRaw := by
    simp [LibsignalSpqrV1.V1State.Chunked.KeysUnsampled.encodeRaw,
      LibsignalSpqrV1.Proto.encodeOptMessage, LibsignalSpqrV1.Proto.encodeMessage,
      hUcEnc, hUcLen, chkRaw]; rfl
  have hChkLen : chkRaw.length = 74 := by simp [chkRaw, hUcLen]
  have hChkLoop : LibsignalSpqrV1.Proto.mergeFieldsLoop
      LibsignalSpqrV1.V1State.Chunked.KeysUnsampled.mergeField 74 default chkRaw 98 =
      .ok { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } } := by
    dsimp only [chkRaw]; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk1 : LibsignalSpqrV1.Proto.decodeKey (0x0a#8 :: 0x48#8 :: (ucRaw ++ [])) =
        .ok ((1#32, .lengthDelimited), 0x48#8 :: (ucRaw ++ [])) := rfl
    rw [hk1]; dsimp only [Bind.bind, Except.bind,
      LibsignalSpqrV1.V1State.Chunked.KeysUnsampled.mergeField,
      LibsignalSpqrV1.Proto.mergeOptMessage, chunked_keysUnsampled_default_uc, Option.getD]
    simp only [show (1#32 == (1#32 : BitVec 32)) = true from rfl, ↓reduceIte]
    rw [mergeMessage_of_lt_128 LibsignalSpqrV1.V1State.Unchunked.KeysUnsampled.mergeField default
      { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } 0x48#8 ucRaw [] 98 97 rfl
      (by decide) hUcLen hUcLoop]; rfl
  let v1Raw := 0x0a#8 :: 0x4a#8 :: (chkRaw ++ [])
  have hV1Enc : LibsignalSpqrV1.V1State.encodeRaw
      { innerState := some (.keysUnsampled
          { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } }) } =
      v1Raw := by
    simp [LibsignalSpqrV1.V1State.encodeRaw, LibsignalSpqrV1.V1State.InnerState.encode,
      LibsignalSpqrV1.Proto.encodeMessage, hChkEnc, hChkLen, v1Raw]; rfl
  have hV1Len : v1Raw.length = 76 := by simp [v1Raw, hChkLen]
  have hV1Loop : LibsignalSpqrV1.Proto.mergeFieldsLoop
      LibsignalSpqrV1.V1State.mergeField 76 default v1Raw 99 =
      .ok { innerState := some (.keysUnsampled
          { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } }) } := by
    dsimp only [v1Raw]; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk1 : LibsignalSpqrV1.Proto.decodeKey (0x0a#8 :: 0x4a#8 :: (chkRaw ++ [])) =
        .ok ((1#32, .lengthDelimited), 0x4a#8 :: (chkRaw ++ [])) := rfl
    rw [hk1]; dsimp only [Bind.bind, Except.bind, LibsignalSpqrV1.V1State.mergeField,
      LibsignalSpqrV1.V1State.InnerState.merge, v1State_default_innerState]
    simp only [show ((1#32 : BitVec 32) ≥ 1#32 && (1#32 : BitVec 32) ≤ 11#32) = true from rfl,
      show (1#32 == (1#32 : BitVec 32)) = true from rfl, ↓reduceIte]
    rw [mergeMessage_of_lt_128 LibsignalSpqrV1.V1State.Chunked.KeysUnsampled.mergeField default
      { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } } 0x4a#8
      chkRaw [] 99 98 rfl (by decide) hChkLen hChkLoop]; rfl
  let vnRaw := 0x0a#8 :: 0x20#8 :: (ak ++ [0x18#8, 0x01#8, 0x22#8, 0x00#8])
  let topRaw := 0x0a#8 :: 0x26#8 :: (vnRaw ++ (0x1a#8 :: 0x4c#8 :: (v1Raw ++ [])))
  have hTopEnc : (LibsignalSpqrV1.spqrDeps F K).encodeState (initPbA ak rk mk) = topRaw := by
    simp [LibsignalSpqrV1.spqrDeps, LibsignalSpqrV1.pbToPqRatchetState, initPbA,
      LibsignalSpqrV1.Proto.encodeState, LibsignalSpqrV1.PqRatchetState.encode,
      LibsignalSpqrV1.PqRatchetState.encodeRaw, LibsignalSpqrV1.Proto.encodeOptMessage,
      LibsignalSpqrV1.PqRatchetState.Inner.encode, LibsignalSpqrV1.Proto.encodeMessage,
      hVnEnc, hVnLen, hV1Enc, hV1Len, topRaw, vnRaw]; rfl
  have hTopLen : topRaw.length = 118 := by simp [topRaw, vnRaw, hak, hV1Len]
  rw [hTopEnc]
  dsimp only [LibsignalSpqrV1.decodeState, LibsignalSpqrV1.spqrDeps,
    LibsignalSpqrV1.Proto.decodeState, LibsignalSpqrV1.PqRatchetState.decode,
    LibsignalSpqrV1.Proto.decodeTopLevelMessage, LibsignalSpqrV1.Proto.mergeTopLevelMessage,
    LibsignalSpqrV1.Proto.RECURSION_LIMIT]
  rw [show topRaw.isEmpty = false from rfl, hTopLen]
  dsimp only [Bool.false_eq_true, ↓reduceIte, topRaw]; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
  have hk1 : LibsignalSpqrV1.Proto.decodeKey
      (0x0a#8 :: 0x26#8 :: (vnRaw ++ (0x1a#8 :: 0x4c#8 :: (v1Raw ++ [])))) =
      .ok ((1#32, .lengthDelimited), 0x26#8 :: (vnRaw ++ (0x1a#8 :: 0x4c#8 :: (v1Raw ++ [])))) := rfl
  rw [hk1]; dsimp only [Bind.bind, Except.bind, LibsignalSpqrV1.PqRatchetState.mergeField,
    LibsignalSpqrV1.Proto.mergeOptMessage, pqRatchetState_default_vn, Option.getD]
  simp only [show (1#32 == (1#32 : BitVec 32)) = true from rfl, ↓reduceIte]
  rw [mergeMessage_of_lt_128 LibsignalSpqrV1.VersionNegotiationPB.mergeField default
    { authKey := ak, direction := 0#32, minVersion := 1#32,
      chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } }
    0x26#8 vnRaw (0x1a#8 :: 0x4c#8 :: (v1Raw ++ [])) 100 99 rfl (by decide) hVnLen hVnLoop]
  dsimp only; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
  have hk2 : LibsignalSpqrV1.Proto.decodeKey (0x1a#8 :: 0x4c#8 :: (v1Raw ++ [])) =
      .ok ((3#32, .lengthDelimited), 0x4c#8 :: (v1Raw ++ [])) := rfl
  rw [hk2]; dsimp only [Bind.bind, Except.bind, LibsignalSpqrV1.PqRatchetState.mergeField,
    LibsignalSpqrV1.PqRatchetState.Inner.merge, pqRatchetState_default_inner]
  simp only [show (3#32 == (1#32 : BitVec 32)) = false from rfl,
    show (3#32 == (2#32 : BitVec 32)) = false from rfl,
    show (3#32 == (3#32 : BitVec 32)) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [mergeMessage_of_lt_128 LibsignalSpqrV1.V1State.mergeField default
    { innerState := some (.keysUnsampled
        { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } }) }
    0x4c#8 v1Raw [] 100 99 rfl (by decide) hV1Len hV1Loop]; rfl

private theorem decode_encode_pd0 :
    LibsignalSpqrV1.Proto.mergeFieldsLoop LibsignalSpqrV1.PolynomialDecoder.mergeField
      36 default (LibsignalSpqrV1.PolynomialDecoder.encodeRaw initPd0) 97 = .ok initPd0 := rfl

private theorem decodeState_encodeState_initPbB (F : ShaCompress) (K : LibsignalSpqrV1.MlKem)
    (ak rk mk : Bytes) (hak : ak.length = 32) (hrk : rk.length = 32) (hmk : mk.length = 32) :
    LibsignalSpqrV1.decodeState (LibsignalSpqrV1.spqrDeps F K)
      ((LibsignalSpqrV1.spqrDeps F K).encodeState (initPbB ak rk mk)) =
      .ok (initPbB ak rk mk) := by
  obtain ⟨hAuthEnc, hAuthLen, hAuthLoop⟩ := decode_encode_auth hrk hmk 96
  obtain ⟨hVnEnc, hVnLen, hVnLoop⟩ := decode_encode_vn hak 1#32 0x01#8 rfl rfl
  let authRaw := 0x0a#8 :: 0x20#8 :: (rk ++ (0x12#8 :: 0x20#8 :: mk))
  let ucRaw := 0x08#8 :: 0x01#8 :: 0x12#8 :: 0x44#8 :: (authRaw ++ [])
  have hUcEnc : LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw
      { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } = ucRaw := by
    simp [LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw,
      LibsignalSpqrV1.Proto.encodeOptMessage, LibsignalSpqrV1.Proto.encodeMessage,
      hAuthEnc, hAuthLen, ucRaw, authRaw]; rfl
  have hUcLen : ucRaw.length = 72 := by simp [ucRaw, authRaw, hrk, hmk]
  have hUcLoop : LibsignalSpqrV1.Proto.mergeFieldsLoop
      LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.mergeField 72 default ucRaw 97 =
      .ok { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } := by
    dsimp only [ucRaw]; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk1 : LibsignalSpqrV1.Proto.decodeKey
        (0x08#8 :: 0x01#8 :: 0x12#8 :: 0x44#8 :: (authRaw ++ [])) =
        .ok ((1#32, .varint), 0x01#8 :: 0x12#8 :: 0x44#8 :: (authRaw ++ [])) := rfl
    have hm1 : LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.mergeField default 1#32 .varint
        (0x01#8 :: 0x12#8 :: 0x44#8 :: (authRaw ++ [])) 97 =
        .ok ({ epoch := 1#64, auth := none }, 0x12#8 :: 0x44#8 :: (authRaw ++ [])) := rfl
    rw [hk1]; dsimp only [Bind.bind, Except.bind]; rw [hm1]; dsimp only [Bind.bind, Except.bind]
    unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk2 : LibsignalSpqrV1.Proto.decodeKey (0x12#8 :: 0x44#8 :: (authRaw ++ [])) =
        .ok ((2#32, .lengthDelimited), 0x44#8 :: (authRaw ++ [])) := rfl
    rw [hk2]; dsimp only [Bind.bind, Except.bind,
      LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.mergeField,
      LibsignalSpqrV1.Proto.mergeOptMessage, Option.getD]
    simp only [show (2#32 == (1#32 : BitVec 32)) = false from rfl,
      show (2#32 == (2#32 : BitVec 32)) = true from rfl, Bool.false_eq_true, ↓reduceIte]
    rw [mergeMessage_of_lt_128 LibsignalSpqrV1.ProtoAuthenticator.mergeField default
      { rootKey := rk, macKey := mk } 0x44#8 authRaw [] 97 96 rfl (by decide) hAuthLen hAuthLoop]
    rfl
  let pdRaw := LibsignalSpqrV1.PolynomialDecoder.encodeRaw initPd0
  have hPdLen : pdRaw.length = 36 := rfl
  let chkRaw := 0x0a#8 :: 0x48#8 :: (ucRaw ++ (0x12#8 :: 0x24#8 :: (pdRaw ++ [])))
  have hChkEnc : LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw
      { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } },
        receivingHdr := some initPd0 } = chkRaw := by
    simp [LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw,
      LibsignalSpqrV1.Proto.encodeOptMessage, LibsignalSpqrV1.Proto.encodeMessage,
      hUcEnc, hUcLen, hPdLen, chkRaw, pdRaw]; rfl
  have hChkLen : chkRaw.length = 112 := by simp [chkRaw, hUcLen, hPdLen]
  have hChkLoop : LibsignalSpqrV1.Proto.mergeFieldsLoop
      LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.mergeField 112 default chkRaw 98 =
      .ok { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } },
            receivingHdr := some initPd0 } := by
    dsimp only [chkRaw]; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk1 : LibsignalSpqrV1.Proto.decodeKey
        (0x0a#8 :: 0x48#8 :: (ucRaw ++ (0x12#8 :: 0x24#8 :: (pdRaw ++ [])))) =
        .ok ((1#32, .lengthDelimited), 0x48#8 :: (ucRaw ++ (0x12#8 :: 0x24#8 :: (pdRaw ++ [])))) := rfl
    rw [hk1]; dsimp only [Bind.bind, Except.bind,
      LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.mergeField,
      LibsignalSpqrV1.Proto.mergeOptMessage, chunked_noHdr_default_uc, Option.getD]
    simp only [show (1#32 == (1#32 : BitVec 32)) = true from rfl, ↓reduceIte]
    rw [mergeMessage_of_lt_128 LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.mergeField default
      { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } } 0x48#8 ucRaw
      (0x12#8 :: 0x24#8 :: (pdRaw ++ [])) 98 97 rfl (by decide) hUcLen hUcLoop]
    dsimp only; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk2 : LibsignalSpqrV1.Proto.decodeKey (0x12#8 :: 0x24#8 :: (pdRaw ++ [])) =
        .ok ((2#32, .lengthDelimited), 0x24#8 :: (pdRaw ++ [])) := rfl
    rw [hk2]; dsimp only [Bind.bind, Except.bind,
      LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.mergeField,
      LibsignalSpqrV1.Proto.mergeOptMessage, chunked_noHdr_default_hdr, Option.getD]
    simp only [show (2#32 == (1#32 : BitVec 32)) = false from rfl,
      show (2#32 == (2#32 : BitVec 32)) = true from rfl, Bool.false_eq_true, ↓reduceIte]
    rw [mergeMessage_of_lt_128 LibsignalSpqrV1.PolynomialDecoder.mergeField default
      initPd0 0x24#8 pdRaw [] 98 97 rfl (by decide) hPdLen decode_encode_pd0]; rfl
  let v1Raw := 0x32#8 :: 0x70#8 :: (chkRaw ++ [])
  have hV1Enc : LibsignalSpqrV1.V1State.encodeRaw
      { innerState := some (.noHeaderReceived
          { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } },
            receivingHdr := some initPd0 }) } = v1Raw := by
    simp [LibsignalSpqrV1.V1State.encodeRaw, LibsignalSpqrV1.V1State.InnerState.encode,
      LibsignalSpqrV1.Proto.encodeMessage, hChkEnc, hChkLen, v1Raw]; rfl
  have hV1Len : v1Raw.length = 114 := by simp [v1Raw, hChkLen]
  have hV1Loop : LibsignalSpqrV1.Proto.mergeFieldsLoop
      LibsignalSpqrV1.V1State.mergeField 114 default v1Raw 99 =
      .ok { innerState := some (.noHeaderReceived
          { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } },
            receivingHdr := some initPd0 }) } := by
    dsimp only [v1Raw]; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
    have hk1 : LibsignalSpqrV1.Proto.decodeKey (0x32#8 :: 0x70#8 :: (chkRaw ++ [])) =
        .ok ((6#32, .lengthDelimited), 0x70#8 :: (chkRaw ++ [])) := rfl
    rw [hk1]; dsimp only [Bind.bind, Except.bind, LibsignalSpqrV1.V1State.mergeField,
      LibsignalSpqrV1.V1State.InnerState.merge, v1State_default_innerState]
    simp only [show ((6#32 : BitVec 32) ≥ 1#32 && (6#32 : BitVec 32) ≤ 11#32) = true from rfl,
      show (6#32 == (1#32 : BitVec 32)) = false from rfl,
      show (6#32 == (2#32 : BitVec 32)) = false from rfl,
      show (6#32 == (3#32 : BitVec 32)) = false from rfl,
      show (6#32 == (4#32 : BitVec 32)) = false from rfl,
      show (6#32 == (5#32 : BitVec 32)) = false from rfl,
      show (6#32 == (6#32 : BitVec 32)) = true from rfl, Bool.false_eq_true, ↓reduceIte]
    rw [mergeMessage_of_lt_128 LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.mergeField default
      { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } },
        receivingHdr := some initPd0 } 0x70#8 chkRaw [] 99 98 rfl (by decide) hChkLen hChkLoop]; rfl
  let vnRaw := 0x0a#8 :: 0x20#8 :: (ak ++ [0x10#8, 0x01#8, 0x18#8, 0x01#8, 0x22#8, 0x00#8])
  let topRaw := 0x0a#8 :: 0x28#8 :: (vnRaw ++ (0x1a#8 :: 0x72#8 :: (v1Raw ++ [])))
  have hTopEnc : (LibsignalSpqrV1.spqrDeps F K).encodeState (initPbB ak rk mk) = topRaw := by
    simp [LibsignalSpqrV1.spqrDeps, LibsignalSpqrV1.pbToPqRatchetState, initPbB,
      LibsignalSpqrV1.Proto.encodeState, LibsignalSpqrV1.PqRatchetState.encode,
      LibsignalSpqrV1.PqRatchetState.encodeRaw, LibsignalSpqrV1.Proto.encodeOptMessage,
      LibsignalSpqrV1.PqRatchetState.Inner.encode, LibsignalSpqrV1.Proto.encodeMessage,
      hVnEnc, hVnLen, hV1Enc, hV1Len, topRaw, vnRaw]; rfl
  have hTopLen : topRaw.length = 158 := by simp [topRaw, vnRaw, hak, hV1Len]
  rw [hTopEnc]
  dsimp only [LibsignalSpqrV1.decodeState, LibsignalSpqrV1.spqrDeps,
    LibsignalSpqrV1.Proto.decodeState, LibsignalSpqrV1.PqRatchetState.decode,
    LibsignalSpqrV1.Proto.decodeTopLevelMessage, LibsignalSpqrV1.Proto.mergeTopLevelMessage,
    LibsignalSpqrV1.Proto.RECURSION_LIMIT]
  rw [show topRaw.isEmpty = false from rfl, hTopLen]
  dsimp only [Bool.false_eq_true, ↓reduceIte, topRaw]; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
  have hk1 : LibsignalSpqrV1.Proto.decodeKey
      (0x0a#8 :: 0x28#8 :: (vnRaw ++ (0x1a#8 :: 0x72#8 :: (v1Raw ++ [])))) =
      .ok ((1#32, .lengthDelimited), 0x28#8 :: (vnRaw ++ (0x1a#8 :: 0x72#8 :: (v1Raw ++ [])))) := rfl
  rw [hk1]; dsimp only [Bind.bind, Except.bind, LibsignalSpqrV1.PqRatchetState.mergeField,
    LibsignalSpqrV1.Proto.mergeOptMessage, pqRatchetState_default_vn, Option.getD]
  simp only [show (1#32 == (1#32 : BitVec 32)) = true from rfl, ↓reduceIte]
  rw [mergeMessage_of_lt_128 LibsignalSpqrV1.VersionNegotiationPB.mergeField default
    { authKey := ak, direction := 1#32, minVersion := 1#32,
      chainParams := some { maxJump := 0#32, maxOooKeys := 0#32 } }
    0x28#8 vnRaw (0x1a#8 :: 0x72#8 :: (v1Raw ++ [])) 100 99 rfl (by decide) hVnLen hVnLoop]
  dsimp only; unfold LibsignalSpqrV1.Proto.mergeFieldsLoop
  have hk2 : LibsignalSpqrV1.Proto.decodeKey (0x1a#8 :: 0x72#8 :: (v1Raw ++ [])) =
      .ok ((3#32, .lengthDelimited), 0x72#8 :: (v1Raw ++ [])) := rfl
  rw [hk2]; dsimp only [Bind.bind, Except.bind, LibsignalSpqrV1.PqRatchetState.mergeField,
    LibsignalSpqrV1.PqRatchetState.Inner.merge, pqRatchetState_default_inner]
  simp only [show (3#32 == (1#32 : BitVec 32)) = false from rfl,
    show (3#32 == (2#32 : BitVec 32)) = false from rfl,
    show (3#32 == (3#32 : BitVec 32)) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [mergeMessage_of_lt_128 LibsignalSpqrV1.V1State.mergeField default
    { innerState := some (.noHeaderReceived
        { uc := some { epoch := 1#64, auth := some { rootKey := rk, macKey := mk } },
          receivingHdr := some initPd0 }) }
    0x72#8 v1Raw [] 100 99 rfl (by decide) hV1Len hV1Loop]; rfl

private theorem generate_of_vec64 (K : LibsignalSpqrV1.MlKem)
    (rs : List.Vector (BitVec 8) 64) :
    LibsignalSpqrV1.generate K rs.toList =
      .ok (let (hdr, ek, dk) := K.fromSeed rs
           ({ ek := ek.toList, dk := dk.toList, hdr := hdr.toList }, [])) := by
  rcases rs with ⟨l, hl⟩
  have h : LibsignalSpqrV1.generate K (expandList 64 l) =
      .ok (let (hdr, ek, dk) := K.fromSeed ⟨expandList 64 l, rfl⟩
           ({ ek := ek.toList, dk := dk.toList, hdr := hdr.toList }, [])) := rfl
  simpa [← expandList_eq hl] using h

private def initHdrDec0 : LibsignalSpqrV1.PolyDecoder :=
  { ptsNeeded := 48
    pts := List.replicate 16 LibsignalSpqrV1.SortedSetPt.new
    isComplete := false }

private def distributeMsgChunksTotal :
    Nat → List (BitVec 8) → List LibsignalSpqrV1.Point → List LibsignalSpqrV1.Point
  | _, [], pts => pts
  | _, [ _ ], pts => pts
  | i, c0 :: c1 :: rest, pts =>
    let poly := i % 16
    let pt := pts[poly]?.getD { value := [] }
    let gf := LibsignalSpqrV1.GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)
    let pts' := pts.set poly { value := pt.value ++ [gf] }
    distributeMsgChunksTotal (i + 1) rest pts'

private theorem distributeMsgChunks_eq_ok :
    ∀ (msg : List (BitVec 8)) (i : Nat) (pts : List LibsignalSpqrV1.Point),
      msg.length % 2 = 0 → pts.length = 16 →
      LibsignalSpqrV1.PolyEncoder.distributeMsgChunks i msg pts =
        .ok (distributeMsgChunksTotal i msg pts) ∧
        (distributeMsgChunksTotal i msg pts).length = 16
  | [], _, pts, _, hpts => by
    simp [LibsignalSpqrV1.PolyEncoder.distributeMsgChunks, distributeMsgChunksTotal, hpts]
  | [ _ ], _, _, hlen, _ => by simp at hlen
  | c0 :: c1 :: rest, i, pts, hlen, hpts => by
    have hrest : rest.length % 2 = 0 := by simp only [List.length_cons] at hlen; omega
    have hpoly_lt : i % 16 < pts.length := by rw [hpts]; exact Nat.mod_lt i (by decide)
    let pt := pts[i % 16]
    have hpt : pts[i % 16]? = some pt := List.getElem?_eq_some_iff.mpr ⟨hpoly_lt, rfl⟩
    let gf := LibsignalSpqrV1.GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)
    have hpts' : (pts.set (i % 16) { value := pt.value ++ [gf] }).length = 16 := by
      rw [List.length_set, hpts]
    have ih := distributeMsgChunks_eq_ok rest (i + 1)
      (pts.set (i % 16) { value := pt.value ++ [gf] }) hrest hpts'
    simp only [LibsignalSpqrV1.PolyEncoder.distributeMsgChunks, distributeMsgChunksTotal,
      hpts, hpt, Option.getD_some]
    exact ih

private theorem distributeMsgChunksTotal_getD_len_le :
    ∀ (msg : Bytes) (i : Nat) (pts : List LibsignalSpqrV1.Point) (k : Nat),
      pts.length = 16 →
      (pts[k]?.getD { value := [] }).value.length ≤
        ((distributeMsgChunksTotal i msg pts)[k]?.getD { value := [] }).value.length
  | [], _, _, _, _ => Nat.le_refl _
  | [ _ ], _, _, _, _ => Nat.le_refl _
  | c0 :: c1 :: rest, i, pts, k, hpts => by
    let pt := pts[i % 16]?.getD { value := [] }
    let gf := LibsignalSpqrV1.GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)
    let pts' := pts.set (i % 16) { value := pt.value ++ [gf] }
    have hpts' : pts'.length = 16 := by simp [pts', hpts]
    have ih := distributeMsgChunksTotal_getD_len_le rest (i + 1) pts' k hpts'
    have hstep : (pts[k]?.getD { value := [] }).value.length ≤
        (pts'[k]?.getD { value := [] }).value.length := by
      dsimp only [pts']; rw [List.getElem?_set]; split_ifs with h1
      · subst h1; simp [pt]
      · omega
      · exact Nat.le_refl _
    exact Nat.le_trans hstep ih

private theorem distributeMsgChunksTotal_getD_len_pos :
    ∀ (msg : Bytes) (i : Nat) (pts : List LibsignalSpqrV1.Point) (k : Nat),
      pts.length = 16 → i ≤ k → k < 16 → 2 * (k - i) + 2 ≤ msg.length →
      0 < ((distributeMsgChunksTotal i msg pts)[k]?.getD { value := [] }).value.length
  | [], _, _, _, _, _, _, hlen => by simp at hlen
  | [ _ ], _, _, _, _, _, _, hlen => by simp at hlen
  | c0 :: c1 :: rest, i, pts, k, hpts, hik, hk16, hlen => by
    let pt := pts[i % 16]?.getD { value := [] }
    let gf := LibsignalSpqrV1.GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)
    let pts' := pts.set (i % 16) { value := pt.value ++ [gf] }
    have hpts' : pts'.length = 16 := by simp [pts', hpts]
    by_cases heq : i = k
    · subst heq
      have himod : i % 16 = i := Nat.mod_eq_of_lt hk16
      have hi_lt : i < pts.length := by omega
      have hpos' : 0 < (pts'[i]?.getD { value := [] }).value.length := by
        dsimp only [pts']; rw [himod, List.getElem?_set_self hi_lt]; simp [pt]
      exact Nat.lt_of_lt_of_le hpos'
        (distributeMsgChunksTotal_getD_len_le rest (i + 1) pts' i hpts')
    · exact distributeMsgChunksTotal_getD_len_pos rest (i + 1) pts' k hpts'
        (by omega) hk16 (by simp only [List.length_cons] at hlen; omega)

private theorem chunkAtLoop_zero_points_eq (pts : List LibsignalSpqrV1.Point) :
    ∀ (rem i : Nat),
      i + rem ≤ 16 → pts.length = 16 →
      (∀ k (hk : k < pts.length), i ≤ k → 0 < (pts[k]'hk).value.length) →
      ∃ data : List.Vector (BitVec 8) (2 * rem),
        LibsignalSpqrV1.PolyEncoder.chunkAtLoop 0#16 i rem { idx := 0#32, s := .points pts } =
          .ok ({ idx := 0#32, s := .points pts }, data)
  | 0, _, _, _, _ => ⟨List.Vector.nil, rfl⟩
  | rem + 1, i, hle, hlen, hall => by
    have hi_len : i < pts.length := by omega
    have hpos : 0 < (pts[i]'hi_len).value.length := hall i hi_len (Nat.le_refl i)
    have hpt_opt : pts[i]? = some (pts[i]'hi_len) := List.getElem?_eq_getElem hi_len
    have hval_opt : (pts[i]'hi_len).value[0]? = some ((pts[i]'hi_len).value[0]'hpos) :=
      List.getElem?_eq_getElem hpos
    have h0_16 : (0#16 : BitVec 16).toNat = 0 := rfl
    have hmod : ((0#16 : BitVec 16).toNat * 16 + i) % 16 = i := by rw [h0_16]; omega
    have hdiv : ((0#16 : BitVec 16).toNat * 16 + i) / 16 = 0 := by rw [h0_16]; omega
    have hpt : LibsignalSpqrV1.PolyEncoder.pointAt { idx := 0#32, s := .points pts } i 0 =
        .ok ({ idx := 0#32, s := .points pts }, (pts[i]'hi_len).value[0]'hpos) := by
      unfold LibsignalSpqrV1.PolyEncoder.pointAt
      simp only [hpt_opt, hval_opt, Pure.pure, Except.pure]
    obtain ⟨tail, ih⟩ := chunkAtLoop_zero_points_eq pts rem (i + 1) (by omega) hlen
      (fun k hk hik => hall k hk (by omega))
    unfold LibsignalSpqrV1.PolyEncoder.chunkAtLoop
    simp only [hmod, hdiv, hpt, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨_, rfl⟩

private def addChunkLoopTotal (chunk : LibsignalSpqrV1.Chunk) :
    Nat → Nat → LibsignalSpqrV1.PolyDecoder → LibsignalSpqrV1.PolyDecoder
  | _, 0, self => self
  | i, rem + 1, self =>
    let totalIdx := chunk.index.toNat * 16 + i
    let poly := totalIdx % 16
    let polyIdx := totalIdx / 16
    let x := LibsignalSpqrV1.GF16.new (BitVec.ofNat 16 polyIdx)
    let y1 := chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    let y2 := chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    let y := LibsignalSpqrV1.GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
    let polyPts := self.pts[poly]?.getD LibsignalSpqrV1.SortedSetPt.new
    let nec := self.necessaryPoints i
    let self' :=
      if polyIdx < nec || polyPts.len < nec then
        let (polyPts', _, _) := polyPts.push { x := x, y := y }
        { self with pts := self.pts.set poly polyPts' }
      else self
    addChunkLoopTotal chunk (i + 1) rem self'

private theorem addChunkLoop_eq_ok (chunk : LibsignalSpqrV1.Chunk) :
    ∀ (rem i : Nat) (self : LibsignalSpqrV1.PolyDecoder),
      self.pts.length = 16 →
      LibsignalSpqrV1.PolyDecoder.addChunkLoop chunk i rem self =
        .ok (addChunkLoopTotal chunk i rem self) ∧
        (addChunkLoopTotal chunk i rem self).pts.length = 16 ∧
        (addChunkLoopTotal chunk i rem self).ptsNeeded = self.ptsNeeded ∧
        (addChunkLoopTotal chunk i rem self).isComplete = self.isComplete
  | 0, _, self, hlen => by
    simp [LibsignalSpqrV1.PolyDecoder.addChunkLoop, addChunkLoopTotal, hlen]
  | rem + 1, i, self, hlen => by
    have hpoly_lt : (chunk.index.toNat * 16 + i) % 16 < self.pts.length := by
      rw [hlen]; exact Nat.mod_lt _ (by decide)
    have hget : self.pts[(chunk.index.toNat * 16 + i) % 16]? =
        some (self.pts[(chunk.index.toNat * 16 + i) % 16]'hpoly_lt) :=
      List.getElem?_eq_getElem hpoly_lt
    let polyPts := self.pts[(chunk.index.toNat * 16 + i) % 16]'hpoly_lt
    let polyIdx := (chunk.index.toNat * 16 + i) / 16
    let x := LibsignalSpqrV1.GF16.new (BitVec.ofNat 16 polyIdx)
    let y1 := chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    let y2 := chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    let y := LibsignalSpqrV1.GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
    let nec := self.necessaryPoints i
    let self' :=
      if polyIdx < nec || polyPts.len < nec then
        let (polyPts', _, _) := polyPts.push { x := x, y := y }
        { self with pts := self.pts.set ((chunk.index.toNat * 16 + i) % 16) polyPts' }
      else self
    have hlen' : self'.pts.length = 16 := by dsimp only [self']; split <;> simp [hlen]
    have hneed' : self'.ptsNeeded = self.ptsNeeded := by dsimp only [self']; split <;> rfl
    have hcomp' : self'.isComplete = self.isComplete := by dsimp only [self']; split <;> rfl
    have ih := addChunkLoop_eq_ok chunk rem (i + 1) self' hlen'
    unfold LibsignalSpqrV1.PolyDecoder.addChunkLoop addChunkLoopTotal
    dsimp only; rw [hget, Option.getD_some]
    exact ⟨ih.1, ih.2.1, ih.2.2.1.trans hneed', ih.2.2.2.trans hcomp'⟩

private theorem addChunkLoopTotal_succ (chunk : LibsignalSpqrV1.Chunk)
    (i rem : Nat) (self : LibsignalSpqrV1.PolyDecoder) :
    addChunkLoopTotal chunk i (rem + 1) self =
      let polyIdx := (chunk.index.toNat * 16 + i) / 16
      let poly := (chunk.index.toNat * 16 + i) % 16
      let x := LibsignalSpqrV1.GF16.new (BitVec.ofNat 16 polyIdx)
      let y1 := chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
      let y2 := chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
      let y := LibsignalSpqrV1.GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
      let polyPts := self.pts[poly]?.getD LibsignalSpqrV1.SortedSetPt.new
      let nec := self.necessaryPoints i
      let self' :=
        if polyIdx < nec || polyPts.len < nec then
          let (polyPts', _, _) := polyPts.push { x := x, y := y }
          { self with pts := self.pts.set poly polyPts' }
        else self
      addChunkLoopTotal chunk (i + 1) rem self' := rfl

private theorem addChunkLoopTotal_zero_pts0_of_pos (data : List.Vector (BitVec 8) 32) :
    ∀ (rem i : Nat) (self : LibsignalSpqrV1.PolyDecoder),
      1 ≤ i → i + rem ≤ 16 →
      (addChunkLoopTotal { index := 0#16, data := data } i rem self).pts[0]? = self.pts[0]?
  | 0, _, _, _, _ => rfl
  | rem + 1, i, self, hi, hle => by
    have h0_16 : (0#16 : BitVec 16).toNat = 0 := rfl
    have hmod : ((0#16 : BitVec 16).toNat * 16 + i) % 16 = i := by rw [h0_16]; omega
    have hne : i ≠ 0 := by omega
    rw [addChunkLoopTotal_succ]; dsimp only
    rw [addChunkLoopTotal_zero_pts0_of_pos data rem (i + 1) _ (by omega) (by omega)]
    split
    · rw [hmod, List.getElem?_set_ne hne]
    · rfl

private theorem addChunkLoopTotal_initHdrDec0_pts0 (data : List.Vector (BitVec 8) 32) :
    ((addChunkLoopTotal { index := 0#16, data := data } 0 16 initHdrDec0).pts[0]?.getD
      LibsignalSpqrV1.SortedSetPt.new).len = 1 := by
  rw [addChunkLoopTotal_succ { index := 0#16, data := data } 0 15 initHdrDec0]; dsimp only
  rw [addChunkLoopTotal_zero_pts0_of_pos data 15 1 _ (by decide) (by decide)]
  rfl

private theorem collectPointsVecs_retNone_true (self : LibsignalSpqrV1.PolyDecoder) :
    ∀ (rem i : Nat) (pointsVecs : List (List LibsignalSpqrV1.Pt)),
      i + rem ≤ self.pts.length →
      ∃ outVecs,
        LibsignalSpqrV1.PolyDecoder.collectPointsVecs self i rem true pointsVecs =
          .ok (true, outVecs)
  | 0, _, pointsVecs, _ => ⟨pointsVecs, rfl⟩
  | rem + 1, i, pointsVecs, hle => by
    have hi : i < self.pts.length := by omega
    have hget : self.pts[i]? = some (self.pts[i]'hi) := List.getElem?_eq_getElem hi
    unfold LibsignalSpqrV1.PolyDecoder.collectPointsVecs
    rw [hget]; dsimp only [Bind.bind, Except.bind]
    split <;> exact collectPointsVecs_retNone_true self rem (i + 1) _ (by omega)

private theorem poly_firstHdrChunk_send_recv (hdr mac : Bytes)
    (hhdr : hdr.length = 64) (hmac : mac.length = 32) :
    ∃ (enc0 enc1 : LibsignalSpqrV1.PolyEncoder) (data : List.Vector (BitVec 8) 32)
      (dec1 : LibsignalSpqrV1.PolyDecoder),
      LibsignalSpqrV1.expectEncodeBytes LibsignalSpqrV1.spqrPolyApi
        "v1/chunked/send_ek.rs:63" (hdr ++ mac) = .ok enc0 ∧
      LibsignalSpqrV1.spqrPolyApi.next_chunk enc0 =
        .ok (enc1, { index := 0#16, data := data }) ∧
      LibsignalSpqrV1.StatesResult.ofPanic
        (LibsignalSpqrV1.spqrPolyApi.add_chunk initHdrDec0 { index := 0#16, data := data }) =
        .ok dec1 ∧
      LibsignalSpqrV1.StatesResult.ofPanic
        (LibsignalSpqrV1.spqrPolyApi.decoded_message dec1) = .ok none := by
  let msg := hdr ++ mac
  have hmsg : msg.length = 96 := by simp [msg, hhdr, hmac]
  have heven : msg.length % 2 = 0 := by rw [hmsg]
  have hnot_odd : (msg.length % 2 != 0) = false := by rw [hmsg]; rfl
  have hnot_long : ¬ (msg.length > (1 <<< 16) * LibsignalSpqrV1.NUM_POLYS) := by
    rw [hmsg]; decide
  let initPts : List LibsignalSpqrV1.Point :=
    List.replicate LibsignalSpqrV1.NUM_POLYS { value := [] }
  have hinit_len : initPts.length = 16 := rfl
  obtain ⟨pts, hpts_def⟩ : ∃ pts, distributeMsgChunksTotal 0 msg initPts = pts := ⟨_, rfl⟩
  obtain ⟨hdist, hpts_len⟩ := distributeMsgChunks_eq_ok msg 0 initPts heven hinit_len
  rw [hpts_def] at hdist hpts_len
  have hall_pos : ∀ k (hk : k < pts.length), 0 < (pts[k]'hk).value.length := by
    intro k hk
    have hk16 : k < 16 := by omega
    have hpos := distributeMsgChunksTotal_getD_len_pos msg 0 initPts k hinit_len
      (Nat.zero_le k) hk16 (by omega)
    rw [hpts_def] at hpos
    have hget : pts[k]? = some (pts[k]'hk) := List.getElem?_eq_getElem hk
    simpa [hget] using hpos
  obtain ⟨data, hchunkLoop⟩ := chunkAtLoop_zero_points_eq pts 16 0 (by decide) hpts_len
    (fun k hk _ => hall_pos k hk)
  have henc : LibsignalSpqrV1.expectEncodeBytes LibsignalSpqrV1.spqrPolyApi
      "v1/chunked/send_ek.rs:63" msg = .ok { idx := 0#32, s := .points pts } := by
    unfold LibsignalSpqrV1.expectEncodeBytes LibsignalSpqrV1.spqrPolyApi
      LibsignalSpqrV1.PolyEncoder.encodeBytes LibsignalSpqrV1.PolyEncoder.encodeBytesBase
    simp only [hnot_odd, hnot_long, Bool.false_eq_true, ↓reduceIte,
      Bind.bind, Except.bind, Pure.pure, Except.pure, Except.mapError]
    rw [show List.replicate LibsignalSpqrV1.NUM_POLYS
        ({ value := [] } : LibsignalSpqrV1.Point) = initPts from rfl, hdist]
    rfl
  have hnext : LibsignalSpqrV1.spqrPolyApi.next_chunk { idx := 0#32, s := .points pts } =
      .ok ({ idx := 1#32, s := .points pts }, { index := 0#16, data := data }) := by
    unfold LibsignalSpqrV1.spqrPolyApi LibsignalSpqrV1.PolyEncoder.nextChunk
      LibsignalSpqrV1.PolyEncoder.chunkAt
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [show BitVec.setWidth 16 (0#32 : BitVec 32) = 0#16 from rfl, hchunkLoop]
    rfl
  let chunk0 : LibsignalSpqrV1.Chunk := { index := 0#16, data := data }
  have hdec0_len : initHdrDec0.pts.length = 16 := rfl
  obtain ⟨dec1, hdec1_def⟩ : ∃ dec1, addChunkLoopTotal chunk0 0 16 initHdrDec0 = dec1 := ⟨_, rfl⟩
  obtain ⟨hadd, hdec1_len, hdec1_need, hdec1_comp⟩ :=
    addChunkLoop_eq_ok chunk0 16 0 initHdrDec0 hdec0_len
  rw [hdec1_def] at hadd hdec1_len hdec1_need hdec1_comp
  have hdec1_pts0 : (dec1.pts[0]?.getD LibsignalSpqrV1.SortedSetPt.new).len = 1 := by
    rw [← hdec1_def]; exact addChunkLoopTotal_initHdrDec0_pts0 data
  have hdec1_pts0_get : ∃ s0, dec1.pts[0]? = some s0 ∧ s0.len = 1 := by
    have h0 : 0 < dec1.pts.length := by rw [hdec1_len]; decide
    refine ⟨dec1.pts[0]'h0, List.getElem?_eq_getElem h0, ?_⟩
    have hget : dec1.pts[0]? = some (dec1.pts[0]'h0) := List.getElem?_eq_getElem h0
    simpa [hget] using hdec1_pts0
  obtain ⟨s0, hs0_get, hs0_len⟩ := hdec1_pts0_get
  obtain ⟨outVecs, hcollect⟩ :=
    collectPointsVecs_retNone_true dec1 15 1 [] (by rw [hdec1_len])
  have hcollect0 :
      LibsignalSpqrV1.PolyDecoder.collectPointsVecs dec1 0 16 false [] =
        .ok (true, outVecs) := by
    unfold LibsignalSpqrV1.PolyDecoder.collectPointsVecs
    rw [hs0_get]; dsimp only [Bind.bind, Except.bind]
    have hnec0 : dec1.necessaryPoints 0 = 3 := by
      simp [LibsignalSpqrV1.PolyDecoder.necessaryPoints, hdec1_need, initHdrDec0]
    have hlt0 : s0.len < dec1.necessaryPoints 0 := by omega
    simp only [hlt0, ↓reduceIte]
    exact hcollect
  refine ⟨{ idx := 0#32, s := .points pts }, { idx := 1#32, s := .points pts }, data, dec1,
    henc, hnext, ?_, ?_⟩
  · dsimp only [LibsignalSpqrV1.spqrPolyApi, LibsignalSpqrV1.PolyDecoder.addChunk,
      LibsignalSpqrV1.StatesResult.ofPanic, Except.mapError]
    rw [hadd]
  · dsimp only [LibsignalSpqrV1.spqrPolyApi, LibsignalSpqrV1.PolyDecoder.decodedMessage,
      LibsignalSpqrV1.StatesResult.ofPanic, Except.mapError]
    rw [hdec1_comp, hdec1_len]
    dsimp only [initHdrDec0, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
    rw [hcollect0]; rfl

private theorem msg_firstHdrChunk_roundtrip (F : ShaCompress) (K : LibsignalSpqrV1.MlKem)
    (data : List.Vector (BitVec 8) 32) :
    let msg : (LibsignalSpqrV1.spqrDeps F K).MessageV1 :=
      { epoch := 1#64, payload := .hdr { index := 0#16, data := data } }
    let raw := (LibsignalSpqrV1.spqrDeps F K).msgSerialize msg 1#32
    raw = [1#8, 1#8, 1#8, 1#8, 0#8] ++ data.toList ∧
      raw.length = 37 ∧
      LibsignalSpqrV1.msgPreamble raw =
        .ok { version := 1#8, epoch := 1#64, index := 1#32,
              remaining := 1#8 :: 0#8 :: data.toList } ∧
      (LibsignalSpqrV1.spqrDeps F K).msgDeserialize 1#64 (1#8 :: 0#8 :: data.toList) =
        .ok msg := by
  intro msg raw
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [raw, msg, LibsignalSpqrV1.spqrDeps, LibsignalSpqrV1.Message.serialize,
      LibsignalSpqrV1.MessageType.from_payload, LibsignalSpqrV1.MessageType.toU8,
      LibsignalSpqrV1.encode_chunk, LibsignalSpqrV1.encode_varint,
      LibsignalSpqrV1.encodeVarintLoop, LibsignalSpqrV1.MAX_VARINT_BYTES_LEN,
      LibsignalSpqrV1.spqrPolyApi]
  · simp [raw, msg, LibsignalSpqrV1.spqrDeps, LibsignalSpqrV1.Message.serialize,
      LibsignalSpqrV1.MessageType.from_payload, LibsignalSpqrV1.MessageType.toU8,
      LibsignalSpqrV1.encode_chunk, LibsignalSpqrV1.encode_varint,
      LibsignalSpqrV1.encodeVarintLoop, LibsignalSpqrV1.MAX_VARINT_BYTES_LEN,
      LibsignalSpqrV1.spqrPolyApi]
  · simp [raw, msg, LibsignalSpqrV1.spqrDeps, LibsignalSpqrV1.Message.serialize,
      LibsignalSpqrV1.MessageType.from_payload, LibsignalSpqrV1.MessageType.toU8,
      LibsignalSpqrV1.encode_chunk, LibsignalSpqrV1.encode_varint,
      LibsignalSpqrV1.encodeVarintLoop, LibsignalSpqrV1.MAX_VARINT_BYTES_LEN,
      LibsignalSpqrV1.spqrPolyApi, LibsignalSpqrV1.msgPreamble,
      LibsignalSpqrV1.msg_preamble, LibsignalSpqrV1.decode_varint,
      LibsignalSpqrV1.decodeVarintLoop, Bind.bind, Except.bind]
  · rcases data with ⟨d, hd⟩
    have hdeser : (LibsignalSpqrV1.spqrDeps F K).msgDeserialize 1#64
        (1#8 :: 0#8 :: expandList 32 d) =
        .ok { epoch := 1#64,
              payload := .hdr { index := 0#16, data := ⟨expandList 32 d, rfl⟩ } } := rfl
    simpa [msg, ← expandList_eq hd] using hdeser

private theorem initialState_eq_of_initInner (F : ShaCompress) (K : LibsignalSpqrV1.MlKem)
    (dir : SpqrDirection) (pqrKey : BitVec 256)
    (inner : Option LibsignalSpqrV1.V1State)
    (pb : LibsignalSpqrV1.PqRatchetStatePB LibsignalSpqrV1.V1State)
    (h : LibsignalSpqrV1.initInner (LibsignalSpqrV1.spqrDeps F K) .v1
      (LibsignalSpqrV1.Direction.ofSpqrDirection dir) (HMAC.keyToBytes32 pqrKey) = .ok inner)
    (hpb : { inner := inner
             versionNegotiation := some
               { authKey := HMAC.keyToBytes32 pqrKey
                 direction := (LibsignalSpqrV1.Direction.ofSpqrDirection dir).toI32
                 minVersion := LibsignalSpqrV1.Version.v1.toI32
                 chainParams := some LibsignalSpqrV1.ChainParams.default.intoPb }
             chain := none } = pb) :
    LibsignalSpqrV1.spqrV1Init F K dir pqrKey =
      (LibsignalSpqrV1.spqrDeps F K).encodeState pb := by
  subst hpb
  obtain ⟨st, hok, hinit, _⟩ := LibsignalSpqrV1.spqrV1Init_eq F K dir pqrKey
  rw [hinit]
  dsimp only [LibsignalSpqrV1.initialState, LibsignalSpqrV1.libsignalSpqrParams,
    LibsignalSpqrV1.libsignalChainParams,
    LibsignalSpqrV1.SpqrApiResult.ofPanic, Bind.bind, Except.bind] at hok
  rw [h] at hok
  exact (Except.ok.inj hok).symm

theorem spqrPq_firstMessage_send_recv (W : PEParams) (pqr0 : BitVec 256)
    (rs : List.Vector (BitVec 8) 64) :
    ∃ stA1 salt pqMsg stB1,
      (pqxdhSpqrSession W).send ((pqxdhSpqrSession W).init .a2b pqr0) rs.toList = some (stA1, salt, pqMsg) ∧
      pqMsg.length = 37 ∧
      (pqxdhSpqrSession W).recv ((pqxdhSpqrSession W).init .b2a pqr0) pqMsg = .ok (stB1, salt) := by
  let ak := HMAC.keyToBytes32 pqr0
  have hak : ak.length = 32 := rfl
  let auth0 := LibsignalSpqrV1.Authenticator.new W.C.F ak 1#64
  have hrk : auth0.rootKey.length = 32 := by
    simp [auth0, LibsignalSpqrV1.Authenticator.new, LibsignalSpqrV1.Authenticator.update,
      LibsignalSpqrV1.hkdfToVecUnchecked, LibsignalSpqrV1.hkdfToSliceUnchecked]
  have hmk : auth0.macKey.length = 32 := by
    simp [auth0, LibsignalSpqrV1.Authenticator.new, LibsignalSpqrV1.Authenticator.update,
      LibsignalSpqrV1.hkdfToVecUnchecked, LibsignalSpqrV1.hkdfToSliceUnchecked]
  have hInnerA :
      LibsignalSpqrV1.initInner (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K) .v1 .a2b ak =
      .ok (some { innerState := some (.keysUnsampled
        { uc := some { epoch := 1#64,
                       auth := some { rootKey := auth0.rootKey, macKey := auth0.macKey } } }) }) :=
    rfl
  have hInnerB :
      LibsignalSpqrV1.initInner (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K) .v1 .b2a ak =
      .ok (some { innerState := some (.noHeaderReceived
        { uc := some { epoch := 1#64,
                       auth := some { rootKey := auth0.rootKey, macKey := auth0.macKey } }
          receivingHdr := some initPd0 }) }) :=
    rfl
  have hInitA : (pqxdhSpqrSession W).init .a2b pqr0 =
      (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).encodeState
        (initPbA ak auth0.rootKey auth0.macKey) :=
    initialState_eq_of_initInner W.C.F W.Q.K .a2b pqr0 _
      (initPbA ak auth0.rootKey auth0.macKey) hInnerA rfl
  have hInitB : (pqxdhSpqrSession W).init .b2a pqr0 =
      (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).encodeState
        (initPbB ak auth0.rootKey auth0.macKey) :=
    initialState_eq_of_initInner W.C.F W.Q.K .b2a pqr0 _
      (initPbB ak auth0.rootKey auth0.macKey) hInnerB rfl
  have hDecA := decodeState_encodeState_initPbA W.C.F W.Q.K ak auth0.rootKey auth0.macKey
    hak hrk hmk
  have hDecB := decodeState_encodeState_initPbB W.C.F W.Q.K ak auth0.rootKey auth0.macKey
    hak hrk hmk
  have hGen := generate_of_vec64 W.Q.K rs
  let hdr := (W.Q.K.fromSeed rs).1.toList
  have hhdr : hdr.length = 64 := (W.Q.K.fromSeed rs).1.toList_length
  have hmk_lt : auth0.macKey.length < 2 ^ 32 := by rw [hmk]; decide
  have hhdr_lt :
      (LibsignalSpqrV1.Authenticator.hdrLabel ++ HMAC.toBEBytes 8 1#64 ++ hdr).length < 2 ^ 32 := by
    simp only [List.length_append, hhdr]; decide
  let mac := auth0.macHdrUnchecked W.C.F 1#64 hdr
  let auth0A : (LibsignalSpqrV1.spqrAuthApi W.C.F).Authenticator := auth0
  have hMacHdr :
      (LibsignalSpqrV1.spqrAuthApi W.C.F).mac_hdr auth0A 1#64 hdr = .ok mac :=
    LibsignalSpqrV1.Authenticator.macHdr_of_lt W.C.F auth0 1#64 hdr hmk_lt hhdr_lt
  have hmac_len : mac.length = 32 :=
    LibsignalSpqrV1.Authenticator.length_macHdrUnchecked W.C.F auth0 1#64 hdr
  obtain ⟨enc0, enc1, data, dec1, hPolyEnc, hPolyNext, hAddChunk, hDecMsg⟩ :=
    poly_firstHdrChunk_send_recv hdr mac hhdr hmac_len
  let enc0A : LibsignalSpqrV1.spqrPolyApi.PolyEncoder := enc0
  let enc1A : LibsignalSpqrV1.spqrPolyApi.PolyEncoder := enc1
  have hPolyEncA :
      LibsignalSpqrV1.expectEncodeBytes LibsignalSpqrV1.spqrPolyApi
        "v1/chunked/send_ek.rs:63" (hdr ++ mac) = .ok enc0A := hPolyEnc
  have hPolyNextA :
      LibsignalSpqrV1.spqrPolyApi.next_chunk enc0A =
        .ok (enc1A, { index := 0#16, data := data }) := hPolyNext
  obtain ⟨hMsgRaw, hMsgLen, hPreamble, hMsgDeser0⟩ :=
    msg_firstHdrChunk_roundtrip W.C.F W.Q.K data
  let msg0 : (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).MessageV1 :=
    { epoch := 1#64, payload := .hdr { index := 0#16, data := data } }
  have hMsgDeser :
      (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).msgDeserialize 1#64 (1#8 :: 0#8 :: data.toList) =
        .ok msg0 := hMsgDeser0
  let genr8r0 := LibsignalSpqrV1.spqrHkdfWith W.C.F (List.replicate 32 0#8) ak
    LibsignalSpqrV1.chainStartInfo 96
  let next0 := (genr8r0.drop 32).take 32
  have hnext0_len : next0.length = 32 := by simp [next0, genr8r0]
  have hNextKey :
      LibsignalSpqrV1.ChainEpochDirection.nextKeyInternal
        (LibsignalSpqrV1.spqrHkdfWith W.C.F) next0 0#32 =
      .ok (let g := LibsignalSpqrV1.spqrHkdfWith W.C.F (List.replicate 32 0#8) next0
                      (HMAC.toBEBytes 4 1#32 ++ LibsignalSpqrV1.chainNextInfo) 64
           (g.take 32, 1#32, (1#32, (g.drop 32).take 32))) := by
    simp [LibsignalSpqrV1.ChainEpochDirection.nextKeyInternal, hnext0_len]
  let gNext := LibsignalSpqrV1.spqrHkdfWith W.C.F (List.replicate 32 0#8) next0
    (HMAC.toBEBytes 4 1#32 ++ LibsignalSpqrV1.chainNextInfo) 64
  let msgKey := (gNext.drop 32).take 32
  have hmsgKey_len : msgKey.length = 32 := by simp [msgKey, gNext]
  have hmsgKey_ne : msgKey.isEmpty = false := by
    cases h : msgKey with
    | nil => simp [h] at hmsgKey_len
    | cons _ _ => rfl
  let msgKeyVec : List.Vector (BitVec 8) 32 := ⟨msgKey, hmsgKey_len⟩
  have hSalt : LibsignalSpqrV1.messageKeyToSalt? (some msgKey) = some (some msgKeyVec) := by
    simp [LibsignalSpqrV1.messageKeyToSalt?, hmsgKey_len, msgKeyVec]
  have hSaltRecv : LibsignalSpqrV1.recvKeyToSalt? (some msgKey) = some (some msgKeyVec) := by
    rw [LibsignalSpqrV1.recvKeyToSalt?_of_isSome (by rw [hSalt]; rfl), hSalt]
  let ced1 : LibsignalSpqrV1.ChainEpochDirection :=
    { ctr := 1#32, next := gNext.take 32, prev := { data := [] } }
  have hCedNextKey :
      (LibsignalSpqrV1.Chain.cedForDirection genr8r0 .a2b).nextKey
        (LibsignalSpqrV1.spqrHkdfWith W.C.F) =
      .ok (ced1, (1#32, msgKey)) := by
    dsimp only [LibsignalSpqrV1.Chain.cedForDirection,
      LibsignalSpqrV1.ChainEpochDirection.new,
      LibsignalSpqrV1.ChainEpochDirection.nextKey,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [hNextKey]; rfl
  have hKeyAdv :
      LibsignalSpqrV1.ChainEpochDirection.keyAdvanceLoop
        (LibsignalSpqrV1.spqrHkdfWith W.C.F)
        { ctr := 0#32, next := next0, prev := LibsignalSpqrV1.KeyHistory.new } 1#32 {} =
      .ok { ctr := 0#32, next := next0, prev := LibsignalSpqrV1.KeyHistory.new } := by
    rw [LibsignalSpqrV1.ChainEpochDirection.keyAdvanceLoop]; dsimp only
    have h6 : ¬ ((0#32 : BitVec 32).toNat + 1 < (1#32 : BitVec 32).toNat) := by decide
    have h7 : ((0#32 : BitVec 32) == 0xffffffff#32) = false := rfl
    simp only [h6, h7, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
  have hCedRecvKey :
      (LibsignalSpqrV1.Chain.cedForDirection genr8r0 .a2b).key
        (LibsignalSpqrV1.spqrHkdfWith W.C.F) 1#32 {} =
      .ok (ced1, msgKey) := by
    dsimp only [LibsignalSpqrV1.Chain.cedForDirection,
      LibsignalSpqrV1.ChainEpochDirection.new,
      LibsignalSpqrV1.ChainEpochDirection.key]
    have hJump : ({} : LibsignalSpqrV1.ChainParamsPB).maxJumpOrDefault = 25000#32 := by decide
    have hOoo : ({} : LibsignalSpqrV1.ChainParamsPB).maxOooKeysOrDefault = 2000#32 := by decide
    have h1 : ¬ ((1#32 : BitVec 32) < 0#32) := by decide
    have h2 : ((1#32 : BitVec 32) == 0#32) = false := rfl
    have h3 : ¬ ((1#32 : BitVec 32) - 0#32 > 25000#32) := by decide
    have h4 : ¬ ((0#32 : BitVec 32).toNat + (2000#32 : BitVec 32).toNat ≥ 2 ^ 32) := by decide
    have h5 : ¬ ((1#32 : BitVec 32) > 0#32 + 2000#32) := by decide
    have hGc : LibsignalSpqrV1.KeyHistory.new.gc 0#32 {} =
        .ok LibsignalSpqrV1.KeyHistory.new := by decide
    simp only [hJump, hOoo, h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte,
      Bind.bind, Except.bind, Pure.pure, Except.pure, LibsignalSpqrV1.ChainResult.ofPanic]
    rw [hKeyAdv]; dsimp only
    rw [hGc]; dsimp only [LibsignalSpqrV1.KeyHistory.new]
    rw [hNextKey]
  let chain0A : LibsignalSpqrV1.Chain :=
    { dir := .a2b, currentEpoch := 0#64, sendEpoch := 0#64,
      links := [{ send := LibsignalSpqrV1.Chain.cedForDirection genr8r0 .a2b
                  recv := LibsignalSpqrV1.Chain.cedForDirection genr8r0 .b2a }],
      nextRoot := genr8r0.take 32, params := {} }
  let chain0B : LibsignalSpqrV1.Chain :=
    { dir := .b2a, currentEpoch := 0#64, sendEpoch := 0#64,
      links := [{ send := LibsignalSpqrV1.Chain.cedForDirection genr8r0 .b2a
                  recv := LibsignalSpqrV1.Chain.cedForDirection genr8r0 .a2b }],
      nextRoot := genr8r0.take 32, params := {} }
  have hChainFromA :
      LibsignalSpqrV1.chainFromVersionNegotiation (LibsignalSpqrV1.spqrHkdfWith W.C.F)
        { authKey := ak, direction := 0#32, minVersion := 1#32, chainParams := some {} } =
      .ok chain0A := rfl
  have hChainFromB :
      LibsignalSpqrV1.chainFrom (LibsignalSpqrV1.spqrHkdfWith W.C.F) none
        (some { authKey := ak, direction := 1#32, minVersion := 1#32, chainParams := some {} }) =
      .ok chain0B := rfl
  have hepgt : ¬ ((1#64 - 1#64 : BitVec 64) > 0#64) := by decide
  have hepge : ¬ (BitVec.toNat (0#64 - (1#64 - 1#64 : BitVec 64)) ≥ 0 + 1) := by decide
  have hChainSendKey :
      chain0A.sendKey (LibsignalSpqrV1.spqrHkdfWith W.C.F) (1#64 - 1#64) =
      .ok ({ chain0A with
               links := [{ send := ced1
                           recv := LibsignalSpqrV1.Chain.cedForDirection genr8r0 .b2a }] },
           (1#32, msgKey)) := by
    have hep : chain0A.epochIdx (1#64 - 1#64) = .ok 0 := by
      dsimp only [LibsignalSpqrV1.Chain.epochIdx, chain0A, List.length_cons, List.length_nil]
      simp only [hepgt, hepge, ↓reduceIte]; rfl
    dsimp only [LibsignalSpqrV1.Chain.sendKey]; rw [hep]
    dsimp only [chain0A, LibsignalSpqrV1.ChainResult.ofError, LibsignalSpqrV1.ChainResult.ofPanic,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    have hlt : ¬ ((1#64 - 1#64 : BitVec 64) < 0#64) := by decide
    have hne : ((0#64 : BitVec 64) != (1#64 - 1#64)) = false := rfl
    simp only [hlt, hne, Bool.false_eq_true, ↓reduceIte, List.getElem?_cons_zero]
    rw [hCedNextKey]; rfl
  have hChainRecvKey :
      chain0B.recvKey (LibsignalSpqrV1.spqrHkdfWith W.C.F) (1#64 - 1#64) 1#32 =
      .ok ({ chain0B with links := [{ send := LibsignalSpqrV1.Chain.cedForDirection genr8r0 .b2a
                                      recv := ced1 }] },
           msgKey) := by
    have hep : chain0B.epochIdx (1#64 - 1#64) = .ok 0 := by
      dsimp only [LibsignalSpqrV1.Chain.epochIdx, chain0B, List.length_cons, List.length_nil]
      simp only [hepgt, hepge, ↓reduceIte]; rfl
    dsimp only [LibsignalSpqrV1.Chain.recvKey]; rw [hep]
    dsimp only [chain0B, LibsignalSpqrV1.ChainResult.ofError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    have hz : (((1#64 - 1#64 : BitVec 64) == 0#64) && ((1#32 : BitVec 32) == 0#32)) = false := rfl
    simp only [hz, Bool.false_eq_true, ↓reduceIte, List.getElem?_cons_zero]
    rw [hCedRecvKey]; rfl
  let stA0 : (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).States :=
    LibsignalSpqrV1.States.keysUnsampled { uc := { epoch := 1#64, auth := auth0A } }
  let stA0' : (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).States :=
    LibsignalSpqrV1.States.keysSampled
      { uc := { epoch := 1#64, auth := auth0A,
                ek := (W.Q.K.fromSeed rs).2.1.toList, dk := (W.Q.K.fromSeed rs).2.2.toList },
        sending_hdr := enc1A }
  let stB0 : (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).States :=
    LibsignalSpqrV1.States.noHeaderReceived
      { uc := { epoch := 1#64, auth := auth0A }, receiving_hdr := initHdrDec0 }
  let stB0' : (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).States :=
    LibsignalSpqrV1.States.noHeaderReceived
      { uc := { epoch := 1#64, auth := auth0A }, receiving_hdr := dec1 }
  have hFromPbA : (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).statesFromPb
      { innerState := some (.keysUnsampled
          { uc := some { epoch := 1#64,
                         auth := some { rootKey := auth0.rootKey, macKey := auth0.macKey } } }) } =
      .ok stA0 := rfl
  have hSendHdr : LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.send_header W.Q.K
      ({ epoch := 1#64, auth := auth0A } :
        LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled (LibsignalSpqrV1.spqrAuthApi W.C.F))
      rs.toList = .ok ({
        epoch := 1#64, auth := auth0A,
        ek := (W.Q.K.fromSeed rs).2.1.toList, dk := (W.Q.K.fromSeed rs).2.2.toList },
        hdr, mac, []) := by
    dsimp only [LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.send_header,
      Bind.bind, Except.bind, Pure.pure, Except.pure,
      monadLift, MonadLift.monadLift, LibsignalSpqrV1.liftSpqrPanic]
    rw [hGen]; dsimp only; rw [hMacHdr]; rfl
  have hStatesSend : ((LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).statesSend stA0 rs.toList).1 =
      .ok (msg0, none, stA0') := by
    dsimp only [stA0, stA0', msg0, LibsignalSpqrV1.spqrDeps, LibsignalSpqrV1.States.send,
      LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled.send_hdr_chunk,
      LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled.epoch, LibsignalSpqrV1.StatesResult.ofPanic,
      Bind.bind, Except.bind, Pure.pure, Except.pure,
      monadLift, MonadLift.monadLift, LibsignalSpqrV1.liftSpqrPanic]
    rw [hSendHdr]; dsimp only; rw [hPolyEncA]; dsimp only; rw [hPolyNextA]; rfl
  have hFromPbB : (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).statesFromPb
      { innerState := some (.noHeaderReceived
          { uc := some { epoch := 1#64,
                         auth := some { rootKey := auth0.rootKey, macKey := auth0.macKey } }
            receivingHdr := some initPd0 }) } = .ok stB0 := rfl
  have hStatesRecv : (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).statesRecv stB0 msg0 =
      .ok (none, stB0') := by
    dsimp only [stB0, stB0', msg0, LibsignalSpqrV1.spqrDeps, LibsignalSpqrV1.States.recv,
      LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.epoch,
      LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk]
    simp only [show ¬ ((1#64 : BitVec 64) > 1#64) by decide,
      show ((1#64 : BitVec 64) != 1#64) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      Bind.bind, Except.bind]
    rw [hAddChunk]; dsimp only; rw [hDecMsg]
  have hEpoch : (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).msgEpoch msg0 = 1#64 := rfl
  have hSend : ∃ stA1, (pqxdhSpqrSession W).send ((pqxdhSpqrSession W).init .a2b pqr0) rs.toList =
      some (stA1, some msgKeyVec,
        (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).msgSerialize msg0 1#32) := ⟨_, by
    rw [hInitA]; dsimp only [pqxdhSpqrSession, LibsignalSpqrV1.spqrV1Session,
      LibsignalTripleRatchet.SpqrModel.spqrWith, pqxdhSpqrModel, LibsignalSpqrV1.spqrV1,
      LibsignalSpqrV1.spqrV1Assembled, LibsignalSpqrV1.toSpqrModel, LibsignalSpqrV1.send]
    rw [hDecA]; dsimp only [initPbA]; rw [hFromPbA]; dsimp only; rw [hStatesSend]
    dsimp only [LibsignalSpqrV1.sendAfterStates, LibsignalSpqrV1.SpqrApiResult.ofError,
      LibsignalSpqrV1.SpqrApiResult.ofChainResult, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp only [show BitVec.slt LibsignalSpqrV1.Version.v0.toI32 1#32 = true from rfl, ↓reduceIte,
      hChainFromA, hEpoch, show ((1#64 : BitVec 64) == 0#64) = false from rfl,
      Bool.false_eq_true, hChainSendKey]
    rw [show (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).msgSerialize msg0 1#32 =
          [1#8, 1#8, 1#8, 1#8, 0#8] ++ data.toList from hMsgRaw]
    simp only [List.cons_append,
      show ((1#8 : BitVec 8) != LibsignalSpqrV1.Version.v1.toU8) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, hmsgKey_ne, hSalt]; rfl⟩
  obtain ⟨stA1, hSend⟩ := hSend
  have hRecv : ∃ stB1, (pqxdhSpqrSession W).recv ((pqxdhSpqrSession W).init .b2a pqr0)
      ((LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).msgSerialize msg0 1#32) =
      .ok (stB1, some msgKeyVec) := ⟨_, by
    rw [hInitB]; dsimp only [pqxdhSpqrSession, LibsignalSpqrV1.spqrV1Session,
      LibsignalTripleRatchet.SpqrModel.spqrWith, pqxdhSpqrModel, LibsignalSpqrV1.spqrV1,
      LibsignalSpqrV1.spqrV1Assembled, LibsignalSpqrV1.toSpqrModel, LibsignalSpqrV1.recv,
      LibsignalSpqrV1.SpqrApiResult.ofError, LibsignalSpqrV1.SpqrApiResult.ofChainResult,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [show LibsignalSpqrV1.msgPreamble
          ((LibsignalSpqrV1.spqrDeps W.C.F W.Q.K).msgSerialize msg0 1#32) =
          .ok { version := 1#8, epoch := 1#64, index := 1#32,
                remaining := 1#8 :: 0#8 :: data.toList } from hPreamble]
    dsimp only; rw [hDecB]
    dsimp only [initPbB, LibsignalSpqrV1.stateVersion, LibsignalSpqrV1.Version.toU8]
    simp only [show ¬ ((1#8 : BitVec 8) < (1#32 : BitVec 32).truncate 8) by decide,
      show (((1#8 : BitVec 8) != 1#8) && !true) = false from rfl,
      show ((1#8 : BitVec 8) == 0#8) = false from rfl,
      show ¬ ((1#8 : BitVec 8) > 1#8) by decide,
      show ((1#8 : BitVec 8) == 1#8) = true from rfl, Bool.false_eq_true, ↓reduceIte]
    rw [hMsgDeser]; dsimp only; rw [hFromPbB]; dsimp only; rw [hStatesRecv]; dsimp only
    simp only [show ((1#64 : BitVec 64) == 0#64) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, hChainFromB]
    rw [hChainRecvKey]; dsimp only
    simp only [hmsgKey_ne, Bool.false_eq_true, ↓reduceIte, hSaltRecv]; rfl⟩
  obtain ⟨stB1, hRecv⟩ := hRecv
  exact ⟨stA1, some msgKeyVec, _, stB1, hSend, hMsgLen, hRecv⟩

theorem spqrPq_sendPanics_false_of_send_some (W : PEParams) (st r : Bytes)
    {res : Bytes × Option (List.Vector (BitVec 8) 32) × Bytes}
    (h : (pqxdhSpqrSession W).send st r = some res) :
    (pqxdhSpqrSession W).sendPanics st r = false := by
  change (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr.send st r = some res at h
  change (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).sendPanics st r = false
  rw [LibsignalSpqrV1.spqrV1_eq] at h ⊢
  dsimp only [LibsignalSpqrV1.toSpqrModel, LibsignalTripleRatchet.SpqrModel.spqr,
    LibsignalSpqrV1.sendPanicsPureB] at h ⊢
  rcases hs : (LibsignalSpqrV1.send (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K)
      (LibsignalSpqrV1.spqrHkdfWith W.C.F) st r).1 with _ | s
  · rw [hs] at h; cases h
  · rfl

theorem spqrPq_recvPanics_false_of_recv_ok (W : PEParams) (st pm : Bytes)
    {res : Bytes × Option (List.Vector (BitVec 8) 32)}
    (h : (pqxdhSpqrSession W).recv st pm = .ok res) :
    (pqxdhSpqrSession W).recvPanics st pm = false := by
  change (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr.recv st pm = .ok res at h
  change (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).recvPanics st pm = false
  rw [LibsignalSpqrV1.spqrV1_eq] at h ⊢
  dsimp only [LibsignalSpqrV1.toSpqrModel, LibsignalTripleRatchet.SpqrModel.spqr,
    LibsignalSpqrV1.recvPanicsB] at h ⊢
  rcases hr : LibsignalSpqrV1.recv (LibsignalSpqrV1.spqrDeps W.C.F W.Q.K)
      (LibsignalSpqrV1.spqrHkdfWith W.C.F) st pm with e | r
  · rw [hr] at h; cases e <;> cases h
  · rfl

end CryptoVerification.SignalSession.FirstMessage
