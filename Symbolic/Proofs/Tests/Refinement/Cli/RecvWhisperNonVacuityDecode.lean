/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Refinement.Cli.RecvWhisperNonVacuitySteps12

/-!
# Concrete SPQR-ON Non-Vacuity Protobuf State Decode

Length-delimited protobuf skip lemmas for opaque 1152-byte `ek` and 2400-byte `dk` ML-KEM keys,
proving `decodeState` on Alice's SPQR V1 state `nvPqA1` without unfolding large key vectors.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers

open DY.Libsignal (HwBytes)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession

set_option maxRecDepth 8192

theorem takeExact_append :
    ∀ (xs ys : HwBytes),
      CryptoVerification.LibsignalSpqrV1.Proto.takeExact xs.length (xs ++ ys) = .ok (xs, ys)
  | [], _ => rfl
  | _ :: xs, ys => by
    simp [CryptoVerification.LibsignalSpqrV1.Proto.takeExact, takeExact_append xs ys,
      Bind.bind, Except.bind]

theorem mergeBytes_nvEk1152 (after : HwBytes) :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited
      (0x80#8 :: 0x09#8 :: (nvEk1152 ++ after)) = .ok (nvEk1152, after) := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes
    CryptoVerification.LibsignalSpqrV1.Proto.checkWireType
  have hvar : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint
      (0x80#8 :: 0x09#8 :: (nvEk1152 ++ after)) =
      .ok (1152#64, nvEk1152 ++ after) := rfl
  rw [hvar]
  dsimp only [Bind.bind, Except.bind]
  rw [show (1152#64 : BitVec 64).toNat = nvEk1152.length from nvEk1152_len.symm]
  exact takeExact_append nvEk1152 after

theorem mergeBytes_nvDk2400 (after : HwBytes) :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited
      (0xe0#8 :: 0x12#8 :: (nvDk2400 ++ after)) = .ok (nvDk2400, after) := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes
    CryptoVerification.LibsignalSpqrV1.Proto.checkWireType
  have hvar : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint
      (0xe0#8 :: 0x12#8 :: (nvDk2400 ++ after)) =
      .ok (2400#64, nvDk2400 ++ after) := rfl
  rw [hvar]
  dsimp only [Bind.bind, Except.bind]
  rw [show (2400#64 : BitVec 64).toNat = nvDk2400.length from nvDk2400_len.symm]
  exact takeExact_append nvDk2400 after

theorem encodeBytesField_nvEk1152 :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 nvEk1152 =
      [0x1a#8, 0x80#8, 0x09#8] ++ nvEk1152 := by
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, nvEk1152_isEmpty,
    Bool.false_eq_true, ↓reduceIte, CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond,
    nvEk1152_len]
  rfl

theorem encodeBytesField_nvDk2400 :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 nvDk2400 =
      [0x22#8, 0xe0#8, 0x12#8] ++ nvDk2400 := by
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, nvDk2400_isEmpty,
    Bool.false_eq_true, ↓reduceIte, CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond,
    nvDk2400_len]
  rfl

theorem mergeMessage_of_len {M : Type}
    (mergeField : M → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType →
      HwBytes → Nat → Except CryptoVerification.LibsignalSpqrV1.Proto.DecodeErr (M × HwBytes))
    (m m' : M) (n : Nat) (sub after : HwBytes) (depth' : Nat)
    (hlen : sub.length = n)
    (hvar : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 n) ++
          (sub ++ after)) =
      .ok (BitVec.ofNat 64 n, sub ++ after))
    (hn : (BitVec.ofNat 64 n).toNat = n)
    (hloop : CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
      mergeField n m sub depth' = .ok m') :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage mergeField .lengthDelimited m
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 n) ++
        (sub ++ after)) (depth' + 1) = .ok (m', after) := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
    CryptoVerification.LibsignalSpqrV1.Proto.checkWireType
  simp only [show (CryptoVerification.LibsignalSpqrV1.Proto.WireType.lengthDelimited !=
      CryptoVerification.LibsignalSpqrV1.Proto.WireType.lengthDelimited) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  rw [hvar]
  dsimp only
  rw [hn, ← hlen, takeExact_append sub after]
  dsimp only
  rw [hlen, hloop]

theorem mergeFieldsLoop_step_nil {M : Type}
    (mergeField : M → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType →
      HwBytes → Nat → Except CryptoVerification.LibsignalSpqrV1.Proto.DecodeErr (M × HwBytes))
    (fuel : Nat) (m m' : M) (tag : BitVec 32)
    (wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType)
    (bs rest : HwBytes) (depth : Nat)
    (hk : CryptoVerification.LibsignalSpqrV1.Proto.decodeKey bs = .ok ((tag, wt), rest))
    (hm : mergeField m tag wt rest depth = .ok (m', [])) :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop mergeField (fuel + 1) m bs depth =
      .ok m' := by
  cases bs with
  | nil => cases hk
  | cons b tl =>
    unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
    dsimp only [Bind.bind, Except.bind]
    rw [hk]
    dsimp only
    rw [hm]
    dsimp only
    unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
    rfl

def nvPePb : CryptoVerification.LibsignalSpqrV1.PolynomialEncoder :=
  CryptoVerification.LibsignalSpqrV1.protoPolyEncoderToPb nvPe1Chunk.1.intoPb

def nvPeBody : HwBytes :=
  let raw := CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw nvPePb
  CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 raw.length) ++ raw

def nvPeRaw : HwBytes := 0x12#8 :: nvPeBody

def nvUcLen : Nat :=
  (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 1#64).length +
  (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
    CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw 2#32
    (some nvAuth0.intoPb)).length +
  (3 + 1152 + 3 + 2400)

def nvKsLen : Nat :=
  1 + (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 nvUcLen)).length +
    nvUcLen + (1 + nvPeBody.length)

def nvV1Len : Nat :=
  1 + (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 nvKsLen)).length +
    nvKsLen

def nvUcPb : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent :=
  { epoch := 1#64, auth := some nvAuth0.intoPb, ek := nvEk1152, dk := nvDk2400 }

def nvKsPb : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled :=
  { uc := some nvUcPb, sendingHdr := some nvPePb }

def nvV1Pb : CryptoVerification.LibsignalSpqrV1.V1State :=
  { innerState := some (.keysSampled nvKsPb) }

theorem nvUcRaw_eq :
    CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw nvUcPb =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 1#64 ++
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
         CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw 2#32 (some nvAuth0.intoPb) ++
       (0x1a#8 :: 0x80#8 :: 0x09#8 :: (nvEk1152 ++ (0x22#8 :: 0xe0#8 :: 0x12#8 :: nvDk2400)))) := by
  simp only [CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw, nvUcPb,
    encodeBytesField_nvEk1152, encodeBytesField_nvDk2400, List.append_assoc, List.cons_append,
    List.nil_append]

theorem nvUcLen_eq :
    (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw nvUcPb).length =
      nvUcLen := by
  rw [nvUcRaw_eq]
  simp only [List.length_append, List.length_cons, nvEk1152_len, nvDk2400_len,
    nvUcLen]
  omega

theorem nv_ucLoop :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
      CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.mergeField
      nvUcLen default
      (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw nvUcPb) 97 =
    .ok nvUcPb := by
  have hge : 4 ≤ nvUcLen := by dsimp only [nvUcLen]; omega
  obtain ⟨fu, hfu⟩ : ∃ fu, nvUcLen = fu + 4 := ⟨nvUcLen - 4, by omega⟩
  rw [hfu, nvUcRaw_eq]
  have hstep12 : ∀ rest,
      CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
        CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.mergeField
        (fu + 4) default
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 1#64 ++
          (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
             CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw 2#32
             (some nvAuth0.intoPb) ++ rest)) 97 =
      CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
        CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.mergeField
        (fu + 2) { epoch := 1#64, auth := some nvAuth0.intoPb, ek := [], dk := [] }
        rest 97 := fun _ => rfl
  rw [hstep12]
  change CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
      CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.mergeField
      ((fu + 1) + 1) _
      (0x1a#8 :: 0x80#8 :: 0x09#8 :: (nvEk1152 ++ (0x22#8 :: 0xe0#8 :: 0x12#8 :: nvDk2400)))
      97 = .ok nvUcPb
  unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
  have hk3 : CryptoVerification.LibsignalSpqrV1.Proto.decodeKey
      (0x1a#8 :: 0x80#8 :: 0x09#8 :: (nvEk1152 ++ (0x22#8 :: 0xe0#8 :: 0x12#8 :: nvDk2400))) =
      .ok ((3#32, .lengthDelimited),
           0x80#8 :: 0x09#8 :: (nvEk1152 ++ (0x22#8 :: 0xe0#8 :: 0x12#8 :: nvDk2400))) := rfl
  rw [hk3]
  dsimp only [Bind.bind, Except.bind,
    CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.mergeField]
  simp only [show (3#32 == (1#32 : BitVec 32)) = false from rfl,
    show (3#32 == (2#32 : BitVec 32)) = false from rfl,
    show (3#32 == (3#32 : BitVec 32)) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [mergeBytes_nvEk1152]
  dsimp only
  exact mergeFieldsLoop_step_nil
    CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.mergeField
    fu _ nvUcPb 4#32 .lengthDelimited
    (0x22#8 :: 0xe0#8 :: 0x12#8 :: nvDk2400)
    (0xe0#8 :: 0x12#8 :: nvDk2400) 97 rfl (by
      dsimp only [Bind.bind, Except.bind,
        CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.mergeField]
      simp only [show (4#32 == (1#32 : BitVec 32)) = false from rfl,
        show (4#32 == (2#32 : BitVec 32)) = false from rfl,
        show (4#32 == (3#32 : BitVec 32)) = false from rfl,
        show (4#32 == (4#32 : BitVec 32)) = true from rfl, Bool.false_eq_true, ↓reduceIte]
      have hd0 : 0xe0#8 :: 0x12#8 :: nvDk2400 = 0xe0#8 :: 0x12#8 :: (nvDk2400 ++ []) := by
        rw [List.append_nil]
      rw [hd0, mergeBytes_nvDk2400 []]
      rfl)

theorem nvKsRaw_eq :
    CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.encodeRaw nvKsPb =
      0x0a#8 :: (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 nvUcLen) ++
        (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw nvUcPb ++
          nvPeRaw)) := by
  simp only [CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.encodeRaw, nvKsPb,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, nvUcLen_eq, nvPeRaw, nvPeBody]
  rfl

theorem nvKsLen_eq :
    (CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.encodeRaw nvKsPb).length =
      nvKsLen := by
  rw [nvKsRaw_eq]
  simp only [List.length_cons, List.length_append, nvUcLen_eq, nvPeRaw, nvKsLen]
  omega

theorem nv_peMerge :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeOptMessage
      CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.mergeField
      .lengthDelimited none nvPeBody 98 = .ok (some nvPePb, []) := rfl

theorem nv_ksLoop :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
      CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.mergeField
      nvKsLen default
      (CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.encodeRaw nvKsPb) 98 =
    .ok nvKsPb := by
  have hUcVar : ∀ after,
      CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 nvUcLen) ++ after) =
      .ok (BitVec.ofNat 64 nvUcLen, after) := fun _ => rfl
  have hUcNat : (BitVec.ofNat 64 nvUcLen).toNat = nvUcLen := rfl
  have hkl : ∃ f2, nvKsLen = f2 + 2 := ⟨nvKsLen - 2, by dsimp [nvKsLen, nvUcLen]; omega⟩
  obtain ⟨f2, hf2⟩ := hkl
  rw [hf2, nvKsRaw_eq]
  have hDefKs : (default : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled) =
      { uc := none, sendingHdr := none } := rfl
  rw [hDefKs]
  change CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
    CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.mergeField
    (f2 + 1 + 1) { uc := none, sendingHdr := none } _ 98 = .ok nvKsPb
  unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
  have hk1 : ∀ rest, CryptoVerification.LibsignalSpqrV1.Proto.decodeKey (0x0a#8 :: rest) =
      .ok ((1#32, .lengthDelimited), rest) := fun _ => rfl
  rw [hk1]
  dsimp only [Bind.bind, Except.bind, Option.getD,
    CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.mergeField,
    CryptoVerification.LibsignalSpqrV1.Proto.mergeOptMessage]
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [mergeMessage_of_len
    CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.mergeField
    default nvUcPb nvUcLen _ nvPeRaw 97 nvUcLen_eq (hUcVar _) hUcNat nv_ucLoop]
  dsimp only
  exact mergeFieldsLoop_step_nil
    CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.mergeField
    f2 { uc := some nvUcPb, sendingHdr := none } nvKsPb 2#32 .lengthDelimited nvPeRaw nvPeBody 98
    rfl (by
      dsimp only [Bind.bind, Except.bind,
        CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.mergeField]
      simp only [show (2#32 == (1#32 : BitVec 32)) = false from rfl,
        show (2#32 == (2#32 : BitVec 32)) = true from rfl, Bool.false_eq_true, ↓reduceIte,
        nv_peMerge]
      rfl)

theorem nvV1Raw_eq :
    CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw nvV1Pb =
      0x12#8 :: (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 nvKsLen) ++
        (CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.encodeRaw nvKsPb ++ [])) := by
  rw [List.append_nil]
  simp only [CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw, nvV1Pb,
    CryptoVerification.LibsignalSpqrV1.V1State.InnerState.encode,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, nvKsLen_eq]
  rfl

theorem nvV1Len_eq :
    (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw nvV1Pb).length = nvV1Len := by
  rw [nvV1Raw_eq, List.append_nil]
  simp only [List.length_cons, List.length_append, nvKsLen_eq, nvV1Len]
  omega

theorem nv_v1Loop :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
      CryptoVerification.LibsignalSpqrV1.V1State.mergeField nvV1Len default
      (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw nvV1Pb) 99 = .ok nvV1Pb := by
  have hV1Var : ∀ after,
      CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 nvKsLen) ++ after) =
      .ok (BitVec.ofNat 64 nvKsLen, after) := fun _ => rfl
  have hKsNat : (BitVec.ofNat 64 nvKsLen).toNat = nvKsLen := rfl
  have hvl : ∃ f1, nvV1Len = f1 + 1 := ⟨nvV1Len - 1, by dsimp [nvV1Len, nvKsLen, nvUcLen]; omega⟩
  obtain ⟨f1, hf1⟩ := hvl
  rw [hf1, nvV1Raw_eq]
  exact mergeFieldsLoop_step_nil
    CryptoVerification.LibsignalSpqrV1.V1State.mergeField f1 default nvV1Pb 2#32 .lengthDelimited
    _ _ 99 rfl (by
      dsimp only [Bind.bind, Except.bind, CryptoVerification.LibsignalSpqrV1.V1State.mergeField,
        CryptoVerification.LibsignalSpqrV1.V1State.InnerState.merge]
      have hDefV1 : (default : CryptoVerification.LibsignalSpqrV1.V1State).innerState = none := rfl
      rw [hDefV1]
      simp only [show ((2#32 : BitVec 32) ≥ 1#32 && (2#32 : BitVec 32) ≤ 11#32) = true from rfl,
        show (2#32 == (1#32 : BitVec 32)) = false from rfl,
        show (2#32 == (2#32 : BitVec 32)) = true from rfl, Bool.false_eq_true, ↓reduceIte]
      rw [mergeMessage_of_len
        CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.mergeField
        default nvKsPb nvKsLen _ [] 98 nvKsLen_eq (hV1Var _) hKsNat nv_ksLoop]
      rfl)

theorem nv_decode_nvPbA1 :
    CryptoVerification.LibsignalSpqrV1.decodeState
      (CryptoVerification.LibsignalSpqrV1.spqrDeps nvCrypto.F nvMlKem) nvPqA1 = .ok nvPbA1 := by
  let vnChRaw := CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB.encodeRaw 1#32 (some nvVnA) ++
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      CryptoVerification.LibsignalSpqrV1.ChainPB.encodeRaw 2#32 (some nvChA1Key.1.intoPb)
  let innerRaw := 0x1a#8 ::
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 nvV1Len) ++
      (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw nvV1Pb ++ []))
  have hPbEq : nvPbA1 = { inner := some nvV1Pb, versionNegotiation := some nvVnA,
                          chain := some nvChA1Key.1.intoPb } := rfl
  have hPqRaw : nvPqA1 = vnChRaw ++ innerRaw := by
    change CryptoVerification.LibsignalSpqrV1.Proto.encodeState
        (CryptoVerification.LibsignalSpqrV1.pbToPqRatchetState nvPbA1) = vnChRaw ++ innerRaw
    rw [hPbEq]
    dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeState,
      CryptoVerification.LibsignalSpqrV1.pbToPqRatchetState, Option.map,
      CryptoVerification.LibsignalSpqrV1.PqRatchetState.encode,
      CryptoVerification.LibsignalSpqrV1.PqRatchetState.encodeRaw,
      CryptoVerification.LibsignalSpqrV1.PqRatchetState.Inner.encode,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, vnChRaw, innerRaw]
    have hkey3 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited =
        [0x1a#8] := rfl
    rw [hkey3, nvV1Len_eq]
    simp only [List.append_nil, List.nil_append, List.cons_append, List.append_assoc]
  have hPqNe : nvPqA1.isEmpty = false := by
    rw [hPqRaw]
    rfl
  have hPqLenGe : 3 ≤ (vnChRaw ++ innerRaw).length := by
    dsimp only [innerRaw]
    simp only [List.length_append, List.length_cons, nvV1Len_eq]
    dsimp only [nvV1Len, nvKsLen, nvUcLen]
    omega
  have hOuterLoop : CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
      CryptoVerification.LibsignalSpqrV1.PqRatchetState.mergeField (vnChRaw ++ innerRaw).length
      default (vnChRaw ++ innerRaw) 100 =
    .ok { versionNegotiation := some nvVnA, chain := some nvChA1Key.1.intoPb,
          inner := some (.v1 nvV1Pb) } := by
    obtain ⟨f3, hf3⟩ : ∃ f3, (vnChRaw ++ innerRaw).length = f3 + 3 :=
      ⟨(vnChRaw ++ innerRaw).length - 3, by omega⟩
    rw [hf3]
    have hstepVnCh : ∀ rest,
        CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
          CryptoVerification.LibsignalSpqrV1.PqRatchetState.mergeField (f3 + 3) default
          (vnChRaw ++ rest) 100 =
        CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
          CryptoVerification.LibsignalSpqrV1.PqRatchetState.mergeField (f3 + 1)
          { versionNegotiation := some nvVnA, chain := some nvChA1Key.1.intoPb, inner := none }
          rest 100 := fun _ => rfl
    rw [hstepVnCh]
    have hV1VarOuter : ∀ after,
        CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint
          (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 nvV1Len) ++ after) =
        .ok (BitVec.ofNat 64 nvV1Len, after) := fun _ => rfl
    have hV1Nat : (BitVec.ofNat 64 nvV1Len).toNat = nvV1Len := rfl
    exact mergeFieldsLoop_step_nil
      CryptoVerification.LibsignalSpqrV1.PqRatchetState.mergeField f3
      { versionNegotiation := some nvVnA, chain := some nvChA1Key.1.intoPb, inner := none }
      { versionNegotiation := some nvVnA, chain := some nvChA1Key.1.intoPb,
        inner := some (.v1 nvV1Pb) }
      3#32 .lengthDelimited innerRaw _ 100 rfl (by
        dsimp only [Bind.bind, Except.bind,
          CryptoVerification.LibsignalSpqrV1.PqRatchetState.mergeField,
          CryptoVerification.LibsignalSpqrV1.PqRatchetState.Inner.merge]
        simp only [show (3#32 == (1#32 : BitVec 32)) = false from rfl,
          show (3#32 == (2#32 : BitVec 32)) = false from rfl,
          show (3#32 == (3#32 : BitVec 32)) = true from rfl, Bool.false_eq_true, ↓reduceIte]
        rw [mergeMessage_of_len CryptoVerification.LibsignalSpqrV1.V1State.mergeField
          default nvV1Pb nvV1Len _ [] 99 nvV1Len_eq (hV1VarOuter _) hV1Nat nv_v1Loop])
  unfold CryptoVerification.LibsignalSpqrV1.decodeState
  rw [hPqNe]
  simp only [Bool.false_eq_true, ↓reduceIte]
  dsimp only [CryptoVerification.LibsignalSpqrV1.spqrDeps,
    CryptoVerification.LibsignalSpqrV1.Proto.decodeState,
    CryptoVerification.LibsignalSpqrV1.PqRatchetState.decode,
    CryptoVerification.LibsignalSpqrV1.Proto.decodeTopLevelMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.mergeTopLevelMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.RECURSION_LIMIT]
  conv => lhs; rw [hPqRaw, hOuterLoop]
  rfl

end Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
