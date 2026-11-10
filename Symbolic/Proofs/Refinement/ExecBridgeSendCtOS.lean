/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import Symbolic.Specifications.Refinement.Concretization
import Symbolic.Proofs.Refinement.RecordBytesBridge

/-!
# HKDF Expansion and Canonical Wire Serialization Bridges for `session_send`

Provides `DY.Bytes.SubFunction` instances into `concretizeAll`, unfolds 80-byte HKDF-SHA256
expansion into three HMAC blocks (`hkdfExpand_80_eq_blocks`), and relates `serializeContent`
under `protoSignalCodec` to `encodeWith canonicalVariation`.
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.libsignal.Refinement.ExecBridgeSendCtOS

open CryptoVerification
open CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalProtoCodec
open DY DY.Comparse
open DY.Libsignal.Refinement DY.Libsignal.TripleRatchet
open DY.Libsignal.Composed.Refinement
open CryptoProofLib.Refinement (ExternInterpretation)
open Swarm.Phase0WholeFunctionBridge (paddedVarint_zero_eq_encodeVarint)

section FoldInstances
variable (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
unseal DY.Bytes in
local instance : DY.Bytes.SubFunction concretizeLit (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
local instance : DY.Bytes.SubFunction concretizeConcat (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
local instance : DY.Bytes.SubFunction (concretizeKdf interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
local instance : DY.Bytes.SubFunction concretizeTrunc (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

end FoldInstances

private theorem hmacWith_length_32 (F : ShaState → List (BitVec 8) → ShaState)
    (k m : List (BitVec 8)) :
    (CryptoGames.HMAC.hmacWith F k m).length = 32 := by
  unfold CryptoGames.HMAC.hmacWith CryptoGames.HMAC.sha256With
  generalize (CryptoGames.HMAC.chunks64 (CryptoGames.HMAC.sha256Pad _)).foldl F
    CryptoGames.HMAC.sha256IV = s
  rcases s with ⟨l, hl⟩
  simp [CryptoGames.HMAC.toBEBytes, List.length_flatMap]

theorem hkdfExpand_80_eq_blocks (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) :
    hkdfExpand F prk info 80 =
      ByteSpecs.hmacWith F prk (info ++ [1#8]) ++
      ByteSpecs.hmacWith F prk
        (ByteSpecs.hmacWith F prk (info ++ [1#8]) ++ info ++ [2#8]) ++
      (ByteSpecs.hmacWith F prk
        (ByteSpecs.hmacWith F prk
          (ByteSpecs.hmacWith F prk (info ++ [1#8]) ++ info ++ [2#8]) ++
          info ++ [3#8])).take 16 := by
  dsimp only [hkdfExpand]
  have h3 : (80 + 31) / 32 = 3 := rfl
  let b1 := CryptoGames.HMAC.hmacWith F prk (info ++ [1#8])
  let b2 := CryptoGames.HMAC.hmacWith F prk (b1 ++ info ++ [2#8])
  let b3 := CryptoGames.HMAC.hmacWith F prk (b2 ++ info ++ [3#8])
  have hblocks : (hkdfBlocks F prk info 3).flatten = (b1 ++ b2) ++ b3 := by
    simp [hkdfBlocks, b1, b2, b3, List.append_assoc]
  have hb1 : b1.length = 32 := hmacWith_length_32 F _ _
  have hb2 : b2.length = 32 := hmacWith_length_32 F _ _
  have hlen12 : (b1 ++ b2).length = 64 := by simp [hb1, hb2]
  rw [h3, hblocks, List.take_append, List.take_of_length_le (by omega), hlen12]
  rfl

theorem serializeContent_eq_encodeWith_canonicalVariation
    (rk : PublicKey)
    (counter previousCounter : BitVec 32)
    (ctext : List (BitVec 8))
    (hct : ctext.length < 2 ^ 64) :
    serializeContent protoSignalCodec 4#8 rk
      counter previousCounter ctext [] none =
    encodeWith canonicalVariation
      { version := 4
        ratchetKey := rk.bytes.toList
        counter := counter.toNat
        previousCounter := previousCounter.toNat
        ciphertext := ctext } := by
  have hv : versionByte 4#8 = BitVec.ofNat 8 (4 * 16 + 4 % 16) := by decide
  have hk1 : CryptoVerification.LibsignalProtoCodec.encodeKey 1 .lengthDelimited =
      paddedVarint (1 * 8 + 2) 0 := by
    change CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 1 <<< 3 ||| BitVec.ofNat 64 2) = _
    rw [show (BitVec.ofNat 64 1 <<< 3 ||| BitVec.ofNat 64 2) = BitVec.ofNat 64 10 by decide]
    exact (paddedVarint_zero_eq_encodeVarint 10 (by decide)).symm
  have hk2 : CryptoVerification.LibsignalProtoCodec.encodeKey 2 .varint =
      paddedVarint (2 * 8) 0 := by
    change CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 2 <<< 3 ||| BitVec.ofNat 64 0) = _
    rw [show (BitVec.ofNat 64 2 <<< 3 ||| BitVec.ofNat 64 0) = BitVec.ofNat 64 16 by decide]
    exact (paddedVarint_zero_eq_encodeVarint 16 (by decide)).symm
  have hk3 : CryptoVerification.LibsignalProtoCodec.encodeKey 3 .varint =
      paddedVarint (3 * 8) 0 := by
    change CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 3 <<< 3 ||| BitVec.ofNat 64 0) = _
    rw [show (BitVec.ofNat 64 3 <<< 3 ||| BitVec.ofNat 64 0) = BitVec.ofNat 64 24 by decide]
    exact (paddedVarint_zero_eq_encodeVarint 24 (by decide)).symm
  have hk4 : CryptoVerification.LibsignalProtoCodec.encodeKey 4 .lengthDelimited =
      paddedVarint (4 * 8 + 2) 0 := by
    change CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 4 <<< 3 ||| BitVec.ofNat 64 2) = _
    rw [show (BitVec.ofNat 64 4 <<< 3 ||| BitVec.ofNat 64 2) = BitVec.ofNat 64 34 by decide]
    exact (paddedVarint_zero_eq_encodeVarint 34 (by decide)).symm
  have hrk_len : rk.serialize.length < 2 ^ 64 := by
    unfold PublicKey.serialize
    have h32 : rk.bytes.toList.length = 32 := rk.bytes.toList_length
    simp [h32]
  have hlen1 := (paddedVarint_zero_eq_encodeVarint rk.serialize.length hrk_len).symm
  have hlen4 := (paddedVarint_zero_eq_encodeVarint ctext.length hct).symm
  have hz2 : counter.zeroExtend 64 = BitVec.ofNat 64 counter.toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  have hc2 : CryptoVerification.LibsignalProtoCodec.encodeVarint (counter.zeroExtend 64) =
      paddedVarint counter.toNat 0 := by
    rw [hz2, ← paddedVarint_zero_eq_encodeVarint counter.toNat (by have := counter.isLt; omega)]
  have hz3 : previousCounter.zeroExtend 64 = BitVec.ofNat 64 previousCounter.toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  have hc3 : CryptoVerification.LibsignalProtoCodec.encodeVarint (previousCounter.zeroExtend 64) =
      paddedVarint previousCounter.toNat 0 := by
    rw [hz3, ← paddedVarint_zero_eq_encodeVarint previousCounter.toNat (by have := previousCounter.isLt; omega)]
  have hrk_eq : 0x05#8 :: rk.bytes.toList = rk.serialize := rfl
  change versionByte 4#8 ::
    ((CryptoVerification.LibsignalProtoCodec.encodeKey 1 .lengthDelimited ++
      CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 rk.serialize.length) ++
      rk.serialize) ++
     (CryptoVerification.LibsignalProtoCodec.encodeKey 2 .varint ++
      CryptoVerification.LibsignalProtoCodec.encodeVarint (counter.zeroExtend 64)) ++
     (CryptoVerification.LibsignalProtoCodec.encodeKey 3 .varint ++
      CryptoVerification.LibsignalProtoCodec.encodeVarint (previousCounter.zeroExtend 64)) ++
     (CryptoVerification.LibsignalProtoCodec.encodeKey 4 .lengthDelimited ++
      CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 ctext.length) ++
      ctext) ++ [] ++ []) =
    BitVec.ofNat 8 (4 * 16 + 4 % 16) ::
      ((paddedVarint (1 * 8 + 2) 0 ++
        paddedVarint (0x05#8 :: rk.bytes.toList ++ []).length 0 ++
        (0x05#8 :: rk.bytes.toList ++ [])) ++
       ((paddedVarint (2 * 8) 0 ++ paddedVarint (counter.toNat + 2 ^ 32 * 0) 0) ++
        ((paddedVarint (3 * 8) 0 ++ paddedVarint (previousCounter.toNat + 2 ^ 32 * 0) 0) ++
         ((paddedVarint (4 * 8 + 2) 0 ++ paddedVarint ctext.length 0 ++ ctext) ++ []))))
  simp only [List.append_nil, Nat.mul_zero, Nat.add_zero, hrk_eq]
  rw [hv, hk1, hk2, hk3, hk4, hlen1, hlen4, hc2, hc3]
  simp only [List.append_assoc]

end Proofs.libsignal.Refinement.ExecBridgeSendCtOS
