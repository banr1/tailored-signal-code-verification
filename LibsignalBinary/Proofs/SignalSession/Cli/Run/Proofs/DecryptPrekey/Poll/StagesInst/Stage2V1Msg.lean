/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Bridge
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPre

/-!
# CLI Poll Stage P2 V1 Message Header and Unpack Bridges

Defines `mkPathAHdr` and proves bidirectional spatial message unpacking and reassembly between
`preKeyMsgAt` on `pmOfE m i` and `p2MsgFieldsAt`, `signalMessageRestVerAt`, and
`pathAMsgRemInnerAt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Canonical `HandshakeHdr` extracted from a typed `PreKeyMessageFields`. -/
def mkPathAHdr (m : PreKeyMessageFields) : HandshakeHdr where
  ikAPk := E2E.vecU8 m.idPub
  ekAPk := E2E.vecU8 m.baseKey
  spkId := u32 m.spkId
  opkId? := m.opkId.map u32
  pqspkId := u32 m.kpkId
  kemCt := E2E.vecU8 m.kyberCt

private theorem toBitVec_u32 (w : BitVec 32) : (u32 w).toBitVec = w :=
  UInt32.toBitVec_ofBitVec w

theorem hdrOpkIdBv?_mkPathAHdr (m : PreKeyMessageFields) :
    hdrOpkIdBv? (mkPathAHdr m) = m.opkId := by
  unfold hdrOpkIdBv? mkPathAHdr
  cases m.opkId with
  | none => rfl
  | some w => simp [toBitVec_u32]

private theorem ofU8_toU8_list : ∀ bs : List (BitVec 8), ofU8 (E2E.toU8 bs) = bs
  | [] => rfl
  | _ :: rest => congrArg₂ List.cons rfl (ofU8_toU8_list rest)

private theorem bytesToBv8_eq_ofU8 : ∀ bs : List UInt8, bytesToBv8 bs = ofU8 bs
  | [] => rfl
  | b :: rest => congrArg₂ List.cons
      ((BitVec.ofNat_toNat 8 b.toBitVec).trans b.toBitVec.setWidth_eq)
      (bytesToBv8_eq_ofU8 rest)

theorem bytesToBv8_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) :
    bytesToBv8 (E2E.vecU8 v) = v.toList := by
  rw [bytesToBv8_eq_ofU8, E2E.vecU8, ofU8_toU8_list]

theorem vecU8_length {n : Nat} (v : List.Vector (BitVec 8) n) :
    (E2E.vecU8 v).length = n := by
  simp [E2E.vecU8, E2E.toU8, v.toList_length]

/-- Remainder of `preKeyMsgRemBaseIdKeyAt` after carving out the read-only fields in `p2MsgFieldsAt`. -/
def pathAMsgRemInnerAt (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (m : PreKeyMessageFields) (i : SignalMessage) : SepProp :=
  ⌜g.kyberPtr ≠ 0 ∧ 1569 < 2 ^ 63⌝ ∗
  E2E.HooksE.A0.live g.kyberPtr 1569 1 ∗
  memRegion (msgA + 0xa4#64) 4 ∗
  boxU8At E2E.HooksE.A0 (msgA + 0x80#64) g.serPtr (pmOfE m i).serialized ∗
  memRegion (msgA + 0xf1#64) 7

/-- `A`-polymorphic generalization of `pathAMsgRemInnerAt` over `(A : RustAlloc)`. -/
def pathAMsgRemInnerAtExt (A : RustAlloc) (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (m : PreKeyMessageFields) (i : SignalMessage) : SepProp :=
  ⌜g.kyberPtr ≠ 0 ∧ 1569 < 2 ^ 63⌝ ∗
  A.live g.kyberPtr 1569 1 ∗
  memRegion (msgA + 0xa4#64) 4 ∗
  boxU8At A (msgA + 0x80#64) g.serPtr (pmOfE m i).serialized ∗
  memRegion (msgA + 0xf1#64) 7

theorem pathAMsgRemInnerAt_eq_A0 (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (m : PreKeyMessageFields) (i : SignalMessage) :
    pathAMsgRemInnerAt g msgA m i = pathAMsgRemInnerAtExt E2E.HooksE.A0 g msgA m i :=
  rfl

/-- `A`-polymorphic unpack of `preKeyMsgAt` on `pmOfE m i` into `p2MsgFieldsAt` +
`signalMessageRestVerAt` + `pathAMsgRemInnerAtExt`. -/
theorem preKeyMsgAt_unpack_pathA_ext (A : RustAlloc) (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (m : PreKeyMessageFields) (i : SignalMessage) :
    preKeyMsgAt A g msgA (pmOfE m i) ⊢
      ∃∗ opkWord : BitVec 32,
        ⌜∀ id : BitVec 32, m.opkId = some id → opkWord = id⌝ ∗
        p2MsgFieldsAt msgA g.kyberPtr (mkPathAHdr m) i.messageVersion
          opkWord m.kpkId m.regId m.spkId ∗
        signalMessageRestVerAt A g.msg msgA i ∗
        pathAMsgRemInnerAtExt A g msgA m i := by
  obtain ⟨hver, hreg, hopk, hspk, hbase, hidk, hmsg, hkyb⟩ := pmOfE_fields m i
  unfold preKeyMsgAt p2MsgFieldsAt pathAMsgRemInnerAtExt
  rw [hmsg, hopk, hkyb, hbase, hidk, hreg, hspk, hver,
      signalMessageAt_eq_ver_sep, hdrOpkIdBv?_mkPathAHdr]
  dsimp only [mkPathAHdr]
  rw [bytesToBv8_vecU8 m.baseKey, bytesToBv8_vecU8 m.idPub, bytesToBv8_vecU8 m.kyberCt]
  dsimp only [optKyberAt, boxU8At]
  have hne : (8#8 :: m.kyberCt.toList) ≠ [] := List.cons_ne_nil _ _
  have hlen1569 : BitVec.ofNat 64 (8#8 :: m.kyberCt.toList).length = 1569#64 := by
    simp [m.kyberCt.toList_length]
  have hlenNat : (8#8 :: m.kyberCt.toList).length = 1569 := by
    simp [m.kyberCt.toList_length]
  simp only [hne, ↓reduceIte, hlen1569, hlenNat, BitVec.add_assoc, BitVec.reduceAdd]
  cases hopk_eq : m.opkId with
  | none =>
    dsimp only [optU32At, opkOptTag32]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [memRegion_4_eq_exists_pointsTo32 (msgA + 0x7c#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun opkWord => ?_
    refine Entails.sepExists_right opkWord (Entails.pure_right (by nofun) ?_)
    exact Entails.of_eq (by ac_rfl)
  | some id =>
    dsimp only [optU32At, opkOptTag32]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right id (Entails.pure_right (fun _ h => Option.some.inj h) ?_)
    exact Entails.of_eq (by ac_rfl)

/-- Unpack `preKeyMsgAt` on `pmOfE m i` into `p2MsgFieldsAt` + `signalMessageRestVerAt` +
`pathAMsgRemInnerAt`, quantifying over `opkWord` (pinned to `id` when `m.opkId = some id`). -/
theorem preKeyMsgAt_unpack_pathA (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (m : PreKeyMessageFields) (i : SignalMessage) :
    preKeyMsgAt E2E.HooksE.A0 g msgA (pmOfE m i) ⊢
      ∃∗ opkWord : BitVec 32,
        ⌜∀ id : BitVec 32, m.opkId = some id → opkWord = id⌝ ∗
        p2MsgFieldsAt msgA g.kyberPtr (mkPathAHdr m) i.messageVersion
          opkWord m.kpkId m.regId m.spkId ∗
        signalMessageRestVerAt E2E.HooksE.A0 g.msg msgA i ∗
        pathAMsgRemInnerAt g msgA m i :=
  preKeyMsgAt_unpack_pathA_ext E2E.HooksE.A0 g msgA m i

/-- `A`-polymorphic reassembly of `p2MsgFieldsAt` + `signalMessageRestVerAt` +
`pathAMsgRemInnerAtExt` into `signalMessageAt`, `baseKey`, `idKey`, and `preKeyMsgRemBaseIdKeyAt`. -/
theorem p2MsgFields_reassemble_slices_ext (A : RustAlloc) (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (m : PreKeyMessageFields) (i : SignalMessage) (opkWord : BitVec 32)
    (hopkWord : ∀ id : BitVec 32, m.opkId = some id → opkWord = id) :
    p2MsgFieldsAt msgA g.kyberPtr (mkPathAHdr m) i.messageVersion
      opkWord m.kpkId m.regId m.spkId ∗
    signalMessageRestVerAt A g.msg msgA i ∗
    pathAMsgRemInnerAtExt A g msgA m i ⊢
      signalMessageAt A g.msg msgA (pmOfE m i).message ∗
      ((msgA + 0xa8#64) ↦ₛ (pmOfE m i).baseKey.bytes.toList) ∗
      ((msgA + 0xc8#64) ↦ₛ (pmOfE m i).identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemBaseIdKeyAt A g msgA (pmOfE m i) := by
  obtain ⟨hver, hreg, hopk, hspk, hbase, hidk, hmsg, hkyb⟩ := pmOfE_fields m i
  unfold p2MsgFieldsAt pathAMsgRemInnerAtExt preKeyMsgRemBaseIdKeyAt
  rw [hmsg, hopk, hkyb, hbase, hidk, hreg, hspk, hver,
      signalMessageAt_eq_ver_sep, hdrOpkIdBv?_mkPathAHdr]
  dsimp only [mkPathAHdr]
  rw [bytesToBv8_vecU8 m.baseKey, bytesToBv8_vecU8 m.idPub, bytesToBv8_vecU8 m.kyberCt]
  dsimp only [optKyberAt, boxU8At]
  have hne : (8#8 :: m.kyberCt.toList) ≠ [] := List.cons_ne_nil _ _
  have hlen1569 : BitVec.ofNat 64 (8#8 :: m.kyberCt.toList).length = 1569#64 := by
    simp [m.kyberCt.toList_length]
  have hlenNat : (8#8 :: m.kyberCt.toList).length = 1569 := by
    simp [m.kyberCt.toList_length]
  simp only [hne, ↓reduceIte, hlen1569, hlenNat, BitVec.add_assoc, BitVec.reduceAdd]
  have hoptU32 :
      ((msgA + 0x78#64) ↦₃₂ opkOptTag32 m.opkId) ∗ ((msgA + 0x7c#64) ↦₃₂ opkWord) ⊢
      optU32At (msgA + 0x78#64) m.opkId := by
    cases hopk_eq : m.opkId with
    | none =>
      dsimp only [optU32At, opkOptTag32]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_right (pointsTo32_entails_memRegion _ _)
    | some id =>
      have hw := hopkWord id hopk_eq
      subst hw
      dsimp only [optU32At, opkOptTag32]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.of_eq rfl
  refine Entails.trans (Entails.of_eq (show _ =
    (((msgA + 0x78#64) ↦₃₂ opkOptTag32 m.opkId) ∗ ((msgA + 0x7c#64) ↦₃₂ opkWord)) ∗
    (((msgA + 0x70#64) ↦₈ i.messageVersion) ∗
      signalMessageRestVerAt A g.msg msgA i ∗
      ((msgA + 0xa8#64) ↦ₛ m.baseKey.toList) ∗
      ((msgA + 0xc8#64) ↦ₛ m.idPub.toList) ∗
      boxU8At A (msgA + 0x80#64) g.serPtr (pmOfE m i).serialized ∗
      (((msgA + 0x90#64) ↦₆₄ g.kyberPtr) ∗
        ((msgA + 0x98#64) ↦₆₄ 1569#64) ∗
        ⌜g.kyberPtr ≠ 0 ∧ 1569 < 2 ^ 63⌝ ∗
        (A.live g.kyberPtr 1569 1 ∗ (g.kyberPtr ↦ₛ (8#8 :: m.kyberCt.toList))) ∗
        ((msgA + 0xa0#64) ↦₃₂ m.kpkId) ∗
        memRegion (msgA + 0xa4#64) 4) ∗
      ((msgA + 0xe8#64) ↦₃₂ m.regId) ∗
      ((msgA + 0xec#64) ↦₃₂ m.spkId) ∗
      ((msgA + 0xf0#64) ↦₈ 4#8) ∗
      memRegion (msgA + 0xf1#64) 7) by simp only [boxU8At, BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hoptU32) ?_
  exact Entails.of_eq (by simp only [boxU8At, BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl)

/-- Reassemble `p2MsgFieldsAt` + `signalMessageRestVerAt` + `pathAMsgRemInnerAt` into
`signalMessageAt`, `baseKey`, `idKey`, and `preKeyMsgRemBaseIdKeyAt` (and hence `preKeyMsgAt`). -/
theorem p2MsgFields_reassemble_slices (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (m : PreKeyMessageFields) (i : SignalMessage) (opkWord : BitVec 32)
    (hopkWord : ∀ id : BitVec 32, m.opkId = some id → opkWord = id) :
    p2MsgFieldsAt msgA g.kyberPtr (mkPathAHdr m) i.messageVersion
      opkWord m.kpkId m.regId m.spkId ∗
    signalMessageRestVerAt E2E.HooksE.A0 g.msg msgA i ∗
    pathAMsgRemInnerAt g msgA m i ⊢
      signalMessageAt E2E.HooksE.A0 g.msg msgA (pmOfE m i).message ∗
      ((msgA + 0xa8#64) ↦ₛ (pmOfE m i).baseKey.bytes.toList) ∗
      ((msgA + 0xc8#64) ↦ₛ (pmOfE m i).identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 g msgA (pmOfE m i) :=
  p2MsgFields_reassemble_slices_ext E2E.HooksE.A0 g msgA m i opkWord hopkWord

/-- Bidirectional split of `memRegion (fut + 0x4f8#64) 736` into `p2CoroScratchTailAt fut`
plus the 6-byte gap at `[+0x782.. +0x788)`. -/
theorem coro_scratch_736_split (fut : BitVec 64) :
    memRegion (fut + 0x4f8#64) 736 =
      p2CoroScratchTailAt fut ∗ memRegion (fut + 0x782#64) 6 := by
  unfold p2CoroScratchTailAt
  rw [memRegion_split (fut + 0x4f8#64) 344 392 (by decide),
      memRegion_split (fut + 0x4f8#64 + 344#64) 8 384 (by decide),
      memRegion_split (fut + 0x4f8#64 + 344#64 + 8#64) 298 86 (by decide),
      memRegion_split (fut + 0x4f8#64 + 344#64 + 8#64 + 298#64) 6 80 (by decide),
      memRegion_split (fut + 0x4f8#64 + 344#64 + 8#64 + 298#64 + 6#64) 16 64 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-- Untouched sub-regions of `memRegion (sp + 0x550#64) 1824` outside `stageP2PreAt`. -/
def sp550P2V1RemAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x550#64) 16 ∗ memRegion (sp + 0x580#64) 288 ∗
  memRegion (sp + 0x6c0#64) 288 ∗ memRegion (sp + 0x800#64) 304 ∗
  memRegion (sp + 0x970#64) 32 ∗ memRegion (sp + 0x990#64) 256 ∗
  memRegion (sp + 0xbb0#64) 56 ∗ memRegion (sp + 0xbe8#64) 8 ∗
  memRegion (sp + 0xbf9#64) 119

/-- Bidirectional split of `memRegion (sp + 0x550#64) 1824` into the exact high-stack scratch
atoms of `stageP2PreAt` / `p2ErrFrameAt` / `p2OkPostAt` plus `sp550P2V1RemAt sp`. -/
theorem sp_550_1824_split_p2v1 (sp fp : BitVec 64) (hfp : fp = sp + 0xc70#64) :
    memRegion (sp + 0x550#64) 1824 =
      cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
      cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
      memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
      sp550P2V1RemAt sp := by
  subst hfp
  rw [sp_550_1824_split_genP3 sp]
  unfold spHighGapsAt sp550P2V1RemAt
  rw [memRegion_split (sp + 0x550#64) 16 976 (by decide),
      memRegion_split (sp + 0x550#64 + 16#64) 32 944 (by decide),
      memRegion_split (sp + 0x550#64 + 16#64 + 32#64) 288 656 (by decide),
      memRegion_split (sp + 0x550#64 + 16#64 + 32#64 + 288#64) 32 624 (by decide),
      memRegion_split (sp + 0x550#64 + 16#64 + 32#64 + 288#64 + 32#64) 288 336 (by decide),
      memRegion_split (sp + 0x550#64 + 16#64 + 32#64 + 288#64 + 32#64 + 288#64) 32 304 (by decide),
      memRegion_split (sp + 0x930#64) 64 32 (by decide),
      memRegion_split (sp + 0xa90#64) 288 56 (by decide),
      memRegion_split (sp + 0xbe8#64) 8 128 (by decide),
      memRegion_split (sp + 0xbe8#64 + 8#64) 9 119 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_cells (sp + 0x560#64) 4 (by decide),
      ProofLib.memRegion_cells (sp + 0x6a0#64) 4 (by decide),
      ProofLib.memRegion_cells (sp + 0x7e0#64) 4 (by decide),
      ProofLib.memRegion_cells (sp + 0x930#64) 8 (by decide)]
  ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
