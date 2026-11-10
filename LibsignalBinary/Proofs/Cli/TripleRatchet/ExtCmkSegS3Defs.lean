/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSeams
public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `SP2Ext` Segment S3 Checkpoint States and Sub-Segment Contracts

Defines the `cmkLoopStackX = 20000` intermediate checkpoint states (`InsertKeyStateX`,
`EvictOldestKeyStateX`, `AdvanceChainKeyStateX`), sub-segment contracts (`DeriveSeedSpecX`,
`InsertKeySpecX`, `EvictOldestKeySpecX`, `AdvanceChainKeySpecX`), and single-iteration composition
(`storeLoop_iter_of_parts_x`) for the key-store loop of `consume_message_key`.
-/

@[expose] public section

namespace Proofs.libsignal.Stage1X.CmkX

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.Ratchet CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.SessionModel
open CryptoVerification.LibsignalSession.StoreLoop
open Proofs.libsignal.Hooks2 (SP2Ext SP2Ext_fnAddr sub_ok_at_caller)
open Proofs.libsignal.Stage1X

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_SegS3Defs : True := trivial

/-! ## Entry and Checkpoint PC Equations -/

theorem cmkEntry_eq_fnAddr_x {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    cmkEntry img = (SP2Ext img.base ext).fnAddr cmkName := by
  rw [cmkEntry_eq h, Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")]

theorem cmkLoopPC_eq_fnAddr_x {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    cmkLoopPC img = (SP2Ext img.base ext).fnAddr cmkName + 820#64 := by
  simp only [cmkLoopPC, cmkEntry_eq_fnAddr_x h ext]

theorem cmkEpiloguePC_eq_fnAddr_x {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    cmkEpiloguePC img = (SP2Ext img.base ext).fnAddr cmkName + 1244#64 := by
  simp only [cmkEpiloguePC, cmkEntry_eq_fnAddr_x h ext]

theorem cmkInsertKeyPC_eq_fnAddr_x {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    cmkInsertKeyPC img = (SP2Ext img.base ext).fnAddr cmkName + 916#64 := by
  simp only [cmkInsertKeyPC, cmkEntry_eq_fnAddr_x h ext]

theorem cmkEvictOldestKeyPC_eq_fnAddr_x {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    cmkEvictOldestKeyPC img = (SP2Ext img.base ext).fnAddr cmkName + 1020#64 := by
  simp only [cmkEvictOldestKeyPC, cmkEntry_eq_fnAddr_x h ext]

theorem cmkAdvanceChainKeyPC_eq_fnAddr_x {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    cmkAdvanceChainKeyPC img = (SP2Ext img.base ext).fnAddr cmkName + 1140#64 := by
  simp only [cmkAdvanceChainKeyPC, cmkEntry_eq_fnAddr_x h ext]

/-! ## Callee Contract Relocation -/

theorem hmac_ok_at_cmk_x {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} (hHmac : HmacOkX img F ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr cmkName + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      ((hmacSpecX F).inImage img) := by
  have h := hHmac
  unfold HmacOkX at h
  rw [SP2Ext_fnAddr] at h
  exact sub_ok_at_caller (k := num% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm]) h

theorem find_index_ok_at_cmk_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hFind : FindIndexOkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr cmkName + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      ((findIndexSpecX img A).inImage img) := by
  have h := hFind
  unfold FindIndexOkX at h
  rw [SP2Ext_fnAddr] at h
  exact sub_ok_at_caller (k := num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm]) h

theorem grow_one_ok_at_cmk_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hGrow : GrowOneChainOkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr cmkName + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      ((growOne104SpecX A).inImage img) := by
  have h := hGrow
  unfold GrowOneChainOkX at h
  rw [SP2Ext_fnAddr] at h
  exact sub_ok_at_caller (k := num% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm]) h

/-! ## Intermediate Checkpoint States -/

/-- Checkpoint state at `+0x394` (`cmkInsertKeyPC`) with `cmkLoopStackX = 20000`. -/
def InsertKeyStateX (F : ShaCompress) (A : RustAlloc) (img : Obj.Image)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (seedPtr : BitVec 64)
    (R : SepProp) (s0 s : State) : Prop :=
  s.pc = cmkInsertKeyPC img ∧
  cmkMidMeta img s0 s ∧
  InsertKeyRegs x Gc ckc ci seedPtr s0 s ∧
  seedPtr ≠ 0#64 ∧
  (s.mem ⊨
    (cmkLoopHeapX A img x Gc stc ckc s0 ∗
     vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ∗ R)

/-- Heap layout at `cmkEvictOldestKeyPC img` (`+0x3fc`) at `cmkLoopStackX = 20000`. -/
def evictOldestKeyHeapX (F : ShaCompress) (A : RustAlloc) (img : Obj.Image)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State) : SepProp :=
  let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  let gks1 := (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  ⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
  vecGhostAt A cg.srk chainPtr ∗
  vecGhostAt A cg.priv (chainPtr + 24#64) ∗
  vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 2001#64 ∗
  vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1 gks1 ∗
  optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
  ratchetContextAt A x.self Gc stc ci ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 20000 ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

/-- Checkpoint state at `+0x3fc` (`cmkEvictOldestKeyPC`) with `cmkLoopStackX = 20000`. -/
def EvictOldestKeyStateX (F : ShaCompress) (A : RustAlloc) (img : Obj.Image)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64)
    (R : SepProp) (s0 s : State) : Prop :=
  s.pc = cmkEvictOldestKeyPC img ∧
  cmkMidMeta img s0 s ∧
  EvictOldestKeyRegs x Gc ckc ci mkPtr1 s ∧
  (∃ hci : ci < Gc.chains.length, cg = Gc.chains[ci]) ∧
  PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
  chc.messageKeys.length = 2000 ∧
  cg.keys.length = 2000 ∧
  2001 ≤ mkCap1.toNat ∧
  mkCap1.toNat * 104 < 2 ^ 63 ∧
  mkPtr1 ≠ 0#64 ∧
  (s.mem ⊨ evictOldestKeyHeapX F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 ∗ R)

/-- Checkpoint state at `+0x474` (`cmkAdvanceChainKeyPC`) with `cmkLoopStackX = 20000`. -/
def AdvanceChainKeyStateX (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (R : SepProp) (s0 s : State) : Prop :=
  s.pc = cmkAdvanceChainKeyPC img ∧
  cmkMidMeta img s0 s ∧
  AdvanceChainKeyRegs x s0 s ∧
  (s.mem ⊨ cmkLoopHeapX A img x G' st' ckc s0 ∗ R)

/-! ## Sub-Segment Contracts and Single-Iteration Composition -/

/-- Sub-segment A (`+0x334 → +0x394` or OOM panic): derives the message-key seed via HMAC. -/
def DeriveSeedSpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Proofs.libsignal.Stage1X.AllocContractsX img A ext → Obj.Loads libsignalSessionImage img →
    FindIndexOkX img A ext → HmacOkX img F ext →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
      (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
      (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopStateX A img x Gc stc ckc R (cmkLoopPC img) s0 s →
      (SP2Ext img.base ext).CodeLoaded s.mem →
      ∃ sA, Steps (SP2Ext img.base ext) s sA ∧
        ((∃ seedPtr, InsertKeyStateX F A img x Gc stc ckc ci seedPtr R s0 sA) ∨
         (sA.status = .Panicked ∧ (sA.mem ⊨ (cmkSpecX F A img).onPanic x s0 sA ∗ R)))

/-- Sub-segment B (`+0x394 → +0x474 / +0x3fc` or OOM panic): inserts the new `MessageKey` into
`message_keys` (growing if full). -/
def InsertKeySpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Proofs.libsignal.Stage1X.AllocContractsX img A ext → Obj.Loads libsignalSessionImage img → GrowOneChainOkX img A ext →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
      (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
      (seedPtr : BitVec 64) (R : SepProp) (s0 sA : State),
      stc.receiverChains[ci]? = some chc →
      InsertKeyStateX F A img x Gc stc ckc ci seedPtr R s0 sA →
      (SP2Ext img.base ext).CodeLoaded sA.mem →
      ∃ sB, Steps (SP2Ext img.base ext) sA sB ∧
        ((∃ G', Gc.AgreeExcept G' (some ci) ∧
            AdvanceChainKeyStateX A img x G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB) ∨
         (∃ cg mkCap1 mkPtr1,
            EvictOldestKeyStateX F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 sB) ∨
         (sB.status = .Panicked ∧ (sB.mem ⊨ (cmkSpecX F A img).onPanic x s0 sB ∗ R)))

/-- Sub-segment C (`+0x3fc → +0x474`): evicts the oldest `MessageKey` when capacity exceeds the limit. -/
def EvictOldestKeySpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Proofs.libsignal.Stage1X.AllocContractsX img A ext → Obj.Loads libsignalSessionImage img →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
      (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
      (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64)
      (R : SepProp) (s0 sB : State),
      stc.receiverChains[ci]? = some chc →
      EvictOldestKeyStateX F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 sB →
      (SP2Ext img.base ext).CodeLoaded sB.mem →
      ∃ sC, Steps (SP2Ext img.base ext) sB sC ∧
        ∃ G', Gc.AgreeExcept G' (some ci) ∧
          AdvanceChainKeyStateX A img x G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sC

/-- Sub-segment D (`+0x474 → nextPC`): advances `ChainKey` via HMAC and updates the loop counter. -/
def AdvanceChainKeySpecX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img → HmacOkX img F ext →
    ∀ (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (st' : RatchetState)
      (ckc : CryptoGames.LibsignalSession.ChainKey) (R : SepProp) (s0 sD : State),
      ckc.index < x.counter →
      AdvanceChainKeyStateX A img x G' st' ckc R s0 sD →
      (SP2Ext img.base ext).CodeLoaded sD.mem →
      let ck' := chainStepN F 1 ckc
      let nextPC := if ck'.index < x.counter then cmkLoopPC img else cmkEpiloguePC img
      ∃ s', Steps (SP2Ext img.base ext) sD s' ∧
        CmkLoopStateX A img x G' st' ck' R nextPC s0 s'

theorem storeLoop_iter_of_parts_x {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (hA_part : DeriveSeedSpecX F A ext img)
    (hB_part : InsertKeySpecX F A ext img)
    (hC_part : EvictOldestKeySpecX F A ext img)
    (hD_part : AdvanceChainKeySpecX F A ext img) :
    CmkS3IterSpecX F A ext img := by
  intro hA himg hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
  obtain ⟨sA, hstepsA, ⟨seedPtr, hsA⟩ | hpanA⟩ :=
    hA_part hA himg hfind hhmac x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
  · have hLA := hstepsA.codeLoaded hL
    obtain ⟨sB, hstepsB, ⟨G', hG', hsD⟩ | ⟨cg, mkCap1, mkPtr1, hsC⟩ | hpanB⟩ :=
      hB_part hA himg hgrow x Gc stc ckc ci chc seedPtr R s0 sA hchc hsA hLA
    · have hLB := hstepsB.codeLoaded hLA
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part himg hhmac x G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB hlt hsD hLB
      exact ⟨s', (hstepsA.trans hstepsB).trans hstepsD, Or.inl ⟨G', hG', hs'⟩⟩
    · have hLB := hstepsB.codeLoaded hLA
      obtain ⟨sC, hstepsC, G', hG', hsD⟩ :=
        hC_part hA himg x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 sB hchc hsC hLB
      have hLC := hstepsC.codeLoaded hLB
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part himg hhmac x G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sC hlt hsD hLC
      exact ⟨s', ((hstepsA.trans hstepsB).trans hstepsC).trans hstepsD, Or.inl ⟨G', hG', hs'⟩⟩
    · exact ⟨sB, hstepsA.trans hstepsB, Or.inr hpanB⟩
  · exact ⟨sA, hstepsA, Or.inr hpanA⟩

end Proofs.libsignal.Stage1X.CmkX
