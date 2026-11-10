/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustFrame
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommon

/-!
# Poll Buffer and Seam Frame Bundles for `segTrust`

Packages stack slot framing, poll-output decomposition, and `UntrustedIdentity` frame bundles for
`segTrust`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

/-! ## 1. Poll Buffer & Slot Framing Lemmas -/

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommonRest (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost)
    (draws : Nat) (s0 : State) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter ctl x.cur x.rest draws ∗ encSavedRegs s0.sp s0

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommon_eq (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : WithStoresEncGhost)
    (draws : Nat) (s0 : State) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 =
      protocolAddressAt A x.rem x.remA ∗ logOff img ∗
      stackAt (s0.sp - 0xbe0#64) encSubStack ∗ A.pool ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommonRest A img.base x draws s0 := by
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommonRest; ac_rfl

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.trustPassive (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (m : CiphertextMessage) (draws : Nat) (s0 : State) : SepProp :=
  let sp := s0.sp - 0xbe0#64
  cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m ∗
  cmScratchRest sp ∗
  encSpillsRest ss_vt id_vt sp x ∗
  memRegion (sp + 0x480#64) 32 ∗
  trustPollRest sp ∗
  memRegion x.ret 248 ∗
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommonRest A ctl x draws s0

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.seam_mem_split (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64) :
    cmSlots A sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch sp ∗
      encSpillsAtV ss_vt id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x716 ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 =
    (trustBaseActive id_vt A img sp x k ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x970#64) 24 ∗
      memRegion (sp + 0x9d0#64) 24) ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.trustPassive ss_vt id_vt A img.base x sess taken otr' pqCap' pqPtr' m draws s0 := by
  subst hsp
  dsimp only [trustBaseActive, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.trustPassive]
  rw [cmSlots_eq, cmScratch_eq, encSpillsAt_eq, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommon_eq, trustPoll_split]
  ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.seam_mem_to_tail (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (P970 P9d0 poll H : SepProp)
    (hpoll :
      memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x480#64) 32 ∗
        memRegion (sp + 0x580#64) 48 ∗ P970 ∗ P9d0 ∗ trustPollRest sp ⊢ poll) :
    (trustBaseActive id_vt A img sp x k ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      P970 ∗ P9d0 ∗ H) ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.trustPassive ss_vt id_vt A img.base x sess taken otr' pqCap' pqPtr' m draws s0 ⊢
    ∃∗ g : RecordGhost,
      (dropRecordSlots A sp cmScratch g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) (some m)
          poll ∗ H) ∗
        encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 := by
  subst hsp
  dsimp only [trustBaseActive, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.trustPassive] at hpoll ⊢
  set sp := s0.sp - 0xbe0#64
  have hreord :
      (((sp + 0x40#64) ↦₆₄ (sp + 0x350#64) ∗ (sp + 0xc0#64) ↦₆₄ x.remA ∗
        (sp + 0xe0#64) ↦₆₄ x.idA ∗ (sp + 0xe8#64) ↦₆₄ id_vt ∗
        (sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A x.rem x.remA ∗
        logOff img ∗ stackAt sp encSubStack ∗ A.pool) ∗
      memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x580#64) 48 ∗ P970 ∗ P9d0 ∗ H) ∗
      (cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m ∗ cmScratchRest sp ∗
      encSpillsRest ss_vt id_vt sp x ∗ memRegion (sp + 0x480#64) 32 ∗ trustPollRest sp ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommonRest A img.base x draws s0) =
      (memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x480#64) 32 ∗
        memRegion (sp + 0x580#64) 48 ∗ P970 ∗ P9d0 ∗ trustPollRest sp) ∗
      (((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗
      H ∗ memRegion x.ret 248) := by
    rw [cmScratch_eq, encSpillsAt_eq, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommon_eq]
    change _ = _ ∗ (_ ∗ _ ∗ _ ∗ (protocolAddressAt A x.rem x.remA ∗ logOff img ∗
      stackAt sp encSubStack ∗ A.pool ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommonRest A img.base x draws s0) ∗ _)
    ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left hpoll) ?_
  unfold cmSlotsRest takenSlots
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
  have hslots := cmSlots_to_dropRecordSlots A sp g sess taken otr' pqCap' pqPtr' k m poll
  have hreord2 :
      poll ∗ (sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
      sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
      (sp + 0x280#64) ↦₆₄ (sp + 0x128#64) ∗ (sp + 0x468#64) ↦₈ 0#8 ∗ (sp + 0x469#64) ↦₈ 1#8 ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      apiEncResultAt A (sp + 0x370#64) (Except.ok m) ∗ cmScratch sp ∗
      encSpillsAtV ss_vt id_vt sp x ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗
      H ∗ memRegion x.ret 248 =
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        (sp + 0x280#64) ↦₆₄ (sp + 0x128#64) ∗ (sp + 0x468#64) ↦₈ 0#8 ∗ (sp + 0x469#64) ↦₈ 1#8 ∗
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
        (sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        apiEncResultAt A (sp + 0x370#64) (Except.ok m) ∗ cmScratch sp ∗ poll) ∗
      (H ∗ encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0) := by
    ac_rfl
  rw [hreord2]
  exact sepConj_mono_left hslots

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.call_nopanic_trap {α : Type} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (trTrapProgAt img.base C abs) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State,
      Steps (trTrapProgAt img.base C abs) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next)
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.SegExit.call_trap hcall xc hpc hrun hsp hlr hm
    (fun sf code R' _ h => by rw [hexit] at h; exact not_satisfies_false_sepConj h)
    (fun sf _ _ h => by
      rw [hpanic, sepConj_assoc] at h
      exact (not_satisfies_false_sepConj h).elim)
    (fun sm _ hsteps hpcm hrunm hspm hcsm hpost => ?_)
    (fun sf R' _ h => by rw [hoom] at h; exact not_satisfies_false_sepConj h)
  rw [sepConj_assoc] at hpost
  exact hnext sm hsteps hpcm hrunm hspm (spAligned_of_sp_eq hsp hspm) hcsm hpost

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.call_nopanic {α : Type} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State,
      Steps (tripleRatchetProgAt img.base C ctl abs) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next)
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.SegExit.call hcall xc hpc hrun hsp hlr hm
    (fun sf code R' _ h => by rw [hexit] at h; exact not_satisfies_false_sepConj h)
    (fun sf _ _ h => by
      rw [hpanic, sepConj_assoc] at h
      exact (not_satisfies_false_sepConj h).elim)
    (fun sm _ hsteps hpcm hrunm hspm hcsm hpost => ?_)
    (fun sf R' _ h => by rw [hoom] at h; exact not_satisfies_false_sepConj h)
  rw [sepConj_assoc] at hpost
  exact hnext sm hsteps hpcm hrunm hspm (spAligned_of_sp_eq hsp hspm) hcsm hpost

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.call_alloc_trap {α : Type} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (trTrapProgAt img.base C abs) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpref0 : s0.trace <+: s.trace)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State,
      Steps (trTrapProgAt img.base C abs) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next)
    (hR : R ⊢ anyHeap ∗ R0 := by exact sepConj_mono_left (entails_anyHeap _))
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.SegExit.call_trap hcall xc hpc hrun hsp hlr hm
    (fun sf code R' _ h => by rw [hexit] at h; exact not_satisfies_false_sepConj h)
    (fun sf _ _ h => by
      rw [hpanic] at h
      exact Satisfies.mono (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.alloc_onPanic_entails hpref0 hR) h)
    (fun sm _ hsteps hpcm hrunm hspm hcsm hpost => ?_)
    (fun sf R' _ h => by rw [hoom] at h; exact not_satisfies_false_sepConj h)
  rw [sepConj_assoc] at hpost
  exact hnext sm hsteps hpcm hrunm hspm (spAligned_of_sp_eq hsp hspm) hcsm hpost

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.call_alloc {α : Type} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpref0 : s0.trace <+: s.trace)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State,
      Steps (tripleRatchetProgAt img.base C ctl abs) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next)
    (hR : R ⊢ anyHeap ∗ R0 := by exact sepConj_mono_left (entails_anyHeap _))
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.SegExit.call hcall xc hpc hrun hsp hlr hm
    (fun sf code R' _ h => by rw [hexit] at h; exact not_satisfies_false_sepConj h)
    (fun sf _ _ h => by
      rw [hpanic] at h
      exact Satisfies.mono (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.alloc_onPanic_entails hpref0 hR) h)
    (fun sm _ hsteps hpcm hrunm hspm hcsm hpost => ?_)
    (fun sf R' _ h => by rw [hoom] at h; exact not_satisfies_false_sepConj h)
  rw [sepConj_assoc] at hpost
  exact hnext sm hsteps hpcm hrunm hspm (spAligned_of_sp_eq hsp hspm) hcsm hpost

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
