/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalFetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalFrame
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import ProofLib.RegChain

/-!
# `segSignal` Pre-Key Items Getter Call (`+0x344..+0x348`)

Defines `SegSignalAckStateV` (`+0x348`) and proves `segSignal_to_ack`, stepping from `KeyStateV`
(`+0x344`) across `unacknowledged_pre_key_message_items` (`0x1245c`) when `sess.pendingPreKey = none`
(tag `2`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Seam state at `+0x348` after `unacknowledged_pre_key_message_items` returns `None`
(tag `2`). -/
def SegSignalAckStateV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (R0 : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  r.currentSession = some sess ∧ kit.ScopeAt Scope st0 x.rem.val r ∧
  execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
  taken.remoteIdentity = some k ∧ sess.pendingPreKey = none ∧
  s.pc = encEntry img + 0x348#64 ∧ encMidMeta img x s0 s ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
  s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x23 = sp + 0x58#64 ∧
  s.readReg64 .x25 = sp + 0x580#64 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
  s.readReg64 .x27 = sp + 0xc0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64 ∧
  x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
  x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
  (s.mem ⊨
    (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
    curScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    (memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8) ∗
    memRegion x.ret 248 ∗ encCommon A ctl img x 0 s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0))

abbrev SegSignalAckState (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc) (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (img : Obj.Image)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (R0 : SepProp) (s0 s : State) : Prop :=
  SegSignalAckStateV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope ctl encRecord x r sess otr taken
    pqCap pqPtr k R0 s0 s

private def segSignalUnackRestFrame {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (_img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (sp : BitVec 64) (s0 : State) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5d8#64) 0x5a8 ∗
  memRegion x.ret 248 ∗
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest 0 ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - unackItemsStack) ∗
  encSavedRegs s0.sp s0 ∗ A.pool

private theorem segSignal_keyState_mem_unpack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (sp : BitVec 64) (R : SepProp) (s0 : State)
    {m : Memory} (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hm : m ⊨ (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x 0 s0 ∗ R) :
    ∃ g G,
      m ⊨ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
          memRegion (sp + 0x580#64) 88 ∗
          logOff img ∗
          stackAt sp unackItemsStack ∗
          segSignalUnackRestFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g otr pqCap pqPtr k sp s0) ∗
        R) := by
  unfold takenSlots encCommon at hm
  rw [hsp0] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc] at hm
  obtain ⟨g, hm⟩ := hm
  have hm_rec := Satisfies.mono (sepConj_mono_left (segSignal_rec_unpack A sp g sess taken)) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc] at hm_rec
  obtain ⟨G, hm_rec⟩ := hm_rec
  have h46a : memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 88 ∗
      memRegion (sp + 0x5d8#64) 0x5a8 := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide),
        mr_cut_add sp (0x46a + 0x116) 88 0x5a8 (by decide)]
  rw [h46a, stackAt_sub sp encSubStack unackItemsStack] at hm_rec
  refine ⟨g, G, ?_⟩
  unfold segSignalUnackRestFrame
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm_rec

private theorem segSignal_unack_pre_frame {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R Pm : SepProp) (s0 s1 : State)
    (hsp1 : s1.sp = sp)
    (hx0 : s1.readReg64 .x0 = sp + 0x128#64)
    (hx8 : s1.readReg64 .x8 = sp + 0x580#64)
    (hPm : Pm ⊢ (sp + 0x280#64) ↦₆₄ (sp + 0x128#64))
    (hm : s1.mem ⊨ Pm ∗
      ((sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
        memRegion (sp + 0x580#64) 88 ∗
        logOff img ∗
        stackAt sp unackItemsStack ∗
        segSignalUnackRestFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g otr pqCap pqPtr k sp s0) ∗
      R)) :
    s1.mem ⊨ (unackItemsSpec A img).pre ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 ∗
      ((((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        segSignalUnackRestFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g otr pqCap pqPtr k sp s0) ∗
      R) := by
  have hm' := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold unackItemsSpec
  dsimp only
  rw [hsp1]
  have hpure : (⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64⌝ : SepProp) ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
          memRegion (sp + 0x580#64) 88 ∗
          logOff img ∗
          stackAt sp unackItemsStack ∗
          segSignalUnackRestFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g otr pqCap pqPtr k sp s0) ∗
        R)) =
      (((⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64⌝ ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
        memRegion (sp + 0x580#64) 88 ∗
        logOff img ∗
        stackAt sp unackItemsStack) ∗
        ((((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          segSignalUnackRestFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g otr pqCap pqPtr k sp s0) ∗
        R))) := by
    ac_rfl
  rw [← hpure, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx8⟩, hm'⟩

private theorem segSignal_unack_panic_absurd (A : RustAlloc) (img : Obj.Image)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (sp : BitVec 64) (F R : SepProp) (s1 sf : State)
    (hpk : sess.pendingPreKey = none)
    (hpost : sf.mem ⊨ ((unackItemsSpec A img).onPanic
      ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 sf ∗ F) ∗ R) :
    False := by
  unfold unackItemsSpec at hpost
  dsimp only at hpost
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
  rcases hpost.1.1 with ⟨items, hsome, _⟩
  rw [hpk] at hsome
  cases hsome

private theorem segSignal_unack_post_pack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R : SepProp) (s0 s1 s2 : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hsp1 : s1.sp = sp)
    (hpk : sess.pendingPreKey = none)
    (hpost : s2.mem ⊨ ((unackItemsSpec A img).post
      ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 s2 ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        segSignalUnackRestFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g otr pqCap pqPtr k sp s0)) ∗
      R) :
    s2.trace = s1.trace ∧
    (s2.mem ⊨
      (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
        memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8) ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x 0 s0 ∗ R) := by
  have hout : unackOutAt (sp + 0x580#64) G.kyber
      ({ sess with state := taken }).pendingKyberPreKey
      ({ sess with state := taken }).pendingPreKey =
      ((sp + 0x580#64) ↦₃₂ 2#32) ∗ memRegion (sp + 0x584#64) 84 := by
    change unackOutAt (sp + 0x580#64) G.kyber sess.pendingKyberPreKey sess.pendingPreKey = _
    rw [hpk]
    unfold unackOutAt
    have h584 : (sp + 0x580#64) + 4#64 = sp + 0x584#64 := by bv_omega
    rw [h584]
  unfold unackItemsSpec at hpost
  dsimp only [Spec.post] at hpost
  rw [hsp1, hout] at hpost
  simp only [sepConj_assoc] at hpost
  rw [satisfies_pure_sepConj] at hpost
  rcases hpost with ⟨htr, hmem⟩
  refine ⟨htr, ?_⟩
  unfold segSignalUnackRestFrame at hmem
  have hrec :
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ⊢
      ∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken) :=
    Entails.trans (segSignal_rec_pack A sp g.prevCap g.prevPtr G sess taken)
      (Entails.sepExists_right ⟨g.prevCap, g.prevPtr, some G⟩ (Entails.refl _))
  have hmem_rearr : s2.mem ⊨
      (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken }) ∗
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - unackItemsStack) ∗
        stackAt sp unackItemsStack) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8 ∗
      memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest 0 ∗ logOff img ∗
      encSavedRegs s0.sp s0 ∗ A.pool ∗ R :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack unackItemsStack] at hmem_rearr
  have hmem_fold := Satisfies.mono (sepConj_mono_left hrec) hmem_rearr
  unfold takenSlots encCommon
  rw [hsp0]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hmem_fold

/-- Steps from `KeyStateV` (`+0x344`) across `unacknowledged_pre_key_message_items` under
`sess.pendingPreKey = none` to `SegSignalAckStateV` (`+0x348`). -/
theorem segSignal_to_ack {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State) (hpk : sess.pendingPreKey = none)
    (hs : KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => SegSignalAckStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr
        k R0 s0 s') := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hs with ⟨hcur, hsc, hfrom, hrem, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, ⟨hx0, hx8, hx20, _hx22, hx23, hx25, hx26, hx27, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hentry : encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt env.loads encryptWithStoresName
  have hs_pc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x344#64 := by
    simpa only [keyPC, hentry] using hs_pc
  obtain ⟨g, G, hm_unp⟩ :=
    segSignal_keyState_mem_unpack A ctl img x sess otr taken pqCap pqPtr k sp R s0 hsp0 hm
  refine SegFrom.SegExit.of_sepWP hm_unp (segSignal_step_bl hs_pc' hrun hsp hal) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x23, hs1_x25, hs1_x26, hs1_x27,
      hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have ⟨hfl1, hsym1⟩ := SegFrom.callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := SegFrom.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hs1_pc' : s1.pc = img.base + 0x1245c#64 := by
    rw [hs1_pc, unack_addr_eq]
  have hm1_pre := segSignal_unack_pre_frame A ctl img x g G sess otr taken pqCap pqPtr k sp R Pm1 s0 s1
    hs1_sp (hs1_x0.trans hx0) (hs1_x8.trans hx8) hPm1 hm1
  refine SegFrom.SegExit.call env.callees.unack
    ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩
    hs1_pc' hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (unackItemsSpec A img).onExit
        ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost =>
      (segSignal_unack_panic_absurd A img G sess taken sp _ R s1 sf hpk hpost).elim)
    ?_
  intro s2 hL1 hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have ⟨hfl2, hsym2⟩ := SegFrom.callInv_steps hfl1 hsym1 hsteps12 hL1
  have hs2_al : s2.spAligned = true := SegFrom.spAligned_of_sp_eq hs1_al hs2_sp
  have ⟨hs2_tr, hm2⟩ := segSignal_unack_post_pack A ctl img x g G sess otr taken pqCap pqPtr k sp R
    s0 s1 s2 hsp0 hs1_sp hpk hpost2
  refine SegFrom.SegExit.next ⟨hcur, hsc, hfrom, hrem, hpk, ?_,
    ⟨hs2_run, by reg_chain, hal0, hs2_al, by reg_chain, by reg_chain, hfl2, hsym2,
      (hcs12.2.2.2.2.2.2.2.2.2.2.2).trans (hs1_vregs.trans hvregs)⟩, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    hpt, hrest, hloc, hnow, hstk, hm2⟩
  rw [hs2_pc, hentry]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

