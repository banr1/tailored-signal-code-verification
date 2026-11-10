/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingKyberPreKeyX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingKyberPreKeyXPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXB
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXBPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PqRatchetStateEpilogueX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RegistrationIdsBaseKeyX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RegistrationIdsBaseKeyXPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RemoteIdentityRootKeyCounterX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RemoteIdentityRootKeyCounterXPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SenderReceiverChainsX

@[expose] public section

set_option autoImplicit false

/-!
# `<SessionStructure as prost::Message>::encode_raw::<Vec<u8>>` (`0x4d38`)

Assembles all per-tag segment proofs to establish the top-level subroutine contract of
`<SessionStructure as prost::Message>::encode_raw::<Vec<u8>>` (`0x4d38`, Block `14`) at
`encodeRawStackX` on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux
open Proofs.libsignal.Hooks2

theorem L1_EncodeRawX : True := trivial

private def sessionRawOpen (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (m : Session (List (BitVec 8))) : SepProp :=
  vecU8At A ss G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
  vecU8At A (ss + 24#64) G.remoteIk.cap G.remoteIk.ptr G.remoteIk.bytes ∗
  vecU8At A (ss + 48#64) G.root.cap G.root.ptr (HMAC.keyToBytes32 m.state.rootKey) ∗
  vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
    (G.chains.zip m.state.receiverChains) ∗
  vecU8At A (ss + 96#64) G.alice.cap G.alice.ptr m.aliceBaseKey ∗
  vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr m.state.pqRatchetState ∗
  optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
  optTailVecAt A 48 (ss + 248#64) G.pending ∗
  optTailVecAt A 32 (ss + 296#64) G.kyber ∗
  ((ss + 328#64) ↦₃₂ m.state.sessionVersion) ∗
  ((ss + 332#64) ↦₃₂ m.state.previousCounter) ∗
  ((ss + 336#64) ↦₃₂ m.remoteRegistrationId) ∗
  ((ss + 340#64) ↦₃₂ m.localRegistrationId)

private theorem sessionStateAt_body_eq_open (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (m : Session (List (BitVec 8)))
    (halice : G.alice.bytes = m.aliceBaseKey)
    (hreg_len : G.regIds.length = 8)
    (hrem_id : G.regIds.take 4 = leBytes 4 m.remoteRegistrationId.toNat)
    (hloc_id : (G.regIds.drop 4).take 4 = leBytes 4 m.localRegistrationId.toNat) :
    (vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
      vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (HMAC.keyToBytes32 m.state.rootKey) ∗
      vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
        (G.chains.zip m.state.receiverChains) ∗
      vecGhostAt A G.alice (ss + 0x60#64) ∗
      vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr m.state.pqRatchetState ∗
      optSenderChainAt A (ss + 0x90#64) G.sender m.state.senderChain ∗
      optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
      optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
      ((ss + 0x148#64) ↦₃₂ m.state.sessionVersion) ∗
      ((ss + 0x14c#64) ↦₃₂ m.state.previousCounter) ∗
      ((ss + 0x150#64) ↦ₛ G.regIds)) =
    sessionRawOpen A ss G m := by
  dsimp only [vecGhostAt, sessionRawOpen]
  rw [halice, pointsToBytes_regIds_eq ss hreg_len hrem_id hloc_id]

private theorem sepWPp_open_sessionAtX {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {ss : BitVec 64} {G : SessionGhost} {m : Session (List (BitVec 8))}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : PendingRel G.pending m.pendingPreKey →
      KyberRel G.kyber m.pendingKyberPreKey →
      (sessionStateReprAt A ss G m = sessionRawOpen A ss G m) →
      SepWPp prog ret s (sessionRawOpen A ss G m ∗ F) Q Qp) :
    SepWPp prog ret s (sessionStateReprAt A ss G m ∗ F) Q Qp := by
  dsimp only [sessionStateReprAt, sessionStateAt]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hp1 => ?_
  refine SepWPp.pure_elim fun hp2 => ?_
  have ⟨hpending, hkyber, halice, hrem_id, hloc_id⟩ := hp1
  have hreg_len : G.regIds.length = 8 := hp2.2.2.2.2.1
  have hbody := sessionStateAt_body_eq_open A ss G m halice hreg_len hrem_id hloc_id
  have heq : sessionStateReprAt A ss G m = sessionRawOpen A ss G m := by
    dsimp only [sessionStateReprAt, sessionStateAt]
    rw [eq_true hp1, eq_true hp2, pure_true, emp_sepConj, emp_sepConj, hbody]
  refine SepWPp.weaken_pre ?_ (h hpending hkyber heq)
  rw [← hbody]
  exact (by sep_frame)

private theorem sepWPpIn_open_sessionAt {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {ss : BitVec 64} {G : SessionGhost} {m : Session (List (BitVec 8))}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : PendingRel G.pending m.pendingPreKey →
      KyberRel G.kyber m.pendingKyberPreKey →
      (sessionStateReprAt A ss G m = sessionRawOpen A ss G m) →
      SepWPpIn img prog ret s (sessionRawOpen A ss G m ∗ F) Q Qp) :
    SepWPpIn img prog ret s (sessionStateReprAt A ss G m ∗ F) Q Qp := by
  intro hF hsym
  apply sepWPp_open_sessionAtX
  intro hp1 hp2 heq
  exact h hp1 hp2 heq hF hsym

private theorem length_le_bytesField_length_er (t : Nat) (fBs : List (BitVec 8)) :
    fBs.length ≤ (bytesField t fBs).length := by
  by_cases h : fBs = []
  · subst h; simp [bytesField]
  · simp [bytesField, lenField, h]; omega

private theorem pending_vec_length_lt_er
    (G_pending : Option TailVecGhost) (s_pending : Option PendingPreKey)
    (hrel : PendingRel G_pending s_pending)
    (hfit : (encPendingFieldMem G_pending s_pending).length < 2 ^ 32) :
    ∀ g, G_pending = some g → g.vec.bytes.length < 2 ^ 32 := by
  intro g hg
  subst hg
  cases s_pending with
  | none => exact False.elim hrel
  | some p =>
    have h1 := length_le_bytesField_length_er 2 g.vec.bytes
    simp only [encPendingFieldMem, lenField, encPendingMem, List.length_append] at hfit
    omega

private theorem kyber_ct_length_lt_er
    (s_kyber : Option PendingKyberPreKey)
    (hfit : (msgField 14 (s_kyber.map encPendingKyber)).length < 2 ^ 32) :
    ∀ k, s_kyber = some k → k.ciphertext.length < 2 ^ 32 := by
  intro k hk
  subst hk
  have h1 := length_le_bytesField_length_er 2 k.ciphertext
  simp only [Option.map_some, msgField, lenField, encPendingKyber, List.length_append] at hfit
  omega

private theorem vecU8At_entails_exists_er (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢
      ∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64, vecU8At A v cap' ptr' bs :=
  Entails.trans
    (Entails.sepExists_intro (P := fun ptr' => vecU8At A v cap ptr' bs) ptr)
    (Entails.sepExists_intro (P := fun cap' => ∃∗ ptr' : BitVec 64, vecU8At A v cap' ptr' bs) cap)

private theorem sepWPp_to_panicAllocPostX {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P R : SepProp} {Q : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (PanicAllocPost s0)) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hok | ⟨hpan_s, P_f, hmf, hp⟩ | hoom⟩ := h R' hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan_s, P_f, hmf, fun hmR => hp R hmR⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

private theorem sepWPpIn_to_panicAllocPost {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P R : SepProp} {Q : State → SepProp → Prop}
    (h : SepWPpIn img prog ret s P Q (PanicAllocPost s0)) :
    SepWPpIn img prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  intro hF hsym
  exact sepWPp_to_panicAllocPostX (h hF hsym)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 400000 in
theorem encodeRaw_ok_ext (A : RustAlloc) (ext : String → Option (State → State)) {img : Obj.Image}
    (hC : SerContractsX img A ext) (hEV : EncodeVarintOkX img A ext) (hDR : DoReserveOkX img A ext)
    (hEC : EncodeChainOkX img A ext) :
    EncodeRawOkX img A ext := by
  apply subroutine_ok_inImage_of_sepWPpIn
  intro ⟨ss, G, m, v, cap0, ptr0, bs0⟩ R s0 hpc0 hrun0 hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(encodeRawSpecX A).pre ⟨ss, G, m, v, cap0, ptr0, bs0⟩ s0, R, hpre, ?_⟩
  dsimp only [encodeRawSpecX]
  apply sepWPpIn_to_panicAllocPost
  simp only [sepConj_assoc]
  refine SepWPpIn.pure_elim fun ⟨hx0, hx1, hfit⟩ => ?_
  refine sepWPpIn_open_sessionAt fun hpending hkyber hSessEq => ?_
  have hlik_le := length_le_bytesField_length_er 2 G.localIk.bytes
  have hrik_le := length_le_bytesField_length_er 3 G.remoteIk.bytes
  have hroot_le := length_le_bytesField_length_er 4 (HMAC.keyToBytes32 m.state.rootKey)
  have halice_le := length_le_bytesField_length_er 13 m.aliceBaseKey
  have hpq_le := length_le_bytesField_length_er 15 m.state.pqRatchetState
  have hfit_expand :
      bs0.length +
      ((uint32Field 1 m.state.sessionVersion).length +
       (bytesField 2 G.localIk.bytes).length +
       (bytesField 3 G.remoteIk.bytes).length +
       (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
       (uint32Field 5 m.state.previousCounter).length +
       (encSenderFieldMem G.sender m.state.senderChain).length +
       (((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten).length +
       (encPendingFieldMem G.pending m.pendingPreKey).length +
       (uint32Field 10 m.remoteRegistrationId).length +
       (uint32Field 11 m.localRegistrationId).length +
       (bytesField 13 m.aliceBaseKey).length +
       (msgField 14 (m.pendingKyberPreKey.map encPendingKyber)).length +
       (bytesField 15 m.state.pqRatchetState).length) < 2 ^ 32 := by
    simpa only [encSessionMem, List.length_append, Nat.add_assoc] using hfit
  have hpend_bound := pending_vec_length_lt_er G.pending m.pendingPreKey hpending (by omega)
  have hkyber_bound := kyber_ct_length_lt_er m.pendingKyberPreKey (by omega)
  unfold sessionRawOpen
  refine step_encraw_prologue_x ext ss v s0.sp hpc0 hrun0 rfl halign rfl hx0 hx1
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl (by sep_frame) ?_
  intro s1 v56 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx20_1 hcs1
  refine step_encraw_tag1_x hDR hEV ss v s0.sp cap0 ptr0 m.state.sessionVersion bs0
    (by omega) hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx20_1 hcs1 (by sep_frame) ?_
  intro s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
  refine step_encraw_tag2_x hC hDR hEV ss v s0.sp G.localIk.cap G.localIk.ptr cap1 ptr1
    (bs0 ++ uint32Field 1 m.state.sessionVersion) G.localIk.bytes
    (by simp only [List.length_append]; omega)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2 (by sep_frame) ?_
  intro s3 cap2 ptr2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
  refine step_encraw_tag3_x hC hDR hEV ss v s0.sp G.remoteIk.cap G.remoteIk.ptr cap2 ptr2
    ((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) G.remoteIk.bytes
    (by simp only [List.length_append]; omega)
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3 (by sep_frame) ?_
  intro s4 cap3 ptr3 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4
  refine step_encraw_tag4_x hC hDR hEV ss v s0.sp G.root.cap G.root.ptr cap3 ptr3
    (((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes)
    (HMAC.keyToBytes32 m.state.rootKey)
    (by simp only [List.length_append]; omega)
    hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hcs4 (by sep_frame) ?_
  intro s5 cap4 ptr4 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hcs5
  refine step_encraw_tag5_x hDR hEV ss v s0.sp cap4 ptr4 m.state.previousCounter
    ((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey))
    (by simp only [List.length_append]; omega)
    hpc5 hrun5 hsp5 halign htr5 hx19_5 hx20_5 hcs5 (by sep_frame) ?_
  intro s6 cap5 ptr5 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6
  refine step_encraw_tag6_x hEC ss v s0.sp cap5 ptr5 G.sender m.state.senderChain
    (((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter)
    (by simp only [List.length_append]; omega)
    hpc6 hrun6 hsp6 halign htr6 hx19_6 hx20_6 hcs6 (by sep_frame) ?_
  intro s7 cap6 ptr6 hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hcs7
  refine step_encraw_tag7_x hEC ss v s0.sp G.chainsCap G.chainsPtr cap6 ptr6
    (G.chains.zip m.state.receiverChains)
    ((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain)
    (by simp only [List.length_append]; omega)
    hpc7 hrun7 hsp7 halign htr7 hx19_7 hx20_7 hcs7 (by sep_frame) ?_
  intro s8 cap7 ptr7 hpc8 hrun8 hsp8 htr8 hx19_8 hx20_8 hcs8
  refine step_encraw_tag9_x hC hEV hDR ss v s0.sp cap7 ptr7 G.pending m.pendingPreKey
    (((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten)
    hpending
    (by revert hpending; cases h : G.pending with
        | none => intro _; trivial
        | some g => intro _; exact hpend_bound g h)
    (by simp only [List.length_append]; omega)
    hpc8 hrun8 hsp8 halign htr8 hx19_8 hx20_8 hcs8 (by sep_frame) ?_
  intro s9 cap8 ptr8 hpc9 hrun9 hsp9 htr9 hx19_9 hx20_9 hcs9
  refine step_encraw_tag10_x hDR hEV ss v s0.sp cap8 ptr8 m.remoteRegistrationId
    ((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey)
    (by simp only [List.length_append]; omega)
    hpc9 hrun9 hsp9 halign htr9 hx19_9 hx20_9 hcs9 (by sep_frame) ?_
  intro s10 cap9 ptr9 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10
  refine step_encraw_tag11_x hDR hEV ss v s0.sp cap9 ptr9 m.localRegistrationId
    (((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey) ++
      uint32Field 10 m.remoteRegistrationId)
    (by simp only [List.length_append]; omega)
    hpc10 hrun10 hsp10 halign htr10 hx19_10 hx20_10 hcs10 (by sep_frame) ?_
  intro s11 cap10 ptr10 hpc11 hrun11 hsp11 htr11 hx19_11 hx20_11 hcs11
  refine step_encraw_tag13_x hDR hEV hC ss v s0.sp G.alice.cap G.alice.ptr cap10 ptr10
    ((((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey) ++
      uint32Field 10 m.remoteRegistrationId) ++
      uint32Field 11 m.localRegistrationId)
    m.aliceBaseKey
    (by simp only [List.length_append]; omega)
    hpc11 hrun11 hsp11 halign htr11 hx19_11 hx20_11 hcs11 (by sep_frame) ?_
  intro s12 cap11 ptr11 hpc12 hrun12 hsp12 htr12 hx19_12 hx20_12 hcs12
  refine step_encraw_tag14_x hDR hEV hC ss v s0.sp cap11 ptr11 G.kyber m.pendingKyberPreKey
    (((((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey) ++
      uint32Field 10 m.remoteRegistrationId) ++
      uint32Field 11 m.localRegistrationId) ++
      bytesField 13 m.aliceBaseKey)
    hkyber
    (by revert hkyber; cases h : m.pendingKyberPreKey with
        | none => intro _; trivial
        | some k => intro _; exact hkyber_bound k h)
    (by simp only [List.length_append]; omega)
    hpc12 hrun12 hsp12 halign htr12 hx19_12 hx20_12 hcs12 (by sep_frame) ?_
  intro s13 cap12 ptr12 hpc13 hrun13 hsp13 htr13 hx19_13 hx20_13 hcs13
  refine step_encraw_tag15_x hDR hEV hC ss v s0.sp G.pq.cap G.pq.ptr cap12 ptr12
    ((((((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey) ++
      uint32Field 10 m.remoteRegistrationId) ++
      uint32Field 11 m.localRegistrationId) ++
      bytesField 13 m.aliceBaseKey) ++
      msgField 14 (m.pendingKyberPreKey.map encPendingKyber))
    m.state.pqRatchetState
    (by simp only [List.length_append]; omega)
    hpc13 hrun13 hsp13 halign htr13 hx19_13 hx20_13 hcs13 (by sep_frame) ?_
  intro s14 cap13 ptr13 hpc14 hrun14 hsp14 htr14 hcs14
  refine step_encraw_epilogue_x s0.sp v56
    hpc14 hrun14 hsp14 halign htr14 rfl hcs14 (by sep_frame) ?_
  intro sm hpcm hrunm hspm htrm hcsm
  apply SepWPpIn.done hpcm hrunm
  refine ⟨fun hm => ?_, hspm, hcsm⟩
  rw [show (⌜sm.trace = s0.trace⌝ ∗
        sessionStateReprAt A ss G m ∗
          (∃∗ cap', ∃∗ ptr', vecU8At A v cap' ptr' (bs0 ++ encSessionMem G m)) ∗
            A.pool ∗ stackAt s0.sp encodeRawStackX ∗ R) =
      (⌜sm.trace = s0.trace⌝ ∗
        sessionStateReprAt A ss G m ∗
          (∃∗ cap', ∃∗ ptr', vecU8At A v cap' ptr' (bs0 ++ encSessionMem G m)) ∗
            A.pool ∗ stackAt s0.sp encodeRawStackX) ∗ R by simp only [sepConj_assoc]]
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  have htr_true : (sm.trace = s0.trace) = True := eq_true htrm
  have hbytes :
      (((((((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
        bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
        uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
        ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
        encPendingFieldMem G.pending m.pendingPreKey) ++
        uint32Field 10 m.remoteRegistrationId) ++
        uint32Field 11 m.localRegistrationId) ++
        bytesField 13 m.aliceBaseKey) ++
        msgField 14 (m.pendingKyberPreKey.map encPendingKyber)) ++
        bytesField 15 m.state.pqRatchetState) =
      bs0 ++ encSessionMem G m := by
    simp only [encSessionMem, List.append_assoc]
  rw [htr_true, pure_true, emp_sepConj, hSessEq, hbytes]
  refine Entails.trans
    (Q := sessionRawOpen A ss G m ∗
      (vecU8At A v cap13 ptr13 (bs0 ++ encSessionMem G m) ∗ A.pool ∗ stackAt s0.sp encodeRawStackX))
    ?_
    (sepConj_mono_right (sepConj_mono_left (vecU8At_entails_exists_er A v cap13 ptr13 _)))
  unfold sessionRawOpen
  exact (by sep_frame)

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `14`) -/

section Placed

open CryptoVerification CryptoVerification.E2E.Record.Placed

private theorem sepWPpLsCl_open_sessionAt {pl : Obj.MultiPlacement} {prog : Program}
    {ret : BitVec 64} {s : State}
    {A : RustAlloc} {ss : BitVec 64} {G : SessionGhost} {m : Session (List (BitVec 8))}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : PendingRel G.pending m.pendingPreKey →
      KyberRel G.kyber m.pendingKyberPreKey →
      (sessionStateReprAt A ss G m = sessionRawOpen A ss G m) →
      SepWPpLsCl pl prog ret s (sessionRawOpen A ss G m ∗ F) Q Qp) :
    SepWPpLsCl pl prog ret s (sessionStateReprAt A ss G m ∗ F) Q Qp := by
  intro hcl
  apply sepWPp_open_sessionAtX
  intro hp1 hp2 heq
  exact h hp1 hp2 heq hcl

private theorem sepWPpLsCl_to_panicAllocPost {pl : Obj.MultiPlacement} {prog : Program}
    {ret : BitVec 64} {s0 s : State}
    {P R : SepProp} {Q : State → SepProp → Prop}
    (h : SepWPpLsCl pl prog ret s P Q (PanicAllocPost s0)) :
    SepWPpLsCl pl prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  intro hcl
  exact sepWPp_to_panicAllocPostX (h hcl)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 400000 in
/-- Block `14` (`SessionStructure::encode_raw`) at `encodeRawStackX` under `[LibsignalPlacement]`. -/
theorem encodeRaw_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (hC : SerContractsXPlaced A H)
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (hEC : EncodeChainPlacedOkX A H) :
    EncodeRawPlacedOkX A H := by
  apply subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
  intro ⟨ss, G, m, v, cap0, ptr0, bs0⟩ R s0 hpc0 hrun0 hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(encodeRawSpecX A).pre ⟨ss, G, m, v, cap0, ptr0, bs0⟩ s0, R, hpre, ?_⟩
  dsimp only [encodeRawSpecX]
  apply sepWPpLsCl_to_panicAllocPost
  simp only [sepConj_assoc]
  refine SepWPpLsCl.pure_elim fun ⟨hx0, hx1, hfit⟩ => ?_
  refine sepWPpLsCl_open_sessionAt fun hpending hkyber hSessEq => ?_
  have hlik_le := length_le_bytesField_length_er 2 G.localIk.bytes
  have hrik_le := length_le_bytesField_length_er 3 G.remoteIk.bytes
  have hroot_le := length_le_bytesField_length_er 4 (HMAC.keyToBytes32 m.state.rootKey)
  have halice_le := length_le_bytesField_length_er 13 m.aliceBaseKey
  have hpq_le := length_le_bytesField_length_er 15 m.state.pqRatchetState
  have hfit_expand :
      bs0.length +
      ((uint32Field 1 m.state.sessionVersion).length +
       (bytesField 2 G.localIk.bytes).length +
       (bytesField 3 G.remoteIk.bytes).length +
       (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
       (uint32Field 5 m.state.previousCounter).length +
       (encSenderFieldMem G.sender m.state.senderChain).length +
       (((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten).length +
       (encPendingFieldMem G.pending m.pendingPreKey).length +
       (uint32Field 10 m.remoteRegistrationId).length +
       (uint32Field 11 m.localRegistrationId).length +
       (bytesField 13 m.aliceBaseKey).length +
       (msgField 14 (m.pendingKyberPreKey.map encPendingKyber)).length +
       (bytesField 15 m.state.pqRatchetState).length) < 2 ^ 32 := by
    simpa only [encSessionMem, List.length_append, Nat.add_assoc] using hfit
  have hpend_bound := pending_vec_length_lt_er G.pending m.pendingPreKey hpending (by omega)
  have hkyber_bound := kyber_ct_length_lt_er m.pendingKyberPreKey (by omega)
  unfold sessionRawOpen
  refine step_encraw_prologue_placed_x H ss v s0.sp hpc0 hrun0 rfl halign rfl hx0 hx1
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl (by sep_frame) ?_
  intro s1 v56 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx20_1 hcs1
  refine step_encraw_tag1_placed_x hDR hEV ss v s0.sp cap0 ptr0 m.state.sessionVersion bs0
    (by omega) hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx20_1 hcs1 (by sep_frame) ?_
  intro s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
  refine step_encraw_tag2_placed_x hC hDR hEV ss v s0.sp G.localIk.cap G.localIk.ptr cap1 ptr1
    (bs0 ++ uint32Field 1 m.state.sessionVersion) G.localIk.bytes
    (by simp only [List.length_append]; omega)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2 (by sep_frame) ?_
  intro s3 cap2 ptr2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
  refine step_encraw_tag3_placed_x hC hDR hEV ss v s0.sp G.remoteIk.cap G.remoteIk.ptr cap2 ptr2
    ((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) G.remoteIk.bytes
    (by simp only [List.length_append]; omega)
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3 (by sep_frame) ?_
  intro s4 cap3 ptr3 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4
  refine step_encraw_tag4_placed_x hC hDR hEV ss v s0.sp G.root.cap G.root.ptr cap3 ptr3
    (((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes)
    (HMAC.keyToBytes32 m.state.rootKey)
    (by simp only [List.length_append]; omega)
    hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hcs4 (by sep_frame) ?_
  intro s5 cap4 ptr4 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hcs5
  refine step_encraw_tag5_placed_x hDR hEV ss v s0.sp cap4 ptr4 m.state.previousCounter
    ((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey))
    (by simp only [List.length_append]; omega)
    hpc5 hrun5 hsp5 halign htr5 hx19_5 hx20_5 hcs5 (by sep_frame) ?_
  intro s6 cap5 ptr5 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6
  refine step_encraw_tag6_placed_x hEC ss v s0.sp cap5 ptr5 G.sender m.state.senderChain
    (((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter)
    (by simp only [List.length_append]; omega)
    hpc6 hrun6 hsp6 halign htr6 hx19_6 hx20_6 hcs6 (by sep_frame) ?_
  intro s7 cap6 ptr6 hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hcs7
  refine step_encraw_tag7_placed_x hEC ss v s0.sp G.chainsCap G.chainsPtr cap6 ptr6
    (G.chains.zip m.state.receiverChains)
    ((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain)
    (by simp only [List.length_append]; omega)
    hpc7 hrun7 hsp7 halign htr7 hx19_7 hx20_7 hcs7 (by sep_frame) ?_
  intro s8 cap7 ptr7 hpc8 hrun8 hsp8 htr8 hx19_8 hx20_8 hcs8
  refine step_encraw_tag9_placed_x hC hEV hDR ss v s0.sp cap7 ptr7 G.pending m.pendingPreKey
    (((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten)
    hpending
    (by revert hpending; cases h : G.pending with
        | none => intro _; trivial
        | some g => intro _; exact hpend_bound g h)
    (by simp only [List.length_append]; omega)
    hpc8 hrun8 hsp8 halign htr8 hx19_8 hx20_8 hcs8 (by sep_frame) ?_
  intro s9 cap8 ptr8 hpc9 hrun9 hsp9 htr9 hx19_9 hx20_9 hcs9
  refine step_encraw_tag10_placed_x hDR hEV ss v s0.sp cap8 ptr8 m.remoteRegistrationId
    ((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey)
    (by simp only [List.length_append]; omega)
    hpc9 hrun9 hsp9 halign htr9 hx19_9 hx20_9 hcs9 (by sep_frame) ?_
  intro s10 cap9 ptr9 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10
  refine step_encraw_tag11_placed_x hDR hEV ss v s0.sp cap9 ptr9 m.localRegistrationId
    (((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey) ++
      uint32Field 10 m.remoteRegistrationId)
    (by simp only [List.length_append]; omega)
    hpc10 hrun10 hsp10 halign htr10 hx19_10 hx20_10 hcs10 (by sep_frame) ?_
  intro s11 cap10 ptr10 hpc11 hrun11 hsp11 htr11 hx19_11 hx20_11 hcs11
  refine step_encraw_tag13_placed_x hDR hEV hC ss v s0.sp G.alice.cap G.alice.ptr cap10 ptr10
    ((((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey) ++
      uint32Field 10 m.remoteRegistrationId) ++
      uint32Field 11 m.localRegistrationId)
    m.aliceBaseKey
    (by simp only [List.length_append]; omega)
    hpc11 hrun11 hsp11 halign htr11 hx19_11 hx20_11 hcs11 (by sep_frame) ?_
  intro s12 cap11 ptr11 hpc12 hrun12 hsp12 htr12 hx19_12 hx20_12 hcs12
  refine step_encraw_tag14_placed_x hDR hEV hC ss v s0.sp cap11 ptr11 G.kyber m.pendingKyberPreKey
    (((((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey) ++
      uint32Field 10 m.remoteRegistrationId) ++
      uint32Field 11 m.localRegistrationId) ++
      bytesField 13 m.aliceBaseKey)
    hkyber
    (by revert hkyber; cases h : m.pendingKyberPreKey with
        | none => intro _; trivial
        | some k => intro _; exact hkyber_bound k h)
    (by simp only [List.length_append]; omega)
    hpc12 hrun12 hsp12 halign htr12 hx19_12 hx20_12 hcs12 (by sep_frame) ?_
  intro s13 cap12 ptr12 hpc13 hrun13 hsp13 htr13 hx19_13 hx20_13 hcs13
  refine step_encraw_tag15_placed_x hDR hEV hC ss v s0.sp G.pq.cap G.pq.ptr cap12 ptr12
    ((((((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey) ++
      uint32Field 10 m.remoteRegistrationId) ++
      uint32Field 11 m.localRegistrationId) ++
      bytesField 13 m.aliceBaseKey) ++
      msgField 14 (m.pendingKyberPreKey.map encPendingKyber))
    m.state.pqRatchetState
    (by simp only [List.length_append]; omega)
    hpc13 hrun13 hsp13 halign htr13 hx19_13 hx20_13 hcs13 (by sep_frame) ?_
  intro s14 cap13 ptr13 hpc14 hrun14 hsp14 htr14 hcs14
  refine step_encraw_epilogue_placed_x s0.sp v56
    hpc14 hrun14 hsp14 halign htr14 rfl hcs14 (by sep_frame) ?_
  intro sm hpcm hrunm hspm htrm hcsm
  apply SepWPpLsCl.done hpcm hrunm
  refine ⟨fun hm => ?_, hspm, hcsm⟩
  rw [show (⌜sm.trace = s0.trace⌝ ∗
        sessionStateReprAt A ss G m ∗
          (∃∗ cap', ∃∗ ptr', vecU8At A v cap' ptr' (bs0 ++ encSessionMem G m)) ∗
            A.pool ∗ stackAt s0.sp encodeRawStackX ∗ R) =
      (⌜sm.trace = s0.trace⌝ ∗
        sessionStateReprAt A ss G m ∗
          (∃∗ cap', ∃∗ ptr', vecU8At A v cap' ptr' (bs0 ++ encSessionMem G m)) ∗
            A.pool ∗ stackAt s0.sp encodeRawStackX) ∗ R by simp only [sepConj_assoc]]
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  have htr_true : (sm.trace = s0.trace) = True := eq_true htrm
  have hbytes :
      (((((((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
        bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
        uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
        ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
        encPendingFieldMem G.pending m.pendingPreKey) ++
        uint32Field 10 m.remoteRegistrationId) ++
        uint32Field 11 m.localRegistrationId) ++
        bytesField 13 m.aliceBaseKey) ++
        msgField 14 (m.pendingKyberPreKey.map encPendingKyber)) ++
        bytesField 15 m.state.pqRatchetState) =
      bs0 ++ encSessionMem G m := by
    simp only [encSessionMem, List.append_assoc]
  rw [htr_true, pure_true, emp_sepConj, hSessEq, hbytes]
  refine Entails.trans
    (Q := sessionRawOpen A ss G m ∗
      (vecU8At A v cap13 ptr13 (bs0 ++ encSessionMem G m) ∗ A.pool ∗ stackAt s0.sp encodeRawStackX))
    ?_
    (sepConj_mono_right (sepConj_mono_left (vecU8At_entails_exists_er A v cap13 ptr13 _)))
  unfold sessionRawOpen
  exact (by sep_frame)

theorem encodeRaw_placed_ok_cl [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H)
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (hEC : EncodeChainPlacedOkX A H) :
    subroutine_ok callerProg (lsmpl.base 14) (withLsCl lsmpl (encodeRawSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeRaw_placed_ok_ext A H hC hEV hDR hEC)

end Placed

end CryptoVerification.E2E.Record.Serialization
