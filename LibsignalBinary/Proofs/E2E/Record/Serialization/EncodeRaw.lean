/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymA
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymB
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChain
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingKyberPreKey
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyFields
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PqRatchetStateEpilogue
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.RegistrationIdsBaseKey
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.RemoteIdentityRootKeyCounter
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint
import ProofLib.SepLogic.WPp

/-!
# `<SessionStructure as prost::Message>::encode_raw::<Vec<u8>>` (`0x4d38`)

Proves `encodeRaw_ok` and its relocatable `[LibsignalPlacement]` counterparts (block `14`):
appends `encSessionMem G s` (tags 1–7, 9, 10, 11, 13, 14, and 15) to the destination `Vec<u8>`
while preserving `sessionStateReprAt`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux

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

private theorem sepWPp_open_sessionAt {prog : Program} {ret : BitVec 64} {s : State}
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
  exact entails_of_sep_focus (by sep_focus)

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

private theorem sepWPp_to_panicAllocPost {prog : Program} {ret : BitVec 64} {s0 s : State}
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
/-- `<SessionStructure as prost::Message>::encode_raw::<Vec<u8>>` (`0x4d38`) satisfies
`encodeRawSpec` given `encode_varint`, `do_reserve_and_handle`, and `encode::<Chain>`. -/
theorem encodeRaw_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (hEC : OkAt b C ctl abs encodeChainName (encodeChainSpec A)) :
    OkAt b C ctl abs encodeRawName (encodeRawSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, G, m, v, cap0, ptr0, bs0⟩ R s0 hpc0 hrun0 hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(encodeRawSpec A).pre ⟨ss, G, m, v, cap0, ptr0, bs0⟩ s0, R, hpre, ?_⟩
  dsimp only [encodeRawSpec]
  apply sepWPp_to_panicAllocPost
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hfit⟩ => ?_
  refine sepWPp_open_sessionAt fun hpending hkyber hSessEq => ?_
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
  refine step_encraw_prologue ss v s0.sp hpc0 hrun0 rfl halign rfl hx0 hx1
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl (by sep_focus) ?_
  intro s1 v56 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx20_1 hcs1
  refine step_encraw_tag1 hDR hEV ss v s0.sp cap0 ptr0 m.state.sessionVersion bs0
    (by omega) hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx20_1 hcs1 (by sep_focus) ?_
  intro s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
  refine step_encraw_tag2 hDR hEV ss v s0.sp G.localIk.cap G.localIk.ptr cap1 ptr1
    (bs0 ++ uint32Field 1 m.state.sessionVersion) G.localIk.bytes
    (by simp only [List.length_append]; omega)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2 (by sep_focus) ?_
  intro s3 cap2 ptr2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
  refine step_encraw_tag3 hDR hEV ss v s0.sp G.remoteIk.cap G.remoteIk.ptr cap2 ptr2
    ((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) G.remoteIk.bytes
    (by simp only [List.length_append]; omega)
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3 (by sep_focus) ?_
  intro s4 cap3 ptr3 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4
  refine step_encraw_tag4 hDR hEV ss v s0.sp G.root.cap G.root.ptr cap3 ptr3
    (((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes)
    (HMAC.keyToBytes32 m.state.rootKey)
    (by simp only [List.length_append]; omega)
    hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hcs4 (by sep_focus) ?_
  intro s5 cap4 ptr4 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hcs5
  refine step_encraw_tag5 hDR hEV ss v s0.sp cap4 ptr4 m.state.previousCounter
    ((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey))
    (by simp only [List.length_append]; omega)
    hpc5 hrun5 hsp5 halign htr5 hx19_5 hx20_5 hcs5 (by sep_focus) ?_
  intro s6 cap5 ptr5 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6
  refine step_encraw_tag6 hEC ss v s0.sp cap5 ptr5 G.sender m.state.senderChain
    (((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter)
    (by simp only [List.length_append]; omega)
    hpc6 hrun6 hsp6 halign htr6 hx19_6 hx20_6 hcs6 (by sep_focus) ?_
  intro s7 cap6 ptr6 hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hcs7
  refine step_encraw_tag7 hEC ss v s0.sp G.chainsCap G.chainsPtr cap6 ptr6
    (G.chains.zip m.state.receiverChains)
    ((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain)
    (by simp only [List.length_append]; omega)
    hpc7 hrun7 hsp7 halign htr7 hx19_7 hx20_7 hcs7 (by sep_focus) ?_
  intro s8 cap7 ptr7 hpc8 hrun8 hsp8 htr8 hx19_8 hx20_8 hcs8
  refine step_encraw_tag9 hEV hDR ss v s0.sp cap7 ptr7 G.pending m.pendingPreKey
    (((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten)
    hpending
    (by revert hpending; cases h : G.pending with
        | none => intro _; trivial
        | some g => intro _; exact hpend_bound g h)
    (by simp only [List.length_append]; omega)
    hpc8 hrun8 hsp8 halign htr8 hx19_8 hx20_8 hcs8 (by sep_focus) ?_
  intro s9 cap8 ptr8 hpc9 hrun9 hsp9 htr9 hx19_9 hx20_9 hcs9
  refine step_encraw_tag10 hDR hEV ss v s0.sp cap8 ptr8 m.remoteRegistrationId
    ((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey)
    (by simp only [List.length_append]; omega)
    hpc9 hrun9 hsp9 halign htr9 hx19_9 hx20_9 hcs9 (by sep_focus) ?_
  intro s10 cap9 ptr9 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10
  refine step_encraw_tag11 hDR hEV ss v s0.sp cap9 ptr9 m.localRegistrationId
    (((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey) ++
      uint32Field 10 m.remoteRegistrationId)
    (by simp only [List.length_append]; omega)
    hpc10 hrun10 hsp10 halign htr10 hx19_10 hx20_10 hcs10 (by sep_focus) ?_
  intro s11 cap10 ptr10 hpc11 hrun11 hsp11 htr11 hx19_11 hx20_11 hcs11
  refine step_encraw_tag13 hDR hEV ss v s0.sp G.alice.cap G.alice.ptr cap10 ptr10
    ((((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey) ++
      uint32Field 10 m.remoteRegistrationId) ++
      uint32Field 11 m.localRegistrationId)
    m.aliceBaseKey
    (by simp only [List.length_append]; omega)
    hpc11 hrun11 hsp11 halign htr11 hx19_11 hx20_11 hcs11 (by sep_focus) ?_
  intro s12 cap11 ptr11 hpc12 hrun12 hsp12 htr12 hx19_12 hx20_12 hcs12
  refine step_encraw_tag14 hEV hDR ss v s0.sp cap11 ptr11 G.kyber m.pendingKyberPreKey
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
    hpc12 hrun12 hsp12 halign htr12 hx19_12 hx20_12 hcs12 (by sep_focus) ?_
  intro s13 cap12 ptr12 hpc13 hrun13 hsp13 htr13 hx19_13 hx20_13 hcs13
  refine step_encraw_tag15 hDR hEV ss v s0.sp G.pq.cap G.pq.ptr cap12 ptr12
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
    hpc13 hrun13 hsp13 halign htr13 hx19_13 hx20_13 hcs13 (by sep_focus) ?_
  intro s14 cap13 ptr13 hpc14 hrun14 hsp14 htr14 hcs14
  refine step_encraw_epilogue s0.sp v56
    hpc14 hrun14 hsp14 halign htr14 rfl hcs14 (by sep_focus) ?_
  intro sm hpcm hrunm hspm htrm hcsm
  apply SepWPp.done hpcm hrunm
  refine ⟨fun hm => ?_, hspm, hcsm⟩
  rw [show (⌜sm.trace = s0.trace⌝ ∗
        sessionStateReprAt A ss G m ∗
          (∃∗ cap', ∃∗ ptr', vecU8At A v cap' ptr' (bs0 ++ encSessionMem G m)) ∗
            A.pool ∗ stackAt s0.sp encodeRawStack ∗ R) =
      (⌜sm.trace = s0.trace⌝ ∗
        sessionStateReprAt A ss G m ∗
          (∃∗ cap', ∃∗ ptr', vecU8At A v cap' ptr' (bs0 ++ encSessionMem G m)) ∗
            A.pool ∗ stackAt s0.sp encodeRawStack) ∗ R by simp only [sepConj_assoc]]
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
      (vecU8At A v cap13 ptr13 (bs0 ++ encSessionMem G m) ∗ A.pool ∗ stackAt s0.sp encodeRawStack))
    ?_
    (sepConj_mono_right (sepConj_mono_left (vecU8At_entails_exists_er A v cap13 ptr13 _)))
  unfold sessionRawOpen
  exact entails_of_sep_focus (by sep_focus)

/-! ## Relocatable `[LibsignalPlacement]` proofs (block `14`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

attribute [local irreducible] Program.fetch Program.externAt?
  vecRest Prost.vecU8Buf vecSrcRest vecCopyDone kyberTailRest
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate32_signExtend64_er truncate32_zeroExtend64
  Prost.ofNat_countLeadingZeros_64
  Prost.ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  er_truncate32_zext64_lsr6
  erHwVarintLen_eq_encodeVarint_length
  erHwVarintLen_bvShift_eq_encodeVarint_length
  bv_add_neg80_4b

set_option maxHeartbeats 400000 in
private theorem step_tag14_write_tag_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8)) (hcap_g : g.vec.cap.toNat < 2 ^ 63) (hlen_lt : bs.length + 1 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1292#64) (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64) (halign : sp0 &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ss) (hcs : EncRawUpperSaved s0 s)
    (hP : P = (kyberOpenAt A ss g k ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 1348#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → sm.sp = sp0 - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((kyberOpenAt A ss g k ∗ vecU8At A v cap' ptr' (bs ++ [0x72#8]) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf_placed _ A H hDR
  have h8 : (ss + 296#64) + 8#64 = ss + 304#64 := BitVec.add_assoc ss 296#64 8#64
  have h16 : (ss + 296#64) + 16#64 = ss + 312#64 := BitVec.add_assoc ss 296#64 16#64
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
    (h := fun hle _ _ => ?_)
  have hcmn1 := cmn1_beq_zero_false hcap_g
  have hcmn2 := cap_beq_noneCap_false hcap_g
  by_cases hlt : bs.length < cap.toNat
  · have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A v cap ptr bs hlt]
    unfold kyberOpenAt
    rw [Prost.vecU8At_eq_header_sep_buf A (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
    simp only [vecHeader, h8, h16, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun old => ?_
    apply sepWPp_of_sepWP_lscl_er hcl (mid := (blkPl_14).base + 1348#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    rw [← vecU8At_close_one A v cap ptr bs 0x72#8 hlt]
    unfold kyberOpenAt
    rw [Prost.vecU8At_eq_header_sep_buf A (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
    simp only [vecHeader, h8, h16]
    exact entails_of_sep_focus (by sep_focus)
  · have hcap_eq : cap.toNat = bs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    rw [Prost.vecU8At_eq_header_sep_buf A v cap ptr bs]
    unfold kyberOpenAt
    rw [Prost.vecU8At_eq_header_sep_buf A (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
    simp only [vecHeader, h8, h16, sepConj_assoc]
    apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2348#64) bs 1
      (by omega) (by omega) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) hcl0
      (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by sep_focus) ?_
    intro s1 newCap p1 hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hnew_ge _
    have hx19_1 : s1.readReg64 .x19 = v := by have := hcs1.1; simp only [arm64_norm, *] at this; exact this
    have hx20_1 : s1.readReg64 .x20 = ss := by have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
    have hcs_1 : EncRawUpperSaved s0 s1 :=
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
        (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
    have hlt_new : bs.length < newCap.toNat := by omega
    rw [vecU8At_open_one A v newCap p1 bs hlt_new]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun old => ?_
    apply sepWPp_of_sepWP_lscl_er hcl1 (mid := (blkPl_14).base + 1348#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    refine SepWPp.weaken_pre ?_ (hnext _ newCap p1
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    rw [← vecU8At_close_one A v newCap p1 bs 0x72#8 hlt_new]
    unfold kyberOpenAt
    rw [Prost.vecU8At_eq_header_sep_buf A (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
    simp only [vecHeader, h8, h16]
    exact entails_of_sep_focus (by sep_focus)

set_option maxHeartbeats 400000 in
private theorem step_tag14_len1_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (ss v sp0 : BitVec 64) (k : PendingKyberPreKey) (hlt_ct : k.ciphertext.length < 2 ^ 63)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1348#64) (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hsp : s.sp = sp0 - 80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ss)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length)
    (hcs : EncRawUpperSaved s0 s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_14).base + (if k.ciphertext.isEmpty then 1440#64 else 1384#64) →
      sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (uint32Field 1 k.preKeyId).length →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm P Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  by_cases hpk : k.preKeyId = 0#32
  · by_cases hct : k.ciphertext = []
    · apply sepWPp_of_sepWP_lscl_er hcl (mid := (blkPl_14).base + 1440#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      exact hnext _ (by simp only [arm64_norm, List.isEmpty_nil, ↓reduceIte, *])
        (by simp only [arm64_norm, *]) hcl0 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hpk, uint32Field1_zero_eq_er])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    · have hempty : k.ciphertext.isEmpty = false := by cases h : k.ciphertext <;> simp_all
      have hbeq_ct := ofNat64_len_beq_zero_false hct hlt_ct
      apply sepWPp_of_sepWP_lscl_er hcl (mid := (blkPl_14).base + 1384#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      exact hnext _ (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
        (by simp only [arm64_norm, *]) hcl0 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hpk, uint32Field1_zero_eq_er])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hbeq0 := zext64_beq_zero_false_3b hpk
    by_cases hct : k.ciphertext = []
    · apply sepWPp_of_sepWP_lscl_er hcl (mid := (blkPl_14).base + 1440#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      exact hnext _ (by simp only [arm64_norm, List.isEmpty_nil, ↓reduceIte, *])
        (by simp only [arm64_norm, *]) hcl0 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, ← uint32Field1_nonzero_length_bv_er hpk, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    · have hempty : k.ciphertext.isEmpty = false := by cases h : k.ciphertext <;> simp_all
      have hbeq_ct := ofNat64_len_beq_zero_false hct hlt_ct
      apply sepWPp_of_sepWP_lscl_er hcl (mid := (blkPl_14).base + 1384#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      exact hnext _ (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
        (by simp only [arm64_norm, *]) hcl0 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, ← uint32Field1_nonzero_length_bv_er hpk, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)

set_option maxHeartbeats 400000 in
private theorem step_tag14_len2_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok (lsProg_10 H) (blkPl_10).base (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8)) (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + (if k.ciphertext.isEmpty then 1440#64 else 1384#64))
    (hrun : s.status = .Running) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64) (halign : sp0 &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (uint32Field 1 k.preKeyId).length)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (kyberOpenAt A ss g k ∗ vecU8At A v cap ptr (bs ++ [0x72#8]) ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + (if k.preKeyId == 0#32 then 1504#64 else 1456#64) →
      sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((kyberOpenAt A ss g k ∗
          vecU8At A v cap' ptr'
            ((bs ++ [0x72#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint_placed _ A H hEV
  rw [hP]
  by_cases hct : k.ciphertext = []
  · have hempty : k.ciphertext.isEmpty = true := List.isEmpty_iff.mpr hct
    simp only [hempty, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    refine hCallEV sp0 (BitVec.ofNat 64 (encPendingKyber k).length) v cap ptr
      ((blkPl_14).base + 1452#64) (bs ++ [0x72#8]) (by simp; omega)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) hcl0
      (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, ← encPendingKyber_length_bv_ct_nil k hct, *])
      (by simp only [arm64_norm, *]) (by sep_focus) ?_
    intro s1 cap' ptr' hpc1 hrun1 hcl1 hsp1 htr1 hcs1
    have hx19_1 : s1.readReg64 .x19 = v := by have := hcs1.1; simp only [arm64_norm, hx19] at this; exact this
    have hx20_1 : s1.readReg64 .x20 = ss := by have := hcs1.2.1; simp only [arm64_norm, hx20] at this; exact this
    have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length := by
      have := hcs1.2.2.1; simp only [arm64_norm, hx21] at this; exact this
    have hx22_1 : s1.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId := by
      have := hcs1.2.2.2.1; simp only [arm64_norm, hx22] at this; exact this
    have hcs_1 : EncRawUpperSaved s0 s1 :=
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
        (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
    by_cases hpk : k.preKeyId = 0#32
    · have hpk_beq : (k.preKeyId == 0#32) = true := beq_iff_eq.mpr hpk
      apply sepWPp_of_sepWP_lscl_er hcl1 (mid := (blkPl_14).base + 1504#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl2
      refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
        (by simp only [arm64_norm, ↓reduceIte, *]) (by simp only [arm64_norm, *]) hcl2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      exact entails_of_sep_focus (by sep_focus)
    · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
      have hbeq0 := zext64_beq_zero_false_3b hpk
      apply sepWPp_of_sepWP_lscl_er hcl1 (mid := (blkPl_14).base + 1456#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl2
      refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
        (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
        (by simp only [arm64_norm, *]) hcl2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      exact entails_of_sep_focus (by sep_focus)
  · have hempty : k.ciphertext.isEmpty = false := by cases h : k.ciphertext <;> simp_all
    simp only [hempty, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    refine hCallEV sp0 (BitVec.ofNat 64 (encPendingKyber k).length) v cap ptr
      ((blkPl_14).base + 1424#64) (bs ++ [0x72#8]) (by simp; omega)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) hcl0
      (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, ← encPendingKyber_length_bv k, ← bytesField2_nonempty_length_bv hct, *])
      (by simp only [arm64_norm, *]) (by sep_focus) ?_
    intro s1 cap' ptr' hpc1 hrun1 hcl1 hsp1 htr1 hcs1
    have hx19_1 : s1.readReg64 .x19 = v := by have := hcs1.1; simp only [arm64_norm, *] at this; exact this
    have hx20_1 : s1.readReg64 .x20 = ss := by have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
    have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length := by
      have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hx22_1 : s1.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId := by
      have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hcs_1 : EncRawUpperSaved s0 s1 :=
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
        (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
    by_cases hpk : k.preKeyId = 0#32
    · have hpk_beq : (k.preKeyId == 0#32) = true := beq_iff_eq.mpr hpk
      apply sepWPp_of_sepWP_lscl_er hcl1 (mid := (blkPl_14).base + 1504#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl2
      refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
        (by simp only [arm64_norm, ↓reduceIte, *]) (by simp only [arm64_norm, *]) hcl2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      exact entails_of_sep_focus (by sep_focus)
    · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
      have hbeq0 := zext64_beq_zero_false_3b hpk
      apply sepWPp_of_sepWP_lscl_er hcl1 (mid := (blkPl_14).base + 1456#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl2
      refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
        (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
        (by simp only [arm64_norm, *]) hcl2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      exact entails_of_sep_focus (by sep_focus)

set_option maxHeartbeats 400000 in
private theorem step_tag14_sub1_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok (lsProg_10 H) (blkPl_10).base (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8)) (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + (if k.preKeyId == 0#32 then 1504#64 else 1456#64))
    (hrun : s.status = .Running) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64) (halign : sp0 &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ss)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (kyberOpenAt A ss g k ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 1504#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → sm.sp = sp0 - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = ss →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((kyberOpenAt A ss g k ∗ vecU8At A v cap' ptr' (bs ++ uint32Field 1 k.preKeyId) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  by_cases hpk : k.preKeyId = 0#32
  · simp only [hpk, beq_self_eq_true, ↓reduceIte] at hpc
    rw [hP]
    refine SepWPp.weaken_pre ?_ (hnext s cap ptr hpc hrun hcl hsp htr hx19 hx20 hx21 hcs)
    simp only [hpk, uint32Field1_zero_eq_er, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
    simp only [hpk_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    have hCallEV := @encraw_call_encodeVarint_placed _ A H hEV
    have hCallDR := @encraw_call_doReserve_buf_placed _ A H hDR
    rw [hP]
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      have hclose := vecU8At_close_one A v cap ptr bs 0x08#8 hlt
      refine SepWPp.weaken_pre (P' :=
          (vecU8At A v cap ptr (bs ++ [0x08#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
            (kyberOpenAt A ss g k ∗ F))
        (by rw [← hclose]; exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.zeroExtend 64 k.preKeyId) v cap ptr ((blkPl_14).base + 1504#64)
        (bs ++ [0x08#8]) (by simp; omega)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) hcl0
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_focus) ?_
      intro s1 cap' ptr' hpc1 hrun1 hcl1 hsp1 htr1 hcs1
      have hx19_1 : s1.readReg64 .x19 = v := by have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      refine SepWPp.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hcl1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hcs_1)
      rw [List.append_assoc, uint32Field1_nonzero_eq_er hpk]
      exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [Prost.vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 13)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2640#64) bs 1
        (by omega) (by omega) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) hcl0
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by sep_focus) ?_
      intro s1 newCap p1 hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hnew_ge _
      have hx19_1 : s1.readReg64 .x19 = v := by have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      have hlt_new : bs.length < newCap.toNat := by omega
      rw [vecU8At_open_one A v newCap p1 bs hlt_new]
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply sepWPp_of_sepWP_lscl_er hcl1 (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl2
      have hclose := vecU8At_close_one A v newCap p1 bs 0x08#8 hlt_new
      refine SepWPp.weaken_pre (P' :=
          (vecU8At A v newCap p1 (bs ++ [0x08#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
            (kyberOpenAt A ss g k ∗ F))
        (by rw [← hclose]; exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.zeroExtend 64 k.preKeyId) v newCap p1 ((blkPl_14).base + 1504#64)
        (bs ++ [0x08#8]) (by simp; omega)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) hcl2
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_focus) ?_
      intro s2 cap' ptr' hpc2 hrun2 hcl3 hsp2 htr2 hcs2
      have hx19_2 : s2.readReg64 .x19 = v := by have := hcs2.1; simp only [arm64_norm, *] at this; exact this
      have hx20_2 : s2.readReg64 .x20 = ss := by have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length := by
        have := hcs2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_2 : EncRawUpperSaved s0 s2 :=
        (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
      refine SepWPp.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hcl3 hsp2 htr2 hx19_2 hx20_2 hx21_2 hcs_2)
      rw [List.append_assoc, uint32Field1_nonzero_eq_er hpk]
      exact entails_of_sep_focus (by sep_focus)

set_option maxHeartbeats 400000 in
private theorem step_tag14_sub2_b_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (hf_nil : fBs ≠ []) (hf_le : fBs.length ≤ fCap.toNat) (hf_cap : fCap.toNat < 2 ^ 63)
    (hlen_lt : bs1.length + fBs.length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1560#64) (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64) (halign : sp0 &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length) (hx22 : s.readReg64 .x22 = fPtr)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A (ss + 296#64) fCap fPtr fBs ∗ vecU8At A v cap1 ptr1 bs1 ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 1608#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → sm.sp = sp0 - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = ss → EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((vecU8At A (ss + 296#64) fCap fPtr fBs ∗ vecU8At A v cap' ptr' (bs1 ++ fBs) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf_placed _ A H hDR
  have hCallMC := @encraw_call_memcpy_buf_placed _ A H hmc
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (h := fun hle1 hcap1 hptr1 => ?_)
  have hf_nat : (BitVec.ofNat 64 fBs.length).toNat = fBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [vecU8At_open_src A (ss + 296#64) fCap fPtr fBs hf_nil hf_le,
      Prost.vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  by_cases hfit : bs1.length + fBs.length ≤ cap1.toNat
  · have hhi := cmp_hi_false_of_le hfit hcap1
    apply sepWPp_of_sepWP_lscl_er hcl (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    refine hCallMC v cap1 ptr1 fPtr ((blkPl_14).base + 1600#64) bs1 fBs hfit hcap1 hptr1 hf_nil
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) hcl0
      (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_focus) ?_
    intro sm hpcm hrunm hclm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := by have := hcsm.1; simp only [arm64_norm, *] at this; exact this
    have hx20m : sm.readReg64 .x20 = ss := by have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
      have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
      have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hspm' : sm.sp = sp0 - 80#64 := by rw [hspm]; simp only [arm64_norm, *]
    have hcsm' : EncRawUpperSaved s0 sm :=
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
        (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
    apply sepWPp_of_sepWP_lscl_er hclm (mid := (blkPl_14).base + 1608#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hclm'
    rw [vecU8At_close_slice A v cap1 ptr1 bs1 fBs hfit hcap1 hptr1 hf_nil]
    refine SepWPp.weaken_pre ?_ (hnext _ cap1 ptr1
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclm'
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    rw [vecU8At_open_src A (ss + 296#64) fCap fPtr fBs hf_nil hf_le]
    exact entails_of_sep_focus (by sep_focus)
  · have hhi := cmp_hi_true_of_gt (add := fBs.length) hle1 (by omega) hcap1 (by omega)
    apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    refine hCallDR sp0 v cap1 ptr1 ((blkPl_14).base + 2700#64) bs1 fBs.length
      (by omega) (by omega) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) hcl0
      (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by sep_focus) ?_
    intro s1 newCap p' hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hnew_ge hnew_lt
    have hx19_1 : s1.readReg64 .x19 = v := by have := hcs1.1; simp only [arm64_norm, *] at this; exact this
    have hx20_1 : s1.readReg64 .x20 = ss := by have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
    have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
      have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hx22_1 : s1.readReg64 .x22 = fPtr := by have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hcs_1 : EncRawUpperSaved s0 s1 :=
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
        (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
    have hls := cmp_ls_true_of_le hnew_ge hnew_lt
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := newCap) (ptr := p') (bs := bs1)
      (h := fun _ _ hp'_ne => ?_)
    rw [Prost.vecU8At_eq_header_sep_buf A v newCap p' bs1]
    simp only [vecHeader, sepConj_assoc]
    apply sepWPp_of_sepWP_lscl_er hcl1 (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    refine hCallMC v newCap p' fPtr ((blkPl_14).base + 1600#64) bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) hcl2
      (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_focus) ?_
    intro sm hpcm hrunm hclm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := by have := hcsm.1; simp only [arm64_norm, *] at this; exact this
    have hx20m : sm.readReg64 .x20 = ss := by have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
      have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
      have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hspm' : sm.sp = sp0 - 80#64 := by rw [hspm]; simp only [arm64_norm, *]
    have hcsm' : EncRawUpperSaved s0 sm :=
      (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
        (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
    apply sepWPp_of_sepWP_lscl_er hclm (mid := (blkPl_14).base + 1608#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hclm'
    rw [vecU8At_close_slice A v newCap p' bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil]
    refine SepWPp.weaken_pre ?_ (hnext _ newCap p'
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclm'
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    rw [vecU8At_open_src A (ss + 296#64) fCap fPtr fBs hf_nil hf_le]
    exact entails_of_sep_focus (by sep_focus)

set_option maxHeartbeats 400000 in
private theorem step_tag14_sub2_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hEV : subroutine_ok (lsProg_10 H) (blkPl_10).base (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (hlen_lt : bs.length + 11 + fBs.length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1504#64) (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64) (halign : sp0 &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A (ss + 296#64) fCap fPtr fBs ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 1608#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → sm.sp = sp0 - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = ss → EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((vecU8At A (ss + 296#64) fCap fPtr fBs ∗ vecU8At A v cap' ptr' (bs ++ bytesField 2 fBs) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf_placed _ A H hDR
  have hCallEV := @encraw_call_encodeVarint_placed _ A H hEV
  have hStepB := @step_tag14_sub2_b_placed _ A H hDR hmc
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := ss + 296#64) (cap := fCap) (ptr := fPtr) (bs := fBs)
    (h := fun hf_le hf_cap _ => ?_)
  by_cases hf_nil : fBs = []
  · subst hf_nil
    simp only [sepConj_assoc]
    apply sepWPp_of_sepWP_lscl_er hcl (mid := (blkPl_14).base + 1608#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    simp only [bytesField_nil, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  · have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hfield_eq : bs ++ bytesField 2 fBs =
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 0x12#8) hf_nil]; simp only [List.append_assoc]
    have hlen_bs1 :
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length + fBs.length < 2 ^ 62 := by
      have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 fBs.length)
      simp only [List.length_append, List.length_singleton]; omega
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    rw [vecU8At_open_src_off' A ss 296#64 304#64 312#64 fCap fPtr fBs hf_nil hf_le]
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      rw [vecU8At_close_src_off' A ss 296#64 304#64 312#64 fCap fPtr fBs hf_nil hf_le,
          vecU8At_close_one A v cap ptr bs 0x12#8 hlt]
      refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr ((blkPl_14).base + 1560#64)
        (bs ++ [0x12#8]) (by simp; omega)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) hcl0
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro s1 cap1 ptr1 hpc1 hrun1 hcl1 hsp1 htr1 hcs1
      have hx19_1 : s1.readReg64 .x19 = v := by have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = fPtr := by have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      refine hStepB ss v sp0 fCap fPtr cap1 ptr1
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
        hf_nil hf_le hf_cap hlen_bs1 hpc1 hrun1 hcl1 hsp1 halign htr1
        hx19_1 hx20_1 hx21_1 hx22_1 hcs_1 (by sep_focus) ?_
      intro sm cap' ptr' hpcm hrunm hclm hspm htrm hx19m hx20m hcsm'
      rw [← hfield_eq]
      refine SepWPp.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hclm hspm htrm hx19m hx20m hcsm')
      exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [Prost.vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 13)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2668#64) bs 1
        (by omega) (by omega) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) hcl0
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by sep_focus) ?_
      intro s1 newCap p' hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hnew_ge _
      have hx19_1 : s1.readReg64 .x19 = v := by have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = fPtr := by have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      have hnew_gt : bs.length < newCap.toNat := by omega
      rw [vecU8At_open_one A v newCap p' bs hnew_gt]
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply sepWPp_of_sepWP_lscl_er hcl1 (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl2
      rw [vecU8At_close_one A v newCap p' bs 0x12#8 hnew_gt]
      refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v newCap p' ((blkPl_14).base + 1560#64)
        (bs ++ [0x12#8]) (by simp; omega)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) hcl2
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro s2 cap1 ptr1 hpc2 hrun2 hcl3 hsp2 htr2 hcs2
      have hx19_2 : s2.readReg64 .x19 = v := by have := hcs2.1; simp only [arm64_norm, *] at this; exact this
      have hx20_2 : s2.readReg64 .x20 = ss := by have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcs2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_2 : s2.readReg64 .x22 = fPtr := by have := hcs2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_2 : EncRawUpperSaved s0 s2 :=
        (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
      have hCloseSrc :
          (vecU8At A v cap1 ptr1 ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ∗
            A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
          ((ss + 296#64) ↦₆₄ fCap) ∗ ((ss + 304#64) ↦₆₄ fPtr) ∗
          ((ss + 312#64) ↦₆₄ BitVec.ofNat 64 fBs.length) ∗
          (fPtr ↦ₛ fBs) ∗ vecSrcRest A fCap fPtr fBs ∗ F =
          (vecU8At A v cap1 ptr1 ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ∗
            A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
          vecU8At A (ss + 296#64) fCap fPtr fBs ∗ F := by
        rw [vecU8At_close_src_off' A ss 296#64 304#64 312#64 fCap fPtr fBs hf_nil hf_le]
      rw [hCloseSrc]; clear hCloseSrc
      refine hStepB ss v sp0 fCap fPtr cap1 ptr1
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
        hf_nil hf_le hf_cap hlen_bs1 hpc2 hrun2 hcl3 hsp2 halign htr2
        hx19_2 hx20_2 hx21_2 hx22_2 hcs_2 (by sep_focus) ?_
      intro sm cap' ptr' hpcm hrunm hclm hspm htrm hx19m hx20m hcsm'
      rw [← hfield_eq]
      refine SepWPp.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hclm hspm htrm hx19m hx20m hcsm')
      exact entails_of_sep_focus (by sep_focus)

set_option maxHeartbeats 400000 in
private theorem step_encraw_tag14_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok (lsProg_10 H) (blkPl_10).base (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (ss v sp0 cap ptr : BitVec 64)
    (G_kyber : Option TailVecGhost) (s_kyber : Option PendingKyberPreKey)
    (bs : List (BitVec 8)) (hrel : KyberRel G_kyber s_kyber)
    (hbound : match s_kyber with | none => True | some k => k.ciphertext.length < 2 ^ 32)
    (hbs_lt : bs.length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1292#64) (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64) (halign : sp0 &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ss) (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optTailVecAt A 32 (ss + 296#64) G_kyber ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 1608#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → sm.sp = sp0 - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = ss → EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((optTailVecAt A 32 (ss + 296#64) G_kyber ∗
          vecU8At A v cap' ptr' (bs ++ msgField 14 (s_kyber.map encPendingKyber)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  cases G_kyber with
  | none =>
    cases s_kyber with
    | some k => exact False.elim hrel
    | none =>
      rw [hP, optTailVecAt_kyber_none_eq]
      simp only [sepConj_assoc]
      apply sepWPp_of_sepWP_lscl_er hcl (mid := (blkPl_14).base + 1608#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl0
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [optTailVecAt_kyber_none_eq]
      simp only [Option.map_none, msgField, List.append_nil]
      exact entails_of_sep_focus (by sep_focus)
  | some g =>
    cases s_kyber with
    | none => exact False.elim hrel
    | some k =>
      have hlt_ct31 : k.ciphertext.length < 2 ^ 32 := hbound
      have hlt_ct63 : k.ciphertext.length < 2 ^ 63 := by omega
      have hlen0_le := encodeVarint_length_le_10 (BitVec.ofNat 64 (encPendingKyber k).length)
      have hlen1_le := uint32Field1_length_le k.preKeyId
      rw [hP]
      refine sepWPp_extract_kyber_some (A := A) (ss := ss) (g := g)
        (h := fun hlen8 _ hcap_g _ => ?_)
      have hopen := optTailVecAt_kyber_some_eq_open A ss g k hlen8 hrel
      rw [hopen]
      refine step_tag14_write_tag_placed hDR ss v sp0 cap ptr g k bs hcap_g (by omega)
        hpc hrun hcl hsp halign htr hx19 hx20 hcs (by sep_focus) ?_
      intro s1 cap1 ptr1 hpc1 hrun1 hcl1 hsp1 htr1 hx19_1 hx20_1 hx22_1 hx21_1 hcs1
      refine step_tag14_len1_placed ss v sp0 k hlt_ct63
        hpc1 hrun1 hcl1 hsp1 htr1 hx19_1 hx20_1 hx22_1 hx21_1 hcs1 ?_
      intro s2 hpc2 hrun2 hcl2 hsp2 htr2 hx19_2 hx20_2 hx8_2 hx22_2 hx21_2 hcs2
      refine step_tag14_len2_placed hEV ss v sp0 cap1 ptr1 g k bs (by omega)
        hpc2 hrun2 hcl2 hsp2 halign htr2 hx19_2 hx20_2 hx8_2 hx22_2 hx21_2 hcs2 (by sep_focus) ?_
      intro s3 cap3 ptr3 hpc3 hrun3 hcl3 hsp3 htr3 hx19_3 hx20_3 hx22_3 hx21_3 hcs3
      refine step_tag14_sub1_placed hEV hDR ss v sp0 cap3 ptr3 g k
        ((bs ++ [0x72#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length))
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc3 hrun3 hcl3 hsp3 halign htr3 hx19_3 hx20_3 hx22_3 hx21_3 hcs3 (by sep_focus) ?_
      intro s4 cap4 ptr4 hpc4 hrun4 hcl4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hcs4
      unfold kyberOpenAt
      refine step_tag14_sub2_placed hDR hEV hmc ss v sp0 g.vec.cap g.vec.ptr cap4 ptr4
        (((bs ++ [0x72#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)) ++
          uint32Field 1 k.preKeyId)
        k.ciphertext
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc4 hrun4 hcl4 hsp4 halign htr4 hx19_4 hx20_4 hx21_4 hcs4 (by sep_focus) ?_
      intro s5 cap5 ptr5 hpc5 hrun5 hcl5 hsp5 htr5 hx19_5 hx20_5 hcs5
      refine SepWPp.weaken_pre ?_ (hnext s5 cap5 ptr5 hpc5 hrun5 hcl5 hsp5 htr5 hx19_5 hx20_5 hcs5)
      rw [hopen]
      unfold kyberOpenAt
      have hbytes :
          ((((bs ++ [0x72#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)) ++
            uint32Field 1 k.preKeyId) ++ bytesField 2 k.ciphertext) =
          bs ++ msgField 14 (Option.map encPendingKyber (some k)) := by
        simp only [Option.map_some, ← msgField14_some_eq k, List.append_assoc]
      rw [hbytes]
      exact entails_of_sep_focus (by sep_focus)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
/-- Relocatable `SessionStructure::encode_raw` (block `14`) contract from callee and `memcpy`
contracts. -/
theorem encodeRaw_placed_ok_of_contracts [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hEV : subroutine_ok (lsProg_10 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hEC : subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_14 H) (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawSpec A)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, G, m, v, cap0, ptr0, bs0⟩ R s0 hpc0 hrun0 hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(withLsCodeLoaded lsmpl (encodeRawSpec A)).pre ⟨ss, G, m, v, cap0, ptr0, bs0⟩ s0, R, hpre, ?_⟩
  dsimp only [withLsCodeLoaded, encodeRawSpec]
  rw [sepConj_comm]
  apply sepWPp_to_panicAllocPost
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hcl0 => ?_
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hfit⟩ => ?_
  refine sepWPp_open_sessionAt fun hpending hkyber hSessEq => ?_
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
  refine step_encraw_prologue_placed ss v s0.sp hpc0 hrun0 hcl0 rfl halign rfl hx0 hx1
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl (by sep_focus) ?_
  intro s1 v56 hpc1 hrun1 hcl1 hsp1 htr1 hx0_1 hx1_1 hx20_1 hcs1
  refine step_encraw_tag1_placed hDR hEV ss v s0.sp cap0 ptr0 m.state.sessionVersion bs0
    (by omega) hpc1 hrun1 hcl1 hsp1 halign htr1 hx0_1 hx1_1 hx20_1 hcs1 (by sep_focus) ?_
  intro s2 cap1 ptr1 hpc2 hrun2 hcl2 hsp2 htr2 hx19_2 hx20_2 hcs2
  refine step_encraw_tag2_placed hDR hEV hmc ss v s0.sp G.localIk.cap G.localIk.ptr cap1 ptr1
    (bs0 ++ uint32Field 1 m.state.sessionVersion) G.localIk.bytes
    (by simp only [List.length_append]; omega)
    hpc2 hrun2 hcl2 hsp2 halign htr2 hx19_2 hx20_2 hcs2 (by sep_focus) ?_
  intro s3 cap2 ptr2 hpc3 hrun3 hcl3 hsp3 htr3 hx19_3 hx20_3 hcs3
  refine step_encraw_tag3_placed hDR hEV hmc ss v s0.sp G.remoteIk.cap G.remoteIk.ptr cap2 ptr2
    ((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) G.remoteIk.bytes
    (by simp only [List.length_append]; omega)
    hpc3 hrun3 hcl3 hsp3 halign htr3 hx19_3 hx20_3 hcs3 (by sep_focus) ?_
  intro s4 cap3 ptr3 hpc4 hrun4 hcl4 hsp4 htr4 hx19_4 hx20_4 hcs4
  refine step_encraw_tag4_placed hDR hEV hmc ss v s0.sp G.root.cap G.root.ptr cap3 ptr3
    (((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes)
    (HMAC.keyToBytes32 m.state.rootKey)
    (by simp only [List.length_append]; omega)
    hpc4 hrun4 hcl4 hsp4 halign htr4 hx19_4 hx20_4 hcs4 (by sep_focus) ?_
  intro s5 cap4 ptr4 hpc5 hrun5 hcl5 hsp5 htr5 hx19_5 hx20_5 hcs5
  refine step_encraw_tag5_placed hDR hEV ss v s0.sp cap4 ptr4 m.state.previousCounter
    ((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey))
    (by simp only [List.length_append]; omega)
    hpc5 hrun5 hcl5 hsp5 halign htr5 hx19_5 hx20_5 hcs5 (by sep_focus) ?_
  intro s6 cap5 ptr5 hpc6 hrun6 hcl6 hsp6 htr6 hx19_6 hx20_6 hcs6
  refine step_encraw_tag6_placed hEC ss v s0.sp cap5 ptr5 G.sender m.state.senderChain
    (((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter)
    (by simp only [List.length_append]; omega)
    hpc6 hrun6 hcl6 hsp6 halign htr6 hx19_6 hx20_6 hcs6 (by sep_focus) ?_
  intro s7 cap6 ptr6 hpc7 hrun7 hcl7 hsp7 htr7 hx19_7 hx20_7 hcs7
  refine step_encraw_tag7_placed hEC ss v s0.sp G.chainsCap G.chainsPtr cap6 ptr6
    (G.chains.zip m.state.receiverChains)
    ((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain)
    (by simp only [List.length_append]; omega)
    hpc7 hrun7 hcl7 hsp7 halign htr7 hx19_7 hx20_7 hcs7 (by sep_focus) ?_
  intro s8 cap7 ptr7 hpc8 hrun8 hcl8 hsp8 htr8 hx19_8 hx20_8 hcs8
  refine step_encraw_tag9_placed hEV hDR hmc ss v s0.sp cap7 ptr7 G.pending m.pendingPreKey
    (((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten)
    hpending
    (by revert hpending; cases h : G.pending with
        | none => intro _; trivial
        | some g => intro _; exact hpend_bound g h)
    (by simp only [List.length_append]; omega)
    hpc8 hrun8 hcl8 hsp8 halign htr8 hx19_8 hx20_8 hcs8 (by sep_focus) ?_
  intro s9 cap8 ptr8 hpc9 hrun9 hcl9 hsp9 htr9 hx19_9 hx20_9 hcs9
  refine step_encraw_tag10_placed hDR hEV ss v s0.sp cap8 ptr8 m.remoteRegistrationId
    ((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey)
    (by simp only [List.length_append]; omega)
    hpc9 hrun9 hcl9 hsp9 halign htr9 hx19_9 hx20_9 hcs9 (by sep_focus) ?_
  intro s10 cap9 ptr9 hpc10 hrun10 hcl10 hsp10 htr10 hx19_10 hx20_10 hcs10
  refine step_encraw_tag11_placed hDR hEV ss v s0.sp cap9 ptr9 m.localRegistrationId
    (((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey) ++
      uint32Field 10 m.remoteRegistrationId)
    (by simp only [List.length_append]; omega)
    hpc10 hrun10 hcl10 hsp10 halign htr10 hx19_10 hx20_10 hcs10 (by sep_focus) ?_
  intro s11 cap10 ptr10 hpc11 hrun11 hcl11 hsp11 htr11 hx19_11 hx20_11 hcs11
  refine step_encraw_tag13_placed hDR hEV hmc ss v s0.sp G.alice.cap G.alice.ptr cap10 ptr10
    ((((((((((bs0 ++ uint32Field 1 m.state.sessionVersion) ++ bytesField 2 G.localIk.bytes) ++
      bytesField 3 G.remoteIk.bytes) ++ bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)) ++
      uint32Field 5 m.state.previousCounter) ++ encSenderFieldMem G.sender m.state.senderChain) ++
      ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten) ++
      encPendingFieldMem G.pending m.pendingPreKey) ++
      uint32Field 10 m.remoteRegistrationId) ++
      uint32Field 11 m.localRegistrationId)
    m.aliceBaseKey
    (by simp only [List.length_append]; omega)
    hpc11 hrun11 hcl11 hsp11 halign htr11 hx19_11 hx20_11 hcs11 (by sep_focus) ?_
  intro s12 cap11 ptr11 hpc12 hrun12 hcl12 hsp12 htr12 hx19_12 hx20_12 hcs12
  refine step_encraw_tag14_placed hEV hDR hmc ss v s0.sp cap11 ptr11 G.kyber m.pendingKyberPreKey
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
    hpc12 hrun12 hcl12 hsp12 halign htr12 hx19_12 hx20_12 hcs12 (by sep_focus) ?_
  intro s13 cap12 ptr12 hpc13 hrun13 hcl13 hsp13 htr13 hx19_13 hx20_13 hcs13
  refine step_encraw_tag15_placed hDR hEV hmc ss v s0.sp G.pq.cap G.pq.ptr cap12 ptr12
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
    hpc13 hrun13 hcl13 hsp13 halign htr13 hx19_13 hx20_13 hcs13 (by sep_focus) ?_
  intro s14 cap13 ptr13 hpc14 hrun14 hcl14 hsp14 htr14 hcs14
  refine step_encraw_epilogue_placed s0.sp v56
    hpc14 hrun14 hcl14 hsp14 halign htr14 rfl hcs14 (by sep_focus) ?_
  intro sm hpcm hrunm _hclm hspm htrm hcsm
  apply SepWPp.done hpcm hrunm
  refine ⟨fun hm => ?_, hspm, hcsm⟩
  rw [show (⌜sm.trace = s0.trace⌝ ∗
        sessionStateReprAt A ss G m ∗
          (∃∗ cap', ∃∗ ptr', vecU8At A v cap' ptr' (bs0 ++ encSessionMem G m)) ∗
            A.pool ∗ stackAt s0.sp encodeRawStack ∗ R) =
      (⌜sm.trace = s0.trace⌝ ∗
        sessionStateReprAt A ss G m ∗
          (∃∗ cap', ∃∗ ptr', vecU8At A v cap' ptr' (bs0 ++ encSessionMem G m)) ∗
            A.pool ∗ stackAt s0.sp encodeRawStack) ∗ R by simp only [sepConj_assoc]]
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
      (vecU8At A v cap13 ptr13 (bs0 ++ encSessionMem G m) ∗ A.pool ∗ stackAt s0.sp encodeRawStack))
    ?_
    (sepConj_mono_right (sepConj_mono_left (vecU8At_entails_exists_er A v cap13 ptr13 _)))
  unfold sessionRawOpen
  exact entails_of_sep_focus (by sep_focus)

/-- Relocatable `SessionStructure::encode_raw` (block `14`) contract from primitive hook hypotheses. -/
theorem encodeRaw_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_14 H) (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawSpec A)) :=
  encodeRaw_placed_ok_of_contracts A H
    (encode_varint_placed_ok hshim halloc hrealloc hpanic)
    (do_reserve_placed_ok hshim halloc hrealloc hpanic)
    (encodeChain_placed_ok hshim halloc hrealloc hmc hpanic)
    hmc

/-- Relocatable `SessionStructure::encode_raw` (block `14`) contract from `PlacedSerializeHooks`. -/
theorem encodeRaw_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hH : PlacedSerializeHooks A H) :
    subroutine_ok (lsProg_14 H) (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawSpec A)) :=
  encodeRaw_placed_ok hH.shim hH.alloc hH.realloc hH.memcpy hH.panic_handle_error

end Placed

end CryptoVerification.E2E.Record.Serialization
