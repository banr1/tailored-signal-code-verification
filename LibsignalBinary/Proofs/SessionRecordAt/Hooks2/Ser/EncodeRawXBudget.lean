/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.MessageKeyLoopXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingKyberPreKeyXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXBPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PqRatchetStateEpilogueXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RegistrationIdsBaseKeyXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RemoteIdentityRootKeyCounterXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SenderReceiverChainsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRawX
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<SessionStructure as prost::Message>::encode_raw::<Vec<u8>>` (Block `14`)

Assembles all budget-threaded segment proofs to establish `EncodeRawPlacedOkX M A lim H` for
Block `14` (`SessionStructure::encode_raw`) at `encodeRawStackX` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRawXBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSessionApi (Session PendingPreKey PendingKyberPreKey)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl withLsCodeLoaded withLsCl
)
open CryptoVerification.RustHeap (RustAlloc vecU8At vecAt)
open CryptoVerification.LibsignalSessionRepr (chainAt vecGhostAt leBytes)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost TailVecGhost sessionStateAt optSenderChainAt optTailVecAt
)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.E2E.Record (
  uint32Field bytesField msgField lenField encPendingKyber PendingRel KyberRel
)
open CryptoVerification.E2E.Record.Placed (blkPl_14 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  EncodeRawGhost encChainMem encSenderFieldMem encPendingMem encPendingFieldMem encSessionMem
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus pointsToBytes_regIds_eq
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (EncodeRawEnv)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_append fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  encodeRawStackX SerContractsXPlaced encodeRawSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  EncodeVarintPlacedOkX DoReservePlacedOkX EncodeChainPlacedOkX EncodeRawPlacedOkX
  subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.MessageKeyLoopXBudget (
  EncodeChainSegPlacedOkX encodeChain_seg_placed_ok
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlacedBudget (
  step_encraw_prologue_placed_x step_encraw_tag1_placed_x step_encraw_tag2_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RemoteIdentityRootKeyCounterXPlacedBudget (
  step_encraw_tag3_placed_x step_encraw_tag4_placed_x step_encraw_tag5_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SenderReceiverChainsXBudget (
  step_encraw_tag6_placed_x step_encraw_tag7_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXBPlacedBudget (
  step_encraw_tag9_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RegistrationIdsBaseKeyXPlacedBudget (
  step_encraw_tag10_placed_x step_encraw_tag11_placed_x step_encraw_tag13_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingKyberPreKeyXPlacedBudget (
  step_encraw_tag14_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PqRatchetStateEpilogueXBudget (
  step_encraw_tag15_placed_x step_encraw_epilogue_placed_x
)

/-! ## Session opening and length helpers -/

private def sessionRawOpen (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (m : Session (List (BitVec 8))) : SepProp :=
  vecU8At A ss G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
  vecU8At A (ss + 24#64) G.remoteIk.cap G.remoteIk.ptr G.remoteIk.bytes ∗
  vecU8At A (ss + 48#64) G.root.cap G.root.ptr (keyToBytes32 m.state.rootKey) ∗
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
      vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 m.state.rootKey) ∗
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
  exact Entails.of_eq (by rw [← hbody]; sep_ac_rfl)

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

private theorem encRawSegEnv_sub_encodeRawEnv (x : EncodeRawGhost) {evs : List AllocEvent}
    (h : EncRawSegEnv x.bs.length (encSessionMem x.G x.s).length evs) :
    EncodeRawEnv x evs := by
  unfold EncRawSegEnv EncodeRawEnv at *
  dsimp only at *
  exact h.mono (by omega) (Nat.le_max_right _ _)

/-! ## Top-level Block `14` (`SessionStructure::encode_raw`) contracts -/

/-- Block `14` (`SessionStructure::encode_raw`) at `encodeRawStackX` under `[LibsignalPlacement]`,
    given `EncodeChainSegPlacedOkX M A lim H` for tags `6` and `7`. -/
theorem encodeRaw_placed_ok_of_seg_ext [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (hEC : EncodeChainSegPlacedOkX M A lim H) :
    EncodeRawPlacedOkX M A lim H := by
  apply subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
  rintro ⟨⟨ss, G, m, v, cap0, ptr0, bs0⟩, st0⟩ R s0 hpc0 hrun0 hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(encodeRawSpecX M A lim).pre (⟨ss, G, m, v, cap0, ptr0, bs0⟩, st0) s0, R, hpre, ?_⟩
  dsimp only [encodeRawSpecX]
  refine SepWPpLsCl.pure_elim fun ⟨hx0, hx1, hfit, hfitEnv⟩ => ?_
  refine sepWPpLsCl_open_sessionAt fun hpending hkyber hSessEq => ?_
  let f1 := uint32Field 1 m.state.sessionVersion
  let f2 := bytesField 2 G.localIk.bytes
  let f3 := bytesField 3 G.remoteIk.bytes
  let f4 := bytesField 4 (keyToBytes32 m.state.rootKey)
  let f5 := uint32Field 5 m.state.previousCounter
  let f6 := encSenderFieldMem G.sender m.state.senderChain
  let f7 := ((G.chains.zip m.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten
  let f9 := encPendingFieldMem G.pending m.pendingPreKey
  let f10 := uint32Field 10 m.remoteRegistrationId
  let f11 := uint32Field 11 m.localRegistrationId
  let f13 := bytesField 13 m.aliceBaseKey
  let f14 := msgField 14 (m.pendingKyberPreKey.map encPendingKyber)
  let f15 := bytesField 15 m.state.pqRatchetState
  have hlik_le : G.localIk.bytes.length ≤ f2.length := length_le_bytesField_length_er 2 G.localIk.bytes
  have hrik_le : G.remoteIk.bytes.length ≤ f3.length := length_le_bytesField_length_er 3 G.remoteIk.bytes
  have hroot_le : (keyToBytes32 m.state.rootKey).length ≤ f4.length :=
    length_le_bytesField_length_er 4 (keyToBytes32 m.state.rootKey)
  have halice_le : m.aliceBaseKey.length ≤ f13.length := length_le_bytesField_length_er 13 m.aliceBaseKey
  have hpq_le : m.state.pqRatchetState.length ≤ f15.length :=
    length_le_bytesField_length_er 15 m.state.pqRatchetState
  let R12 := f15.length
  let R11 := f14.length + R12
  let R10 := f13.length + R11
  let R9 := f11.length + R10
  let R8 := f10.length + R9
  let R7 := f9.length + R8
  let R6 := f7.length + R7
  let R5 := f6.length + R6
  let R4 := f5.length + R5
  let R3 := f4.length + R4
  let R2 := f3.length + R3
  let R1 := f2.length + R2
  let R0 := f1.length + R1
  have henc_len : (encSessionMem G m).length = R0 := by
    simp only [encSessionMem, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12,
      f1, f2, f3, f4, f5, f6, f7, f9, f10, f11, f13, f14, f15, List.length_append]
    omega
  have hfit_expand :
      bs0.length +
      (f1.length + f2.length + f3.length + f4.length + f5.length + f6.length +
       f7.length + f9.length + f10.length + f11.length + f13.length + f14.length + f15.length) < 2 ^ 32 := by
    simpa only [encSessionMem, f1, f2, f3, f4, f5, f6, f7, f9, f10, f11, f13, f14, f15,
      List.length_append, Nat.add_assoc] using hfit
  have hpend_bound := pending_vec_length_lt_er G.pending m.pendingPreKey hpending
    (by dsimp only [f9] at hfit_expand; omega)
  have hkyber_bound := kyber_ct_length_lt_er m.pendingKyberPreKey
    (by dsimp only [f14] at hfit_expand; omega)
  have hfit0 : FitsEnv M lim st0 (EncRawSegEnv bs0.length R0) := by
    rw [← henc_len]
    exact fun evs he => hfitEnv evs (encRawSegEnv_sub_encodeRawEnv ⟨ss, G, m, v, cap0, ptr0, bs0⟩ he)
  unfold sessionRawOpen
  simp only [sepConj_assoc]
  refine step_encraw_prologue_placed_x H ss v s0.sp hpc0 hrun0 rfl halign rfl hx0 hx1
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl (by sep_focus) ?_
  intro s1 v56 hvm0 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx20_1 hcs1
  rw [← A.pool_of_vmPreserved (lim := lim) (st := st0) hvm0]
  refine step_encraw_tag1_placed_x hDR hEV ss v s0.sp cap0 ptr0 m.state.sessionVersion bs0 st0
    (by omega) (fitsEnv_encRawSeg_left hfit0)
    hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx20_1 hcs1 (by sep_focus) ?_
  intro s2 cap1 ptr1 evs1 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hevs1
  let bs1 := bs0 ++ f1
  let st1 := M.stepEvents evs1 st0
  have hbs1_len : bs1.length = bs0.length + f1.length := List.length_append
  have hfit1 : FitsEnv M lim st1 (EncRawSegEnv bs1.length R1) := by
    rw [hbs1_len]; exact fitsEnv_encRawSeg_right hfit0 hevs1
  refine step_encraw_tag2_placed_x hDR hEV hC ss v s0.sp G.localIk.cap G.localIk.ptr cap1 ptr1
    bs1 G.localIk.bytes st1
    (by rw [hbs1_len]; omega) (fitsEnv_encRawSeg_left hfit1)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2 (by sep_focus) ?_
  intro s3 cap2 ptr2 evs2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 hevs2
  let bs2 := bs1 ++ f2
  let st2 := M.stepEvents evs2 st1
  have hbs2_len : bs2.length = bs1.length + f2.length := List.length_append
  have hfit2 : FitsEnv M lim st2 (EncRawSegEnv bs2.length R2) := by
    rw [hbs2_len]; exact fitsEnv_encRawSeg_right hfit1 hevs2
  refine step_encraw_tag3_placed_x hC hDR hEV ss v s0.sp G.remoteIk.cap G.remoteIk.ptr cap2 ptr2
    bs2 G.remoteIk.bytes st2
    (by rw [hbs2_len, hbs1_len]; omega) (fitsEnv_encRawSeg_left hfit2)
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3 (by sep_focus) ?_
  intro s4 cap3 ptr3 evs3 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 hevs3
  let bs3 := bs2 ++ f3
  let st3 := M.stepEvents evs3 st2
  have hbs3_len : bs3.length = bs2.length + f3.length := List.length_append
  have hfit3 : FitsEnv M lim st3 (EncRawSegEnv bs3.length R3) := by
    rw [hbs3_len]; exact fitsEnv_encRawSeg_right hfit2 hevs3
  refine step_encraw_tag4_placed_x hC hDR hEV ss v s0.sp G.root.cap G.root.ptr cap3 ptr3
    bs3 (keyToBytes32 m.state.rootKey) st3
    (by rw [hbs3_len, hbs2_len, hbs1_len]; omega) (fitsEnv_encRawSeg_left hfit3)
    hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hcs4 (by sep_focus) ?_
  intro s5 cap4 ptr4 evs4 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hcs5 hevs4
  let bs4 := bs3 ++ f4
  let st4 := M.stepEvents evs4 st3
  have hbs4_len : bs4.length = bs3.length + f4.length := List.length_append
  have hfit4 : FitsEnv M lim st4 (EncRawSegEnv bs4.length R4) := by
    rw [hbs4_len]; exact fitsEnv_encRawSeg_right hfit3 hevs4
  refine step_encraw_tag5_placed_x hDR hEV ss v s0.sp cap4 ptr4 m.state.previousCounter
    bs4 st4
    (by rw [hbs4_len, hbs3_len, hbs2_len, hbs1_len]; omega) (fitsEnv_encRawSeg_left hfit4)
    hpc5 hrun5 hsp5 halign htr5 hx19_5 hx20_5 hcs5 (by sep_focus) ?_
  intro s6 cap5 ptr5 evs5 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6 hevs5
  let bs5 := bs4 ++ f5
  let st5 := M.stepEvents evs5 st4
  have hbs5_len : bs5.length = bs4.length + f5.length := List.length_append
  have hfit5 : FitsEnv M lim st5 (EncRawSegEnv bs5.length R5) := by
    rw [hbs5_len]; exact fitsEnv_encRawSeg_right hfit4 hevs5
  refine step_encraw_tag6_placed_x hEC ss v s0.sp cap5 ptr5 G.sender m.state.senderChain
    bs5 st5
    (by rw [hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len]; dsimp only [f6] at hfit_expand; omega)
    (fitsEnv_encRawSeg_left hfit5)
    hpc6 hrun6 hsp6 halign htr6 hx19_6 hx20_6 hcs6 (by sep_focus) ?_
  intro s7 cap6 ptr6 evs6 hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hcs7 hevs6
  let bs6 := bs5 ++ f6
  let st6 := M.stepEvents evs6 st5
  have hbs6_len : bs6.length = bs5.length + f6.length := List.length_append
  have hfit6 : FitsEnv M lim st6 (EncRawSegEnv bs6.length R6) := by
    rw [hbs6_len]; exact fitsEnv_encRawSeg_right hfit5 hevs6
  refine step_encraw_tag7_placed_x hEC ss v s0.sp G.chainsCap G.chainsPtr cap6 ptr6
    (G.chains.zip m.state.receiverChains) bs6 st6
    (by rw [hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len]; dsimp only [f7] at hfit_expand; omega)
    (fitsEnv_encRawSeg_left hfit6)
    hpc7 hrun7 hsp7 halign htr7 hx19_7 hx20_7 hcs7 (by sep_focus) ?_
  intro s8 cap7 ptr7 evs7 hpc8 hrun8 hsp8 htr8 hx19_8 hx20_8 hcs8 hevs7
  let bs7 := bs6 ++ f7
  let st7 := M.stepEvents evs7 st6
  have hbs7_len : bs7.length = bs6.length + f7.length := List.length_append
  have hfit7 : FitsEnv M lim st7 (EncRawSegEnv bs7.length R7) := by
    rw [hbs7_len]; exact fitsEnv_encRawSeg_right hfit6 hevs7
  refine step_encraw_tag9_placed_x hC hEV hDR ss v s0.sp cap7 ptr7 G.pending m.pendingPreKey
    bs7 st7 hpending
    (by revert hpending; cases h : G.pending with
        | none => intro _; trivial
        | some g => intro _; exact hpend_bound g h)
    (by rw [hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len];
        dsimp only [f9] at hfit_expand; omega)
    (fitsEnv_encRawSeg_left hfit7)
    hpc8 hrun8 hsp8 halign htr8 hx19_8 hx20_8 hcs8 (by sep_focus) ?_
  intro s9 cap8 ptr8 evs8 hpc9 hrun9 hsp9 htr9 hx19_9 hx20_9 hcs9 hevs8
  let bs8 := bs7 ++ f9
  let st8 := M.stepEvents evs8 st7
  have hbs8_len : bs8.length = bs7.length + f9.length := List.length_append
  have hfit8 : FitsEnv M lim st8 (EncRawSegEnv bs8.length R8) := by
    rw [hbs8_len]; exact fitsEnv_encRawSeg_right hfit7 hevs8
  refine step_encraw_tag10_placed_x hDR hEV ss v s0.sp cap8 ptr8 m.remoteRegistrationId
    bs8 st8
    (by rw [hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len]; omega)
    (fitsEnv_encRawSeg_left hfit8)
    hpc9 hrun9 hsp9 halign htr9 hx19_9 hx20_9 hcs9 (by sep_focus) ?_
  intro s10 cap9 ptr9 evs9 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10 hevs9
  let bs9 := bs8 ++ f10
  let st9 := M.stepEvents evs9 st8
  have hbs9_len : bs9.length = bs8.length + f10.length := List.length_append
  have hfit9 : FitsEnv M lim st9 (EncRawSegEnv bs9.length R9) := by
    rw [hbs9_len]; exact fitsEnv_encRawSeg_right hfit8 hevs9
  refine step_encraw_tag11_placed_x hDR hEV ss v s0.sp cap9 ptr9 m.localRegistrationId
    bs9 st9
    (by rw [hbs9_len, hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len]; omega)
    (fitsEnv_encRawSeg_left hfit9)
    hpc10 hrun10 hsp10 halign htr10 hx19_10 hx20_10 hcs10 (by sep_focus) ?_
  intro s11 cap10 ptr10 evs10 hpc11 hrun11 hsp11 htr11 hx19_11 hx20_11 hcs11 hevs10
  let bs10 := bs9 ++ f11
  let st10 := M.stepEvents evs10 st9
  have hbs10_len : bs10.length = bs9.length + f11.length := List.length_append
  have hfit10 : FitsEnv M lim st10 (EncRawSegEnv bs10.length R10) := by
    rw [hbs10_len]; exact fitsEnv_encRawSeg_right hfit9 hevs10
  refine step_encraw_tag13_placed_x hDR hEV hC ss v s0.sp G.alice.cap G.alice.ptr cap10 ptr10
    bs10 m.aliceBaseKey st10
    (by rw [hbs10_len, hbs9_len, hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len];
        omega)
    (fitsEnv_encRawSeg_left hfit10)
    hpc11 hrun11 hsp11 halign htr11 hx19_11 hx20_11 hcs11 (by sep_focus) ?_
  intro s12 cap11 ptr11 evs11 hpc12 hrun12 hsp12 htr12 hx19_12 hx20_12 hcs12 hevs11
  let bs11 := bs10 ++ f13
  let st11 := M.stepEvents evs11 st10
  have hbs11_len : bs11.length = bs10.length + f13.length := List.length_append
  have hfit11 : FitsEnv M lim st11 (EncRawSegEnv bs11.length R11) := by
    rw [hbs11_len]; exact fitsEnv_encRawSeg_right hfit10 hevs11
  refine step_encraw_tag14_placed_x hDR hEV hC ss v s0.sp cap11 ptr11 G.kyber m.pendingKyberPreKey
    bs11 st11 hkyber
    (by revert hkyber; cases h : m.pendingKyberPreKey with
        | none => intro _; trivial
        | some k => intro _; exact hkyber_bound k h)
    (by rw [hbs11_len, hbs10_len, hbs9_len, hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len,
            hbs2_len, hbs1_len];
        dsimp only [f14] at hfit_expand; omega)
    (fitsEnv_encRawSeg_left hfit11)
    hpc12 hrun12 hsp12 halign htr12 hx19_12 hx20_12 hcs12 (by sep_focus) ?_
  intro s13 cap12 ptr12 evs12 hpc13 hrun13 hsp13 htr13 hx19_13 hx20_13 hcs13 hevs12
  let bs12 := bs11 ++ f14
  let st12 := M.stepEvents evs12 st11
  have hbs12_len : bs12.length = bs11.length + f14.length := List.length_append
  have hfit12 : FitsEnv M lim st12 (EncRawSegEnv bs12.length f15.length) := by
    rw [hbs12_len]; exact fitsEnv_encRawSeg_right hfit11 hevs12
  refine step_encraw_tag15_placed_x hDR hEV hC ss v s0.sp G.pq.cap G.pq.ptr cap12 ptr12
    bs12 m.state.pqRatchetState st12
    (by rw [hbs12_len, hbs11_len, hbs10_len, hbs9_len, hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len,
            hbs3_len, hbs2_len, hbs1_len];
        omega)
    hfit12
    hpc13 hrun13 hsp13 halign htr13 hx19_13 hx20_13 hcs13 (by sep_focus) ?_
  intro s14 cap13 ptr13 evs13 hpc14 hrun14 hsp14 htr14 hcs14 hevs13
  let st13 := M.stepEvents evs13 st12
  refine step_encraw_epilogue_placed_x (H := H) s0.sp v56
    hpc14 hrun14 hsp14 halign htr14 rfl hcs14 (by sep_focus) ?_
  intro sm hvm_ep hpcm hrunm hspm htrm hcsm
  rw [← A.pool_of_vmPreserved (lim := lim) (st := st13) hvm_ep]
  apply SepWPpLsCl.done hpcm hrunm
  refine ⟨fun hm => ?_, hspm, hcsm⟩
  let evs_tot :=
    evs1 ++ (evs2 ++ (evs3 ++ (evs4 ++ (evs5 ++ (evs6 ++
      (evs7 ++ (evs8 ++ (evs9 ++ (evs10 ++ (evs11 ++ (evs12 ++ evs13)))))))))))
  have hst_tot : st13 = M.stepEvents evs_tot st0 := by
    simp only [st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1,
      evs_tot, M.stepEvents_append]
  have he12_13 : EncRawSegEnv bs11.length R11 (evs12 ++ evs13) :=
    encRawSegEnv_append hevs12 (hbs12_len ▸ hevs13)
  have he11_13 : EncRawSegEnv bs10.length R10 (evs11 ++ (evs12 ++ evs13)) :=
    encRawSegEnv_append hevs11 (hbs11_len ▸ he12_13)
  have he10_13 : EncRawSegEnv bs9.length R9 (evs10 ++ (evs11 ++ (evs12 ++ evs13))) :=
    encRawSegEnv_append hevs10 (hbs10_len ▸ he11_13)
  have he9_13 : EncRawSegEnv bs8.length R8 (evs9 ++ (evs10 ++ (evs11 ++ (evs12 ++ evs13)))) :=
    encRawSegEnv_append hevs9 (hbs9_len ▸ he10_13)
  have he8_13 : EncRawSegEnv bs7.length R7
      (evs8 ++ (evs9 ++ (evs10 ++ (evs11 ++ (evs12 ++ evs13))))) :=
    encRawSegEnv_append hevs8 (hbs8_len ▸ he9_13)
  have he7_13 : EncRawSegEnv bs6.length R6
      (evs7 ++ (evs8 ++ (evs9 ++ (evs10 ++ (evs11 ++ (evs12 ++ evs13)))))) :=
    encRawSegEnv_append hevs7 (hbs7_len ▸ he8_13)
  have he6_13 : EncRawSegEnv bs5.length R5
      (evs6 ++ (evs7 ++ (evs8 ++ (evs9 ++ (evs10 ++ (evs11 ++ (evs12 ++ evs13))))))) :=
    encRawSegEnv_append hevs6 (hbs6_len ▸ he7_13)
  have he5_13 : EncRawSegEnv bs4.length R4
      (evs5 ++ (evs6 ++ (evs7 ++ (evs8 ++ (evs9 ++ (evs10 ++ (evs11 ++ (evs12 ++ evs13)))))))) :=
    encRawSegEnv_append hevs5 (hbs5_len ▸ he6_13)
  have he4_13 : EncRawSegEnv bs3.length R3
      (evs4 ++ (evs5 ++ (evs6 ++ (evs7 ++ (evs8 ++ (evs9 ++ (evs10 ++ (evs11 ++ (evs12 ++ evs13))))))))) :=
    encRawSegEnv_append hevs4 (hbs4_len ▸ he5_13)
  have he3_13 : EncRawSegEnv bs2.length R2
      (evs3 ++ (evs4 ++ (evs5 ++ (evs6 ++ (evs7 ++ (evs8 ++ (evs9 ++ (evs10 ++ (evs11 ++ (evs12 ++ evs13)))))))))) :=
    encRawSegEnv_append hevs3 (hbs3_len ▸ he4_13)
  have he2_13 : EncRawSegEnv bs1.length R1
      (evs2 ++ (evs3 ++ (evs4 ++ (evs5 ++ (evs6 ++ (evs7 ++ (evs8 ++ (evs9 ++ (evs10 ++ (evs11 ++ (evs12 ++ evs13))))))))))) :=
    encRawSegEnv_append hevs2 (hbs2_len ▸ he3_13)
  have hevs_seg : EncRawSegEnv bs0.length R0 evs_tot :=
    encRawSegEnv_append hevs1 (hbs1_len ▸ he2_13)
  have hevs_env : EncodeRawEnv ⟨ss, G, m, v, cap0, ptr0, bs0⟩ evs_tot := by
    rw [← henc_len] at hevs_seg
    exact encRawSegEnv_sub_encodeRawEnv ⟨ss, G, m, v, cap0, ptr0, bs0⟩ hevs_seg
  have hbytes :
      bs12 ++ f15 = bs0 ++ encSessionMem G m := by
    simp only [bs12, bs11, bs10, bs9, bs8, bs7, bs6, bs5, bs4, bs3, bs2, bs1,
      f1, f2, f3, f4, f5, f6, f7, f9, f10, f11, f13, f14, f15,
      encSessionMem, List.append_assoc]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs_tot, ?_⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨htrm, hevs_env⟩, ?_⟩
  rw [show (sessionStateReprAt A.repAlloc ss G m ∗
        (∃∗ cap', ∃∗ ptr', vecU8At A.repAlloc v cap' ptr' (bs0 ++ encSessionMem G m)) ∗
        A.pool lim (M.stepEvents evs_tot st0) sm ∗ stackAt s0.sp encodeRawStackX ∗ R) =
      (sessionStateReprAt A.repAlloc ss G m ∗
        (∃∗ cap', ∃∗ ptr', vecU8At A.repAlloc v cap' ptr' (bs0 ++ encSessionMem G m)) ∗
        A.pool lim (M.stepEvents evs_tot st0) sm ∗ stackAt s0.sp encodeRawStackX) ∗ R by
    simp only [sepConj_assoc]]
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  rw [hSessEq, hbytes, hst_tot]
  refine Entails.trans
    (Q := sessionRawOpen A.repAlloc ss G m ∗
      (vecU8At A.repAlloc v cap13 ptr13 (bs0 ++ encSessionMem G m) ∗
        A.pool lim (M.stepEvents evs_tot st0) sm ∗ stackAt s0.sp encodeRawStackX))
    ?_
    (sepConj_mono_right (sepConj_mono_left (vecU8At_entails_exists_er A.repAlloc v cap13 ptr13 _)))
  unfold sessionRawOpen
  exact Entails.of_eq (by sep_ac_rfl)

/-- Block `14` (`SessionStructure::encode_raw`) at `encodeRawStackX` under `[LibsignalPlacement]`,
    instantiating `encodeChain_seg_placed_ok` from `(hC, hEV, hDR)`. -/
theorem encodeRaw_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H) :
    EncodeRawPlacedOkX M A lim H :=
  encodeRaw_placed_ok_of_seg_ext A lim H hC hEV hDR (encodeChain_seg_placed_ok A lim H hC hEV hDR)

/-- Block `14` (`SessionStructure::encode_raw`) at `encodeRawStackX` under `[LibsignalPlacement]`. -/
theorem encodeRaw_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (_hEC : EncodeChainPlacedOkX M A lim H) :
    EncodeRawPlacedOkX M A lim H :=
  encodeRaw_placed_ok_of_contracts A lim H hC hEV hDR

theorem encodeRaw_placed_ok_cl [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (hEC : EncodeChainPlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 14)
      (withLsCl lsmpl (encodeRawSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeRaw_placed_ok_ext A lim H hC hEV hDR hEC)

theorem encodeRaw_placed_cl_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 14)
      (withLsCl lsmpl (encodeRawSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeRaw_placed_ok_of_contracts A lim H hC hEV hDR)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRawXBudget
