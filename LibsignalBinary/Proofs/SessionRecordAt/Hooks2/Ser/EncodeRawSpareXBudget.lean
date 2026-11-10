/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareBaseXBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareChainsXBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SparePendingPreKeyXPlacedBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareTags1To5XPlacedBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareTailTagsXPlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Pre-Reserved `<SessionStructure as prost::Message>::encode_raw::<Vec<u8>>` (Block `14`)

Assembles all pre-reserved segment steppers to prove the zero-allocation (`VmPreserved`-preserving)
Block `14` contract `EncodeRawPreallocPlacedOkX A.repAlloc H` at `encodeRawStackX` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRawSpareXBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSessionApi (Session PendingPreKey PendingKyberPreKey)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl withLsCl
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
open CryptoVerification.E2E.Record.Serialization (
  encChainMem encSenderFieldMem encPendingMem encPendingFieldMem encSessionMem
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  pointsToBytes_regIds_eq
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (VmPreserved AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (
  encodeRawPreallocSpecX EncodeRawPreallocPlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  encodeRawStackX SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareBaseXBudget (
  EncodeChainPreallocPlacedOkX'
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareTags1To5XPlacedBudget (
  step_encraw_prologue_placed_x
  step_encraw_tag1_prealloc_placed_x
  step_encraw_tag2_prealloc_placed_x
  step_encraw_tag3_prealloc_placed_x
  step_encraw_tag4_prealloc_placed_x
  step_encraw_tag5_prealloc_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareChainsXBudget (
  step_encraw_tag6_prealloc_placed_x
  step_encraw_tag7_prealloc_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SparePendingPreKeyXPlacedBudget (
  step_encraw_tag9_prealloc_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareTailTagsXPlacedBudget (
  step_encraw_tag10_prealloc_placed_x
  step_encraw_tag11_prealloc_placed_x
  step_encraw_tag13_prealloc_placed_x
  step_encraw_tag14_prealloc_placed_x
  step_encraw_tag15_prealloc_placed_x
  step_encraw_epilogue_placed_x
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

/-! ## Top-level pre-reserved Block `14` contract -/

/-- Block `14` (`SessionStructure::encode_raw`) satisfies the pre-reserved `0`-allocation
    `VmPreserved` contract `EncodeRawPreallocPlacedOkX A.repAlloc H` at `encodeRawStackX`
    under `[LibsignalPlacement]`, given `SerContractsXPlaced M A lim H` and
    `EncodeChainPreallocPlacedOkX' A.repAlloc H`. -/
theorem encodeRawPrealloc_placed_ok_of_chain [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hEC : EncodeChainPreallocPlacedOkX' A.repAlloc H) :
    EncodeRawPreallocPlacedOkX A.repAlloc H := by
  apply subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
  rintro ⟨ss, G, m, v, cap0, ptr0, bs0⟩ R s0 hpc0 hrun0 hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(encodeRawPreallocSpecX A.repAlloc).pre ⟨ss, G, m, v, cap0, ptr0, bs0⟩ s0, R, hpre, ?_⟩
  dsimp only [encodeRawPreallocSpecX]
  refine SepWPpLsCl.pure_elim fun ⟨hx0, hx1, hspare, hfit⟩ => ?_
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
  have hpq_le : m.state.pqRatchetState.length ≤ f15.length :=
    length_le_bytesField_length_er 15 m.state.pqRatchetState
  have hspare_expand :
      bs0.length +
      (f1.length + f2.length + f3.length + f4.length + f5.length + f6.length +
       f7.length + f9.length + f10.length + f11.length + f13.length + f14.length + f15.length) ≤
        cap0.toNat := by
    simpa only [encSessionMem, f1, f2, f3, f4, f5, f6, f7, f9, f10, f11, f13, f14, f15,
      List.length_append, Nat.add_assoc] using hspare
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
  unfold sessionRawOpen
  simp only [sepConj_assoc]
  refine step_encraw_prologue_placed_x H ss v s0.sp hpc0 hrun0 rfl halign rfl hx0 hx1
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl (by sep_focus) ?_
  intro s1 v56 hvm0 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx20_1 hcs1
  refine step_encraw_tag1_prealloc_placed_x A ss v s0.sp cap0 ptr0 m.state.sessionVersion bs0
    (by dsimp only [f1] at hspare_expand; omega) (by dsimp only [f1] at hfit_expand; omega)
    hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx20_1 hcs1 (by sep_focus) ?_
  intro s2 hvm1 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
  let bs1 := bs0 ++ f1
  have hbs1_len : bs1.length = bs0.length + f1.length := List.length_append
  refine step_encraw_tag2_prealloc_placed_x hC ss v s0.sp G.localIk.cap G.localIk.ptr cap0 ptr0
    bs1 G.localIk.bytes
    (by rw [hbs1_len]; dsimp only [f2] at hspare_expand; omega)
    (by rw [hbs1_len]; dsimp only [f2] at hfit_expand; omega)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2 (by sep_focus) ?_
  intro s3 hvm2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
  let bs2 := bs1 ++ f2
  have hbs2_len : bs2.length = bs1.length + f2.length := List.length_append
  refine step_encraw_tag3_prealloc_placed_x hC ss v s0.sp G.remoteIk.cap G.remoteIk.ptr cap0 ptr0
    bs2 G.remoteIk.bytes
    (by rw [hbs2_len, hbs1_len]; dsimp only [f3] at hspare_expand; omega)
    (by rw [hbs2_len, hbs1_len]; dsimp only [f3] at hfit_expand; omega)
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3 (by sep_focus) ?_
  intro s4 hvm3 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4
  let bs3 := bs2 ++ f3
  have hbs3_len : bs3.length = bs2.length + f3.length := List.length_append
  refine step_encraw_tag4_prealloc_placed_x hC ss v s0.sp G.root.cap G.root.ptr cap0 ptr0
    bs3 (keyToBytes32 m.state.rootKey)
    (by rw [hbs3_len, hbs2_len, hbs1_len]; dsimp only [f4] at hspare_expand; omega)
    (by rw [hbs3_len, hbs2_len, hbs1_len]; dsimp only [f4] at hfit_expand; omega)
    hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hcs4 (by sep_focus) ?_
  intro s5 hvm4 hpc5 hrun5 htr5_sp htr5 hx19_5 hx20_5 hcs5
  let bs4 := bs3 ++ f4
  have hbs4_len : bs4.length = bs3.length + f4.length := List.length_append
  refine step_encraw_tag5_prealloc_placed_x A ss v s0.sp cap0 ptr0 m.state.previousCounter
    bs4
    (by rw [hbs4_len, hbs3_len, hbs2_len, hbs1_len]; dsimp only [f5] at hspare_expand; omega)
    (by rw [hbs4_len, hbs3_len, hbs2_len, hbs1_len]; dsimp only [f5] at hfit_expand; omega)
    hpc5 hrun5 htr5_sp halign htr5 hx19_5 hx20_5 hcs5 (by sep_focus) ?_
  intro s6 hvm5 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6
  let bs5 := bs4 ++ f5
  have hbs5_len : bs5.length = bs4.length + f5.length := List.length_append
  refine step_encraw_tag6_prealloc_placed_x hEC ss v s0.sp cap0 ptr0 G.sender m.state.senderChain
    bs5
    (by rw [hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len]; dsimp only [f6] at hspare_expand; omega)
    (by rw [hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len]; dsimp only [f6] at hfit_expand; omega)
    hpc6 hrun6 hsp6 halign htr6 hx19_6 hx20_6 hcs6 (by sep_focus) ?_
  intro s7 hvm6 hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hcs7
  let bs6 := bs5 ++ f6
  have hbs6_len : bs6.length = bs5.length + f6.length := List.length_append
  refine step_encraw_tag7_prealloc_placed_x hEC ss v s0.sp G.chainsCap G.chainsPtr cap0 ptr0
    (G.chains.zip m.state.receiverChains) bs6
    (by rw [hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len];
        dsimp only [f7] at hspare_expand; omega)
    (by rw [hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len];
        dsimp only [f7] at hfit_expand; omega)
    hpc7 hrun7 hsp7 halign htr7 hx19_7 hx20_7 hcs7 (by sep_focus) ?_
  intro s8 hvm7 hpc8 hrun8 hsp8 htr8 hx19_8 hx20_8 hcs8
  let bs7 := bs6 ++ f7
  have hbs7_len : bs7.length = bs6.length + f7.length := List.length_append
  refine step_encraw_tag9_prealloc_placed_x hC ss v s0.sp cap0 ptr0 G.pending m.pendingPreKey
    bs7 hpending
    (by revert hpending; cases h : G.pending with
        | none => intro _; trivial
        | some g => intro _; exact hpend_bound g h)
    (by rw [hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len];
        dsimp only [f9] at hfit_expand; omega)
    (by rw [hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len];
        dsimp only [f9] at hspare_expand; omega)
    hpc8 hrun8 hsp8 halign htr8 hx19_8 hx20_8 hcs8 (by sep_focus) ?_
  intro s9 hvm8 hpc9 hrun9 hsp9 htr9 hx19_9 hx20_9 hcs9
  let bs8 := bs7 ++ f9
  have hbs8_len : bs8.length = bs7.length + f9.length := List.length_append
  refine step_encraw_tag10_prealloc_placed_x A ss v s0.sp cap0 ptr0 m.remoteRegistrationId
    bs8
    (by rw [hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len];
        dsimp only [f10] at hspare_expand; omega)
    (by rw [hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len];
        dsimp only [f10] at hfit_expand; omega)
    hpc9 hrun9 hsp9 halign htr9 hx19_9 hx20_9 hcs9 (by sep_focus) ?_
  intro s10 hvm9 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10
  let bs9 := bs8 ++ f10
  have hbs9_len : bs9.length = bs8.length + f10.length := List.length_append
  refine step_encraw_tag11_prealloc_placed_x A ss v s0.sp cap0 ptr0 m.localRegistrationId
    bs9
    (by rw [hbs9_len, hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len];
        dsimp only [f11] at hspare_expand; omega)
    (by rw [hbs9_len, hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len, hbs1_len];
        dsimp only [f11] at hfit_expand; omega)
    hpc10 hrun10 hsp10 halign htr10 hx19_10 hx20_10 hcs10 (by sep_focus) ?_
  intro s11 hvm10 hpc11 hrun11 hsp11 htr11 hx19_11 hx20_11 hcs11
  let bs10 := bs9 ++ f11
  have hbs10_len : bs10.length = bs9.length + f11.length := List.length_append
  refine step_encraw_tag13_prealloc_placed_x hC ss v s0.sp G.alice.cap G.alice.ptr cap0 ptr0
    bs10 m.aliceBaseKey
    (by rw [hbs10_len, hbs9_len, hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len,
            hbs1_len];
        dsimp only [f13] at hspare_expand; omega)
    (by rw [hbs10_len, hbs9_len, hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len, hbs2_len,
            hbs1_len];
        dsimp only [f13] at hfit_expand; omega)
    hpc11 hrun11 hsp11 halign htr11 hx19_11 hx20_11 hcs11 (by sep_focus) ?_
  intro s12 hvm11 hpc12 hrun12 hsp12 htr12 hx19_12 hx20_12 hcs12
  let bs11 := bs10 ++ f13
  have hbs11_len : bs11.length = bs10.length + f13.length := List.length_append
  refine step_encraw_tag14_prealloc_placed_x hC ss v s0.sp cap0 ptr0 G.kyber m.pendingKyberPreKey
    bs11 hkyber
    (by revert hkyber; cases h : m.pendingKyberPreKey with
        | none => intro _; trivial
        | some k => intro _; exact hkyber_bound k h)
    (by rw [hbs11_len, hbs10_len, hbs9_len, hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len,
            hbs2_len, hbs1_len];
        dsimp only [f14] at hspare_expand; omega)
    (by rw [hbs11_len, hbs10_len, hbs9_len, hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len, hbs3_len,
            hbs2_len, hbs1_len];
        dsimp only [f14] at hfit_expand; omega)
    hpc12 hrun12 hsp12 halign htr12 hx19_12 hx20_12 hcs12 (by sep_focus) ?_
  intro s13 hvm12 hpc13 hrun13 hsp13 htr13 hx19_13 hx20_13 hcs13
  let bs12 := bs11 ++ f14
  have hbs12_len : bs12.length = bs11.length + f14.length := List.length_append
  refine step_encraw_tag15_prealloc_placed_x hC ss v s0.sp G.pq.cap G.pq.ptr cap0 ptr0
    bs12 m.state.pqRatchetState
    (by rw [hbs12_len, hbs11_len, hbs10_len, hbs9_len, hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len,
            hbs3_len, hbs2_len, hbs1_len];
        dsimp only [f15] at hspare_expand; omega)
    (by rw [hbs12_len, hbs11_len, hbs10_len, hbs9_len, hbs8_len, hbs7_len, hbs6_len, hbs5_len, hbs4_len,
            hbs3_len, hbs2_len, hbs1_len];
        dsimp only [f15] at hpq_le hfit_expand; omega)
    hpc13 hrun13 hsp13 halign htr13 hx19_13 hx20_13 hcs13 (by sep_focus) ?_
  intro s14 hvm13 hpc14 hrun14 hsp14 htr14 hcs14
  refine step_encraw_epilogue_placed_x (H := H) s0.sp v56
    hpc14 hrun14 hsp14 halign htr14 rfl hcs14 (by sep_focus) ?_
  intro sm hvm_ep hpcm hrunm hspm htrm hcsm
  have hvm_tot : VmPreserved s0 sm :=
    hvm0.trans (hvm1.trans (hvm2.trans (hvm3.trans (hvm4.trans (hvm5.trans
      (hvm6.trans (hvm7.trans (hvm8.trans (hvm9.trans (hvm10.trans
        (hvm11.trans (hvm12.trans (hvm13.trans hvm_ep)))))))))))))
  have hbytes :
      bs12 ++ bytesField 15 m.state.pqRatchetState = bs0 ++ encSessionMem G m := by
    simp only [bs12, bs11, bs10, bs9, bs8, bs7, bs6, bs5, bs4, bs3, bs2, bs1,
      f1, f2, f3, f4, f5, f6, f7, f9, f10, f11, f13, f14,
      encSessionMem, List.append_assoc]
  apply SepWPpLsCl.done hpcm hrunm
  refine ⟨fun hm => ?_, hspm, hcsm⟩
  rw [satisfies_pure_sepConj]
  refine ⟨⟨htrm, hvm_tot⟩, ?_⟩
  rw [hSessEq, ← hbytes]
  unfold sessionRawOpen
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm

theorem encodeRawPrealloc_placed_cl_of_chain [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hEC : EncodeChainPreallocPlacedOkX' A.repAlloc H) :
    subroutine_ok callerProg (lsmpl.base 14)
      (withLsCl lsmpl (encodeRawPreallocSpecX A.repAlloc)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeRawPrealloc_placed_ok_of_chain hC hEC)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRawSpareXBudget
