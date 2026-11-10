/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogue
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.FindIndexCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WP.FrameAuto
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Epilogue of `RatchetState::consume_message_key`

Proves `AdvanceEpiloguePlacedSpec` and `AdvanceEpiloguePlacedRoSpec` (Block 24) under
`RustCliAllocBudget M` and `SeamBudget`, ruling out allocator OOM on both 32-byte allocations.
-/

@[expose] public section

set_option maxRecDepth 200000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueBudget

open Arm64 ProofLib
open Arm64.ReachesOutcome (reaches_outcome_of_sepWPp)
open CryptoGames.HMAC (ShaState keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey PublicKey RatchetState ReceiverChain maxMessageKeys
)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
  blkLib_eq_24 blkPC_24 blkPl_24
  libsignalRoLoaded_of_keepsFrozen lsLogFilterAddr lsmpl lsρ
)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecHeader)
open CryptoVerification.LibsignalSessionRepr (
  RatchetGhost chainAt chainKeyBytes consumeMessageKeyResultAt
  length_keyToBytes32 optChainKeyAt optChainKeyNone
  optChainKeyAt_some_entails_dealloc ratchetAt
)
open CryptoVerification.SessionModel (chainStepN)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost
  cmkDummyImg cmkEpiloguePC_placed cmkLoopFrame cmkLoopHeap_placed cmkSavedRegs cmkStack
  cmkRustAllocSym cmkRustDeallocSym cmkRustNoAllocShimSym
  cmk_hook_ok_of_mem logFilterAddr_cmkDummyImg map_snd_zip_chains
)
open CryptoVerification.LibsignalSession.AdvanceEpilogue (
  BitVec_ofFin_eq_ofNat Int64_mk_toBitVec UInt64_mk_toBitVec UInt64_ofNat_toBitVec
  SepWPp.conseq_pre
  cells4_entails_memRegion32 chainKeyBytes_pointsTo chainKey_key_idx_entails_memRegion
  chainStepN_one cmkLoopFrameRest cmkLoopFrame_repack cmkLoopFrame_unpack
  focus_optChainKeyAt
  hmacWith_one_eq_messageKeys_seed keyToBytes32_chainStepN_one
  length_messageKeys_seed
  memRegion32_eq_exists_cells4 memRegion88_unpack
  optChainKeyAt_none_unpack optChainKeyAt_some_of_parts
  pointsTo8_eq_pointsToBytes1 pointsToBytes1_31_entails_cells4
  ratchetAt_expose_for_findIndex ratchetRestAtChain ratchetTail
  repack_optChainKeyAt resultAt_ok_of_parts sepWPp_seq_lscl
  stackAt_7712_split_1024 stackAt_7712_split_2048 stackAt_7712_split_4096
  stackAt_cmkStack_repack ule_false_of_lt
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits
  FitsEvents FreeOnlyEvs RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustCliAllocNoOomSpec rustCliDeallocBudgetSpec rustDeallocEvents
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (hmacSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  AdvanceEpiloguePlacedRoSpec AdvanceEpiloguePlacedSpec
  CmkAllocHooks CmkEnv CmkEpilogueEvs CmkLoopState_placed
  FindIndexPlacedOk HmacPlacedOk HmacPlacedRoOk
  cmkPlacedSpec cmkShimSpec findIndexPlacedSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget (
  ConcatEnv findIndex_placed_ok_at_state
  hmacAtStateSpec hmac_placed_ok_at_state hmac_placed_ro_ok_at_state
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget)

attribute [local irreducible] Program.fetch Program.externAt? cmkDummyImg
attribute [-simp, -arm64_norm, -wp_norm] logFilterAddr_cmkDummyImg
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  Int64_mk_toBitVec UInt64_ofNat_toBitVec UInt64_mk_toBitVec BitVec_ofFin_eq_ofNat

/-! ## Structural and Allocator-State Helpers -/

private class EpInvClass [LibsignalPlacement] (Inv : Memory → Prop) : Prop where
  of_keepsFrozen : ∀ {m m' : Memory}, Inv m → m.KeepsFrozen m' → Inv m'
  to_lscl : ∀ {m : Memory}, Inv m → LibsignalCodeLoaded lsmpl m

private instance [LibsignalPlacement] : EpInvClass (LibsignalCodeLoaded lsmpl) where
  of_keepsFrozen h hkf := h.of_keepsFrozen hkf
  to_lscl h := h

private instance [LibsignalPlacement] :
    EpInvClass (fun m => LibsignalCodeLoaded lsmpl m ∧ LibsignalRoLoaded lsmpl m) where
  of_keepsFrozen h hkf := ⟨h.1.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen h.2 hkf⟩
  to_lscl h := h.1

private theorem sepWPp_seq_epInv [LibsignalPlacement] {Inv : Memory → Prop} [EpInvClass Inv]
    {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      Inv sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => EpInvClass.of_keepsFrozen h hkf) hinv h

private theorem sepWPp_frame_weaken {prog : Program} {ret : BitVec 64} {s : State}
    {P P₀ P' F : SepProp} {Q Qp : State → SepProp → Prop}
    (hSub : P₀ ⊢ P')
    (hsplit : P = P₀ ∗ F := by sep_frame)
    (hnext : SepWPp prog ret s (P' ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.conseq_pre (hsplit ▸ sepConj_mono_left hSub) hnext

private theorem entails_pull_pure4 {P0 A B C D : SepProp} {φ : Prop}
    (h : P0 ⊢ A ∗ B ∗ C ∗ (⌜φ⌝ ∗ D)) :
    P0 ⊢ ⌜φ⌝ ∗ (A ∗ B ∗ C ∗ D) := by
  have heq : A ∗ B ∗ C ∗ (⌜φ⌝ ∗ D) = ⌜φ⌝ ∗ (A ∗ B ∗ C ∗ D) := by sep_ac_rfl
  exact heq ▸ h

private theorem ratchetAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    ratchetAt (A.atState lim st s) = ratchetAt A.repAlloc :=
  rfl

private theorem consumeMessageKeyResultAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    consumeMessageKeyResultAt (A.atState lim st s) = consumeMessageKeyResultAt A.repAlloc :=
  rfl

def advanceEpilogueBudgetPost [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ConsumeMessageKeyGhost) (st_init : M.σ) (R : SepProp) (s0 sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (cmkPlacedSpec F A lim).post (x, st_init) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

def advanceEpilogueBudgetPanic [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ConsumeMessageKeyGhost) (st_init : M.σ) (R : SepProp) (s0 sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 sf ∗ R)

/-! ## Epilogue Segment Execution (`+0x4dc .. +0x798`) -/

set_option maxHeartbeats 800000 in
theorem advanceEpilogue_ret_epilogue_placed [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (x : ConsumeMessageKeyGhost) (st_init : M.σ) (evs_tot : List AllocEvent)
    (G' : RatchetGhost) (R : SepProp) (s0 s : State)
    (henv_tot : CmkEnv x evs_tot)
    (hpc : s.pc = (blkPl_24).base + 1916#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (_hsp : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hmodel_ok : (x.model F).1 ≠ .error .panic)
    (hagree : x.G.AgreeExcept G' (x.touched F)) :
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s
      (ratchetAt A.repAlloc x.self G' (x.model F).2 ∗
       consumeMessageKeyResultAt A.repAlloc x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       memRegion (s0.sp - 480#64) 384 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool lim (M.stepEvents evs_tot st_init) s)
      (advanceEpilogueBudgetPost F A lim x st_init R s0)
      (advanceEpilogueBudgetPanic F A lim x st_init R s0) := by
  unfold cmkSavedRegs
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  refine SepWPp.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨fun hm => ?_, by simp only [wp_norm, arm64_norm, *], by
      simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, applyWriteback,
        State.advancePC_eq_setPC, State.setPC_setPC, State.writeReg64_setPC, State.setPState_setPC,
        State.setPState_setPState, State.writeReg64_setPState, State.setMem_setPC, State.setMem_setMem,
        State.writeReg64_setMem, State.setPState_setMem, State.writeReg64_writeReg64_same,
        arm64_norm, *]⟩
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  unfold cmkPlacedSpec CryptoVerification.LibsignalSession.cmkPlacedSpec
    CryptoVerification.withLsCodeLoaded
  dsimp only
  refine Entails.sepExists_right evs_tot (Entails.pure_right henv_tot ?_)
  refine Entails.pure_right ⟨hmodel_ok, by simp only [wp_norm, arm64_norm, *]⟩ ?_
  simp only [ratchetAt_atState, consumeMessageKeyResultAt_atState, RustCliAllocBudget.atState_pool]
  have hstk := stackAt_cmkStack_repack s0.sp s0
  unfold cmkSavedRegs at hstk
  have hex :
      ratchetAt A.repAlloc x.self G' (x.model F).2 ⊢
        ∃∗ G'' : RatchetGhost,
          ⌜x.G.AgreeExcept G'' (x.touched F)⌝ ∗ ratchetAt A.repAlloc x.self G'' (x.model F).2 :=
    Entails.sepExists_right G' (Entails.pure_right hagree (Entails.refl _))
  refine Entails.trans ?_ (sepConj_mono_left hex)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk))))))
  have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
  exact heq (by sep_ac_rfl)

set_option maxHeartbeats 1600000 in
theorem advanceEpilogue_after_hmac1_placed [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (x : ConsumeMessageKeyGhost) (st_init st2 : M.σ)
    (hsb2 : SeamBudget M lim (CmkEnv x) st_init st2 (fun evs => evs = rustAllocEvents 32 1))
    (G' : RatchetGhost) (ckc : ChainKey) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1448#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (_hsp0 : s0.spAligned = true)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hagree : x.G.AgreeExcept G' (x.touched F)) :
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s
      (ratchetAt A.repAlloc x.self G' (x.model F).2 ∗
       memRegion x.ret 88 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦ₛ [1#8]) ∗
       memRegion (s0.sp - 319#64) 31 ∗
       ((s0.sp - 224#64) ↦ₛ (ckc.messageKeys F).seed) ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool lim st2 s)
      (advanceEpilogueBudgetPost F A lim x st_init R s0)
      (advanceEpilogueBudgetPanic F A lim x st_init R s0) := by
  have hfit32 : FitsEvents M lim st2 (rustAllocEvents 32 1) :=
    hsb2.1 (rustAllocEvents 32 1) rfl
  obtain ⟨evs_tot, hst_tot, henv_tot⟩ :=
    hsb2.finish (evs_exit := rustAllocEvents 32 1) rfl
  have hshim : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H)
      (lsρ cmkRustNoAllocShimSym) cmkShimSpec :=
    cmk_hook_ok_of_mem hA.2.2.1
  dsimp only [cmkShimSpec] at hshim
  have halloc_nooom : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H)
      (lsρ cmkRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (cmk_hook_ok_of_mem hA.1)
  have hret_fn := @advanceEpilogue_ret_epilogue_placed _ M F A lim H x st_init evs_tot G' R s0
  have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : RustLayoutOk 32 1 := ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
  have hfe32_raw : FitsEvents M lim st2 [.alloc 32] := by
    simpa [rustAllocEvents] using hfit32
  rcases hfe32_raw with ⟨⟨_hwma32, _henf32, _hram32, _hva32⟩, -⟩
  obtain ⟨w0, w1, w2, w3, _, hw_seed⟩ := exists_unpack64_of_length_32 (length_messageKeys_seed F ckc)
  rw [hw_seed (s0.sp - 224#64), stackAt_7712_split_4096 (s0.sp - 480#64)]
  refine sepWPp_frame_weaken (memRegion88_unpack x.ret) (hnext := ?_)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun t0 => SepWPp.exists_elim fun c0 =>
    SepWPp.exists_elim fun p0 => SepWPp.exists_elim fun l0 => SepWPp.exists_elim fun i0 => ?_
  refine sepWPp_seq_lscl (mid := (blkPl_24).base + bv% (1468)) hloaded ?_
  wp_steps_sync_pool (lsρ cmkRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  have htr_sf0 : sf.trace = s0.trace :=
    (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, *])
  wp_steps_sync_pool (lsρ cmkRustAllocSym)
  wp_call halloc_nooom (32, 1, st2)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded1
  have hsp_sf1 : sf_1.spAligned = true := by
    unfold State.spAligned at *
    simp only [wp_norm, arm64_norm, *]
  have htr_sf1 : sf_1.trace = s0.trace :=
    (‹AllocCallPreserved _ sf_1›).2.1.trans (by simp only [wp_norm, arm64_norm, *])
  have hoom : sf_1.readReg64 Reg.x0 ≠ 0 := ‹sf_1.readReg64 .x0 ≠ 0#64›
  have hoom' : ¬sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
  have hcbz_oom : (sf_1.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  rw [hst_tot, memRegion32_eq_exists_cells4 (sf_1.readReg64 Reg.x0)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
  refine sepWPp_seq_lscl (mid := (blkPl_24).base + bv% (1916)) hloaded1 ?_
  wp_steps_sync_pool ((blkPl_24).base + bv% (1916))
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro _hloaded2
  have hmodel_ok : (x.model F).1 ≠ .error .panic := by rw [hm1]; nofun
  have hres := resultAt_ok_of_parts A.repAlloc x.ret (sf_1.readReg64 Reg.x0) (ckc.messageKeys F)
    (length_messageKeys_seed F ckc) hoom
  rw [hw_seed (sf_1.readReg64 Reg.x0)] at hres
  have hck_mem := chainKey_key_idx_entails_memRegion x.ckA ckc
  have hfrm_mem := cmkLoopFrame_repack s0.sp x.ret x.counter 1#8
  rw [← pointsTo8_eq_pointsToBytes1] at hfrm_mem
  have h224 :
      ((s0.sp - 224#64) ↦₆₄ w0) ∗ ((s0.sp - 216#64) ↦₆₄ w1) ∗
        ((s0.sp - 208#64) ↦₆₄ w2) ∗ ((s0.sp - 200#64) ↦₆₄ w3) ⊢
        memRegion (s0.sp - 224#64) 32 := by
    have := cells4_entails_memRegion32 (s0.sp - 224#64) w0 w1 w2 w3
    have ha1 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_arith
    have ha2 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_arith
    have ha3 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_arith
    rwa [ha1, ha2, ha3] at this
  refine sepWPp_frame_weaken h224 (hnext := ?_)
  refine sepWPp_frame_weaken hfrm_mem (hnext := ?_)
  refine sepWPp_frame_weaken hck_mem (hnext := ?_)
  refine sepWPp_frame_weaken hres (hnext := ?_)
  refine SepWPp.conseq_pre ?_
    (hret_fn _ henv_tot
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by unfold State.spAligned at *; simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hmodel_ok hagree)
  have h8192 : s0.sp - 480#64 - 7712#64 = s0.sp - 8192#64 := by bv_arith
  have hsf_sp : sf.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
  have hsf1_sp : sf_1.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
  rw [hm1, stackAt_7712_split_4096 (s0.sp - 480#64), h8192]
  simp only [State.sp_setMem, State.sp_writeReg64, State.sp_setPC, State.sp_setPState,
    hsf1_sp, hsf_sp, hsp_eq]
  have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
  exact heq (by sep_ac_rfl)

set_option maxHeartbeats 1600000 in
private theorem advanceEpilogue_set_chain_and_hmac1_placed_inv [LibsignalPlacement]
    {Inv : Memory → Prop} [EpInvClass Inv] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (hhmac_at : ∀ {s : State}, Inv s.mem →
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s))
    (x : ConsumeMessageKeyGhost) (st_init st2 : M.σ)
    (hsb2 : SeamBudget M lim (CmkEnv x) st_init st2 (fun evs => evs = rustAllocEvents 32 1))
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (ptr_ck c0 p0 l0 : BitVec 64) (idx0 : BitVec 32)
    (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1400#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp0 : s0.spAligned = true)
    (hsp : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hloaded : Inv s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx20 : s.readReg64 .x20 = (ckc.index + 1#32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = ptr_ck)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hptr_nz : ptr_ck ≠ 0)
    (hci : ci < stc.receiverChains.length)
    (hgi : ci < Gc.chains.length)
    (hchains_len : Gc.chains.length = stc.receiverChains.length)
    (hpad_len : Gc.senderPad.length = 100)
    (hmax_jumps : stc.maxForwardJumps < 2 ^ 64)
    (hcap_le : stc.receiverChains.length ≤ Gc.chainsCap.toNat)
    (hcap_lt : Gc.chainsCap.toNat * 104 < 2 ^ 63)
    (hptr_ne : Gc.chainsPtr ≠ 0)
    (hsrk : PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length)
    (hagree_Gc : x.G.AgreeExcept Gc (some ci))
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hm2 : (x.model F).2 =
      { stc with
        receiverChains := stc.receiverChains.set ci
          { chc with chainKey := some (chainStepN F 1 ckc) } })
    (htouched : x.touched F = some ci) :
    let c_Addr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s
      (ratchetRestAtChain A.repAlloc x.self Gc stc ci chc hgi ∗
       ((c_Addr + 72#64) ↦₆₄ c0) ∗
       ((c_Addr + 80#64) ↦₆₄ p0) ∗
       ((c_Addr + 88#64) ↦₆₄ l0) ∗
       ((c_Addr + 96#64) ↦₃₂ idx0) ∗
       memRegion (c_Addr + 100#64) 4 ∗
       A.live ptr_ck 32 1 ∗
       (ptr_ck ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) ∗
       memRegion x.ret 88 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       memRegion (s0.sp - 320#64) 32 ∗
       memRegion (s0.sp - 224#64) 32 ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool lim st2 s)
      (advanceEpilogueBudgetPost F A lim x st_init R s0)
      (advanceEpilogueBudgetPanic F A lim x st_init R s0) := by
  intro c_Addr
  have hafter_fn := @advanceEpilogue_after_hmac1_placed _ M F A lim H hA x st_init st2 hsb2
  have hsplit320 :
      memRegion (s0.sp - 320#64) 32 =
        (∃∗ b0 : BitVec 8, ((s0.sp - 320#64) ↦₈ b0)) ∗ memRegion (s0.sp - 319#64) 31 := by
    have h319 : s0.sp - 320#64 + 1#64 = s0.sp - 319#64 := by bv_arith
    rw [show (32 : Nat) = 1 + 31 from rfl,
        memRegion_split (s0.sp - 320#64) 1 31 (by decide),
        memRegion_one (s0.sp - 320#64), h319]
  rw [hsplit320, stackAt_7712_split_2048 (s0.sp - 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  refine sepWPp_seq_epInv (mid := lsmpl.base 73) hloaded ?_
  wp_steps_sync_pool (lsmpl.base 73)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded1
  have hhmac1 := hhmac_at hloaded1
  dsimp only [hmacAtStateSpec, hmacSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.hmacSpec] at hhmac1
  have hlen_key : (keyToBytes32 ckc.key).length = 32 := length_keyToBytes32 ckc.key
  have hlen_inp : ([1#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 320#64) 1#8]
  refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1448)) hloaded1 ?_
  wp_call hhmac1 (s0.sp - 224#64, x.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [1#8])
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded2
  have hsp_sf : sf.spAligned = true := by
    unfold State.spAligned at *
    simp only [wp_norm, arm64_norm, *]
  have htr_sf : sf.trace = s0.trace :=
    (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, *])
  have hopt := optChainKeyAt_some_of_parts A.repAlloc (c_Addr + 72#64) ptr_ck (chainStepN F 1 ckc) hptr_nz
  have hrepack := repack_optChainKeyAt A.repAlloc x.self Gc stc ci chc hci hgi
    ⟨32#64, ptr_ck⟩ (some (chainStepN F 1 ckc))
    hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne hsrk hmax hklen
  have hst_eq : stc.setChain ci { chc with chainKey := some (chainStepN F 1 ckc) } = (x.model F).2 := by
    rw [hm2]; rfl
  rw [hst_eq] at hrepack
  have hc80 : c_Addr + 72#64 + 8#64 = c_Addr + 80#64 := by bv_arith
  have hc88 : c_Addr + 72#64 + 16#64 = c_Addr + 88#64 := by bv_arith
  have hc96 : c_Addr + 72#64 + 24#64 = c_Addr + 96#64 := by bv_arith
  have hc100 : c_Addr + 72#64 + 28#64 = c_Addr + 100#64 := by bv_arith
  rw [hc80, hc88, hc96, hc100] at hopt
  have hidx_eq : ckc.index + 1#32 = (chainStepN F 1 ckc).index := by
    simp [chainStepN_one]
  let G' := Gc.setChain ci { Gc.chains[ci]'hgi with ck := ⟨32#64, ptr_ck⟩ }
  have hagree' : x.G.AgreeExcept G' (x.touched F) := by
    rw [htouched]
    exact RatchetGhost.AgreeExcept.setChain_of_agreeExcept hagree_Gc hgi
      { Gc.chains[ci]'hgi with ck := ⟨32#64, ptr_ck⟩ } rfl rfl
  have hchain_pack :
      (((c_Addr + 72#64) ↦₆₄ 32#64) ∗
       ((c_Addr + 80#64) ↦₆₄ ptr_ck) ∗
       ((c_Addr + 88#64) ↦₆₄ 32#64) ∗
       ((c_Addr + 96#64) ↦₃₂ (chainStepN F 1 ckc).index) ∗
       memRegion (c_Addr + 100#64) 4 ∗
       A.live ptr_ck 32 1 ∗
       (ptr_ck ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key)) ∗
      ratchetRestAtChain A.repAlloc x.self Gc stc ci chc hgi ⊢
      ratchetAt A.repAlloc x.self G' (x.model F).2 :=
    Entails.trans (sepConj_mono_left hopt) hrepack
  rw [hidx_eq]
  refine sepWPp_frame_weaken hchain_pack (hnext := ?_)
  refine SepWPp.conseq_pre ?_
    (hafter_fn G' ckc R s0 sf
      hpc_sf hrun_sf (by simp only [wp_norm, arm64_norm, *]) hsp0 hsp_sf htr_sf
      (EpInvClass.to_lscl hloaded2)
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hm1 hagree')
  have h8192 : s0.sp - 480#64 - 7712#64 = s0.sp - 8192#64 := by bv_arith
  have hsf_sp : sf.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
  rw [hmacWith_one_eq_messageKeys_seed F ckc,
      stackAt_7712_split_2048 (s0.sp - 480#64), h8192,
      pointsTo8_eq_pointsToBytes1 (s0.sp - 320#64) 1#8]
  simp only [State.sp_setMem, State.sp_writeReg64, State.sp_setPC, State.sp_setPState,
    hsf_sp, hsp_eq]
  have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
  exact heq (by sep_ac_rfl)

set_option maxHeartbeats 1600000 in
private theorem advanceEpilogue_after_find_index_placed_inv [LibsignalPlacement]
    {Inv : Memory → Prop} [EpInvClass Inv] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (hhmac_at : ∀ {s : State}, Inv s.mem →
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s))
    (x : ConsumeMessageKeyGhost) (st_init st : M.σ)
    (hsb : SeamBudget M lim (CmkEnv x) st_init st (CmkEpilogueEvs false))
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1312#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp0 : s0.spAligned = true)
    (_hsp : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hloaded : Inv s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = 1#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx20 : s.readReg64 .x20 = Gc.chainsPtr)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 stc.receiverChains.length)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : s.readReg64 .x28 = ckc.index.zeroExtend 64)
    (hci : ci < stc.receiverChains.length)
    (hgi : ci < Gc.chains.length)
    (hchains_len : Gc.chains.length = stc.receiverChains.length)
    (hpad_len : Gc.senderPad.length = 100)
    (hmax_jumps : stc.maxForwardJumps < 2 ^ 64)
    (hcap_le : stc.receiverChains.length ≤ Gc.chainsCap.toNat)
    (hcap_lt : Gc.chainsCap.toNat * 104 < 2 ^ 63)
    (hptr_ne : Gc.chainsPtr ≠ 0)
    (hsrk : PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length)
    (hagree_Gc : x.G.AgreeExcept Gc (some ci))
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hm2 : (x.model F).2 =
      { stc with
        receiverChains := stc.receiverChains.set ci
          { chc with chainKey := some (chainStepN F 1 ckc) } })
    (htouched : x.touched F = some ci) :
    let c_Addr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s
      (optChainKeyAt A.repAlloc (Gc.chains[ci]'hgi).ck chc.chainKey (c_Addr + 72#64) ∗
       ratchetRestAtChain A.repAlloc x.self Gc stc ci chc hgi ∗
       memRegion x.ret 88 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) ∗
       memRegion (s0.sp - 224#64) 32 ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool lim st s)
      (advanceEpilogueBudgetPost F A lim x st_init R s0)
      (advanceEpilogueBudgetPanic F A lim x st_init R s0) := by
  intro c_Addr
  have hseq1 : ∀ e1 e2, (e1 = rustAllocEvents 32 1) →
      ConcatEnv FreeOnlyEvs (· = rustAllocEvents 32 1) e2 →
      CmkEpilogueEvs false (e1 ++ e2) := by
    rintro _ _ rfl ⟨ec, _, rfl, hec, rfl⟩
    exact ⟨ec, hec, by simp [List.append_assoc]⟩
  have hne1 : ∃ e2, ConcatEnv FreeOnlyEvs (· = rustAllocEvents 32 1) e2 :=
    ⟨rustAllocEvents 32 1, [], rustAllocEvents 32 1, rfl, FreeOnlyEvs.nil, rfl⟩
  have hfit1 : FitsEvents M lim st (rustAllocEvents 32 1) :=
    (hsb.fitsSeg hseq1 hne1) (rustAllocEvents 32 1) rfl
  have hsb1 : SeamBudget M lim (CmkEnv x) st_init (M.stepEvents (rustAllocEvents 32 1) st)
      (ConcatEnv FreeOnlyEvs (· = rustAllocEvents 32 1)) :=
    hsb.step hseq1 rfl
  have hshim : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H)
      (lsρ cmkRustNoAllocShimSym) cmkShimSpec :=
    cmk_hook_ok_of_mem hA.2.2.1
  dsimp only [cmkShimSpec] at hshim
  have halloc_nooom : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H)
      (lsρ cmkRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (cmk_hook_ok_of_mem hA.1)
  have hdealloc : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H)
      (lsρ cmkRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    cmk_hook_ok_of_mem hA.2.1
  have hset_fn := @advanceEpilogue_set_chain_and_hmac1_placed_inv _ Inv _ M F A lim H hA hhmac_at x st_init
  have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : RustLayoutOk 32 1 := ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
  have hfe32_raw : FitsEvents M lim st [.alloc 32] := by
    simpa [rustAllocEvents] using hfit1
  rcases hfe32_raw with ⟨⟨_hwma32, _henf32, _hram32, _hva32⟩, -⟩
  obtain ⟨w0, w1, w2, w3, _, hw_ck⟩ :=
    exists_unpack64_of_length_32 (length_keyToBytes32 (chainStepN F 1 ckc).key)
  rw [hw_ck (s0.sp - 320#64), stackAt_7712_split_4096 (s0.sp - 480#64)]
  refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1340)) hloaded ?_
  wp_steps_sync_pool (lsρ cmkRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  have htr_sf0 : sf.trace = s0.trace :=
    (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, *])
  wp_steps_sync_pool (lsρ cmkRustAllocSym)
  wp_call halloc_nooom (32, 1, st)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded1
  have hsp_sf1 : sf_1.spAligned = true := by
    unfold State.spAligned at *
    simp only [wp_norm, arm64_norm, *]
  have htr_sf1 : sf_1.trace = s0.trace :=
    (‹AllocCallPreserved _ sf_1›).2.1.trans (by simp only [wp_norm, arm64_norm, *])
  have hoom : sf_1.readReg64 Reg.x0 ≠ 0 := ‹sf_1.readReg64 .x0 ≠ 0#64›
  have hoom_false : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
    beq_false_of_ne hoom
  have hoom_not_true : ¬((sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true) := by
    rw [hoom_false]; decide
  rw [memRegion32_eq_exists_cells4 (sf_1.readReg64 Reg.x0)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
  have hci_bv : BitVec.ofNat 64 ci < BitVec.ofNat 64 stc.receiverChains.length := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact hci
  have hci_not_le : ¬(BitVec.ofNat 64 stc.receiverChains.length ≤ BitVec.ofNat 64 ci) := by
    bv_omega
  have hci_ule : (BitVec.ofNat 64 stc.receiverChains.length).ule (BitVec.ofNat 64 ci) = false :=
    ule_false_of_lt hci_bv
  have hci_not_ule : ¬((BitVec.ofNat 64 stc.receiverChains.length).ule (BitVec.ofNat 64 ci) = true) := by
    rw [hci_ule]; decide
  refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1376)) hloaded1 ?_
  wp_steps_sync_pool ((blkPl_24).base + bv% (1376))
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded2
  have hc_addr_eq :
      Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = c_Addr := by
    change Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    rw [BitVec.ofNat_mul]
  have h8192 : s0.sp - 480#64 - 7712#64 = s0.sp - 8192#64 := by bv_arith
  have h320_mem :
      ((s0.sp - 320#64) ↦₆₄ w0) ∗ ((s0.sp - 312#64) ↦₆₄ w1) ∗
        ((s0.sp - 304#64) ↦₆₄ w2) ∗ ((s0.sp - 296#64) ↦₆₄ w3) ⊢
        memRegion (s0.sp - 320#64) 32 := by
    have := cells4_entails_memRegion32 (s0.sp - 320#64) w0 w1 w2 w3
    have ha1 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_arith
    have ha2 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_arith
    have ha3 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_arith
    rwa [ha1, ha2, ha3] at this
  cases hck_opt : chc.chainKey with
  | none =>
    have hsb2 : SeamBudget M lim (CmkEnv x) st_init (M.stepEvents (rustAllocEvents 32 1) st)
        (fun evs => evs = rustAllocEvents 32 1) :=
      hsb1.weaken fun _ h => ⟨[], _, rfl, FreeOnlyEvs.nil, h⟩
    have hnone_unpack := optChainKeyAt_none_unpack A.repAlloc (Gc.chains[ci]'hgi).ck (c_Addr + 72#64)
    have hc80 : c_Addr + 72#64 + 8#64 = c_Addr + 80#64 := by bv_arith
    have hc88 : c_Addr + 72#64 + 16#64 = c_Addr + 88#64 := by bv_arith
    have hc96 : c_Addr + 72#64 + 24#64 = c_Addr + 96#64 := by bv_arith
    have hc100 : c_Addr + 72#64 + 28#64 = c_Addr + 100#64 := by bv_arith
    rw [hc80, hc88, hc96, hc100] at hnone_unpack
    refine sepWPp_frame_weaken hnone_unpack (hnext := ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun idx0 => SepWPp.exists_elim fun l0 =>
      SepWPp.exists_elim fun p0 => ?_
    have hslt_none : BitVec.slt optChainKeyNone 1#64 = true := by decide
    refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1400)) hloaded2 ?_
    wp_steps_sync_pool ((blkPl_24).base + bv% (1400))
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hloaded3
    refine sepWPp_frame_weaken h320_mem (hnext := ?_)
    refine SepWPp.conseq_pre ?_
      (hset_fn (M.stepEvents (rustAllocEvents 32 1) st) hsb2
        Gc stc ckc ci chc (sf_1.readReg64 Reg.x0) optChainKeyNone p0 l0 idx0 R s0 _
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hsp0
        (by unfold State.spAligned at *; simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hloaded3
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [c_Addr, wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hoom hci hgi hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne
        hsrk hmax hklen hagree_Gc hm1 hm2 htouched)
    dsimp only [c_Addr]
    have hsf_sp : sf.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
    have hsf1_sp : sf_1.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
    rw [hw_ck (sf_1.readReg64 Reg.x0), stackAt_7712_split_4096 (s0.sp - 480#64), h8192]
    simp only [State.sp_setMem, State.sp_writeReg64, State.sp_setPC, State.sp_setPState,
      hsf1_sp, hsf_sp, hsp_eq]
    have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
    exact heq (by sep_ac_rfl)
  | some old_ck =>
    let evs_ck := rustDeallocEvents (Gc.chains[ci]'hgi).ck.cap.toNat 1
    have hfree_ck : FreeOnlyEvs evs_ck := FreeOnlyEvs.singleton 1 (Gc.chains[ci]'hgi).ck.cap.toNat
    have hsb2 : SeamBudget M lim (CmkEnv x) st_init
        (M.stepEvents evs_ck (M.stepEvents (rustAllocEvents 32 1) st))
        (fun evs => evs = rustAllocEvents 32 1) :=
      hsb1.step (segEnv := (· = evs_ck))
        (by intro e1 e2 he1 he2; subst he1; subst he2; exact ⟨evs_ck, rustAllocEvents 32 1, rfl, hfree_ck, rfl⟩)
        rfl
    have hsome_unpack := entails_pull_pure4
      (optChainKeyAt_some_entails_dealloc A.repAlloc (Gc.chains[ci]'hgi).ck old_ck (c_Addr + 72#64))
    unfold vecHeader at hsome_unpack
    have hc80 : c_Addr + 72#64 + 8#64 = c_Addr + 80#64 := by bv_arith
    have hc88 : c_Addr + 72#64 + 16#64 = c_Addr + 88#64 := by bv_arith
    have hc96 : c_Addr + 72#64 + 24#64 = c_Addr + 96#64 := by bv_arith
    have hc100 : c_Addr + 72#64 + 28#64 = c_Addr + 100#64 := by bv_arith
    rw [hc80, hc88, hc96, hc100] at hsome_unpack
    refine sepWPp_frame_weaken hsome_unpack (hnext := ?_)
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hcap32, hcap_lt63, _hptr_old_ne⟩ => ?_
    have hcap_ne0 : (Gc.chains[ci]'hgi).ck.cap ≠ 0 := by
      intro h0; rw [h0] at hcap32; change 32 ≤ 0 at hcap32; omega
    simp only [hcap_ne0, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
    have hslt_some : ¬BitVec.slt (Gc.chains[ci]'hgi).ck.cap 1#64 := by
      unfold BitVec.slt
      have : (Gc.chains[ci]'hgi).ck.cap.toInt = (Gc.chains[ci]'hgi).ck.cap.toNat :=
        BitVec.toInt_eq_toNat_of_lt (by omega)
      have h1 : (1#64).toInt = 1 := rfl
      simp only [this, h1, decide_eq_true_eq]
      omega
    have hsf_sp : sf.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
    have hsf1_sp : sf_1.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
    have hsf_eq_sf1 : sf.sp = sf_1.sp := hsf_sp.trans hsf1_sp.symm
    simp only [State.sp_setMem, State.sp_writeReg64, State.sp_setPC, State.sp_setPState,
      hsf_eq_sf1]
    refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1400)) hloaded2 ?_
    wp_steps_sync_pool (lsρ cmkRustDeallocSym)
    wp_call hdealloc ((Gc.chains[ci]'hgi).ck.ptr, (Gc.chains[ci]'hgi).ck.cap.toNat, 1,
      M.stepEvents (rustAllocEvents 32 1) st)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hloaded3
    have htr_sf2 : sf_2.trace = s0.trace :=
      (‹AllocCallPreserved _ sf_2›).2.1.trans (by simp only [wp_norm, arm64_norm, *])
    have hsf2_sp : sf_2.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
    refine sepWPp_frame_weaken h320_mem (hnext := ?_)
    refine SepWPp.conseq_pre ?_
      (hset_fn (M.stepEvents evs_ck (M.stepEvents (rustAllocEvents 32 1) st)) hsb2
        Gc stc ckc ci chc (sf_1.readReg64 Reg.x0)
        (Gc.chains[ci]'hgi).ck.cap (Gc.chains[ci]'hgi).ck.ptr 32#64 old_ck.index R s0 sf_2
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hsp0
        (by unfold State.spAligned at *; simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        htr_sf2
        hloaded3
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [c_Addr, wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hoom hci hgi hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne
        hsrk hmax hklen hagree_Gc hm1 hm2 htouched)
    dsimp only [c_Addr, evs_ck]
    rw [hw_ck (sf_1.readReg64 Reg.x0), stackAt_7712_split_4096 (s0.sp - 480#64), h8192]
    simp only [State.sp_setMem, State.sp_writeReg64, State.sp_setPC, State.sp_setPState,
      hsf2_sp, hsf1_sp, hsf_sp, hsp_eq]
    have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
    exact heq (by sep_ac_rfl)

set_option maxHeartbeats 1600000 in
private theorem advanceEpilogue_entry_placed_inv [LibsignalPlacement]
    {Inv : Memory → Prop} [EpInvClass Inv] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (hfind : FindIndexPlacedOk H A)
    (hhmac_at : ∀ {s : State}, Inv s.mem →
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s))
    (x : ConsumeMessageKeyGhost) (st_init st : M.σ)
    (hsb : SeamBudget M lim (CmkEnv x) st_init st (CmkEpilogueEvs false))
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1244#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp0 : s0.spAligned = true)
    (_hsp : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hloaded : Inv s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx26 : s.readReg64 .x26 = x.theirA)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : s.readReg64 .x28 = ckc.index.zeroExtend 64)
    (hck_eq : ckc.index = x.counter)
    (hc_max : x.counter ≠ BitVec.allOnes 32)
    (hci_find : stc.findReceiverChainIndex x.their = some ci)
    (hchc_get : stc.receiverChains[ci]? = some chc)
    (hagree_Gc : x.G.AgreeExcept Gc (some ci))
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hm2 : (x.model F).2 =
      { stc with
        receiverChains := stc.receiverChains.set ci
          { chc with chainKey := some (chainStepN F 1 ckc) } })
    (htouched : x.touched F = some ci) :
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s
      (cmkLoopHeap_placed (A.atState lim st s) x Gc stc ckc s0)
      (advanceEpilogueBudgetPost F A lim x st_init R s0)
      (advanceEpilogueBudgetPanic F A lim x st_init R s0) := by
  have hafter_find_fn :=
    @advanceEpilogue_after_find_index_placed_inv _ Inv _ M F A lim H hA hhmac_at
      x st_init st hsb Gc stc ckc ci chc R s0
  have ⟨hci, hchc_eq⟩ := List.getElem?_eq_some_iff.mp hchc_get
  unfold cmkLoopHeap_placed
  rw [ratchetAt_atState, RustCliAllocBudget.atState_pool,
      chainKeyBytes_pointsTo x.ckA ckc, stackAt_7712_split_2048 (s0.sp - 480#64)]
  refine sepWPp_frame_weaken (cmkLoopFrame_unpack s0.sp x.ret x.counter) (hnext := ?_)
  refine sepWPp_frame_weaken (ratchetAt_expose_for_findIndex A.repAlloc x.self Gc stc hci) (hnext := ?_)
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, _hcap_ne⟩ => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  refine sepWPp_seq_epInv (mid := lsmpl.base 73) hloaded ?_
  wp_steps_sync_pool (lsmpl.base 73)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded1
  have hhmac1 := hhmac_at hloaded1
  dsimp only [hmacAtStateSpec, hmacSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.hmacSpec] at hhmac1
  have hlen_key : (keyToBytes32 ckc.key).length = 32 := length_keyToBytes32 ckc.key
  have hlen_inp : ([2#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 320#64) 2#8]
  refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1276)) hloaded1 ?_
  wp_call hhmac1 (s0.sp - 224#64, x.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [2#8])
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  apply SepWP.done hpc_sf hrun_sf
  intro hloaded2
  have htr_sf : sf.trace = s0.trace :=
    (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, *])
  rw [← keyToBytes32_chainStepN_one F ckc,
      pointsTo8_eq_pointsToBytes1 (s0.sp - 320#64) 2#8]
  simp only [State.sp_setMem, State.sp_writeReg64, State.sp_setPC, State.sp_setPState, hsp_eq]
  obtain ⟨w0, w1, w2, w3, _, hw_ck⟩ :=
    exists_unpack64_of_length_32 (length_keyToBytes32 (chainStepN F 1 ckc).key)
  have h8192 : s0.sp - 480#64 - 7712#64 = s0.sp - 8192#64 := by bv_arith
  have h320_cells :
      ((s0.sp - 320#64) ↦ₛ [2#8]) ∗ memRegion (s0.sp - 319#64) 31 ⊢
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
          ((s0.sp - 320#64) ↦₆₄ d0) ∗ ((s0.sp - 312#64) ↦₆₄ d1) ∗
          ((s0.sp - 304#64) ↦₆₄ d2) ∗ ((s0.sp - 296#64) ↦₆₄ d3) := by
    have h319 : s0.sp - 320#64 + 1#64 = s0.sp - 319#64 := by bv_arith
    have ha1 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_arith
    have ha2 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_arith
    have ha3 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_arith
    have h := pointsToBytes1_31_entails_cells4 (s0.sp - 320#64) 2#8
    rwa [h319, ha1, ha2, ha3] at h
  have hstk_merge2048 :
      memRegion (s0.sp - 8192#64) 5664 ∗ stackAt (s0.sp - 480#64) 2048 ⊢
        stackAt (s0.sp - 480#64) 7712 := by
    rw [stackAt_7712_split_2048 (s0.sp - 480#64), h8192]
    exact Entails.refl _
  refine sepWPp_frame_weaken hstk_merge2048 (hnext := ?_)
  refine sepWPp_frame_weaken h320_cells (hnext := ?_)
  rw [hw_ck (s0.sp - 224#64), stackAt_7712_split_1024 (s0.sp - 480#64), h8192]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
  have hadd1_ne0 : x.counter + 1#32 ≠ 0#32 := by
    have hc_ne : x.counter ≠ 0xffffffff#32 := hc_max
    bv_omega
  have hadd1_beq0 : (x.counter + 1#32 == 0#32) = false :=
    beq_false_of_ne hadd1_ne0
  have hadd1_not_beq0 : ¬((x.counter + 1#32 == 0#32) = true) := by
    rw [hadd1_beq0]; decide
  refine sepWPp_seq_epInv (mid := lsmpl.base 26) hloaded2 ?_
  wp_steps_sync_pool (lsmpl.base 26)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded3
  have hfind1 := findIndex_placed_ok_at_state hfind (EpInvClass.to_lscl hloaded3)
  dsimp only [findIndexPlacedSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.findIndexPlacedSpec] at hfind1
  have hzip_len : (Gc.chains.zip stc.receiverChains).length = stc.receiverChains.length := by
    simp [hchains_len]
  have hlen_bv_toNat : (BitVec.ofNat 64 stc.receiverChains.length).toNat =
      (Gc.chains.zip stc.receiverChains).length := by
    rw [hzip_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hzip_cap_lt : (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63 := by
    rw [hzip_len]; omega
  refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1312)) hloaded3 ?_
  wp_call hfind1 (Gc.chainsPtr, Gc.chains.zip stc.receiverChains, x.theirA, x.their)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded4
  have htr_sf1 : sf_1.trace = s0.trace :=
    (‹sf_1.trace = _›).trans (by simp only [wp_norm, arm64_norm, *])
  have hpost_match :
      (match ((Gc.chains.zip stc.receiverChains).map (·.2)).findIdx?
          (fun c => c.senderRatchetKey == x.their) with
       | some i => sf_1.readReg64 .x0 = 1#64 ∧ (sf_1.readReg64 .x1).toNat = i
       | none => sf_1.readReg64 .x0 = 0#64) := by assumption
  have hmap_find :
      ((Gc.chains.zip stc.receiverChains).map (·.2)).findIdx?
        (fun c => c.senderRatchetKey == x.their) = some ci := by
    rw [map_snd_zip_chains hchains_len]
    exact hci_find
  rw [hmap_find] at hpost_match
  rcases hpost_match with ⟨hx0_sf1, hx1_toNat_sf1⟩
  have hx1_sf1 : sf_1.readReg64 Reg.x1 = BitVec.ofNat 64 ci := by
    rw [← hx1_toNat_sf1, BitVec.ofNat_toNat]; rfl
  have hgi : ci < Gc.chains.length := hchains_len ▸ hci
  have hfocus := focus_optChainKeyAt A.repAlloc x.self Gc stc ci chc hci hgi hchc_eq
  have h224_mem :
      ((s0.sp - 224#64) ↦₆₄ w0) ∗ ((s0.sp - 216#64) ↦₆₄ w1) ∗
        ((s0.sp - 208#64) ↦₆₄ w2) ∗ ((s0.sp - 200#64) ↦₆₄ w3) ⊢
        memRegion (s0.sp - 224#64) 32 := by
    have := cells4_entails_memRegion32 (s0.sp - 224#64) w0 w1 w2 w3
    have hb1 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_arith
    have hb2 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_arith
    have hb3 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_arith
    rwa [hb1, hb2, hb3] at this
  have h320_ck :
      ((s0.sp - 320#64) ↦₆₄ w0) ∗ ((s0.sp - 312#64) ↦₆₄ w1) ∗
        ((s0.sp - 304#64) ↦₆₄ w2) ∗ ((s0.sp - 296#64) ↦₆₄ w3) ⊢
        ((s0.sp - 320#64) ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) := by
    have ha1 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_arith
    have ha2 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_arith
    have ha3 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_arith
    rw [hw_ck (s0.sp - 320#64), ha1, ha2, ha3]
    exact Entails.refl _
  refine sepWPp_frame_weaken h224_mem (hnext := ?_)
  refine sepWPp_frame_weaken h320_ck (hnext := ?_)
  refine sepWPp_frame_weaken hfocus (hnext := ?_)
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hsrk, hmax, hklen⟩ => ?_
  refine SepWPp.conseq_pre ?_
    (hafter_find_fn sf_1
      hpc_sf_1 hrun_sf_1 (by simp only [wp_norm, arm64_norm, *]) hsp0
      (by unfold State.spAligned at *; simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) htr_sf1 hloaded4
      (by simp only [wp_norm, arm64_norm, *])
      hx0_sf1 hx1_sf1 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hci hgi hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne
      hsrk hmax hklen hagree_Gc hm1 hm2 htouched)
  have hsf_sp : sf.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
  have hsf1_sp : sf_1.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
  rw [stackAt_7712_split_1024 (s0.sp - 480#64), h8192]
  simp only [State.sp_setMem, State.sp_writeReg64, State.sp_setPC, State.sp_setPState,
    hsf1_sp, hsf_sp, hsp_eq]
  have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
  exact heq (by sep_ac_rfl)

/-! ## Top-Level Epilogue Theorems -/

/-- Budget-threaded relocatable correctness of the `consume_message_key` epilogue. -/
theorem advanceEpilogue_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) :
    AdvanceEpiloguePlacedSpec F A lim H := by
  intro hA hfind hhmac x st_init st Gc stc ckc ci chc R s0 s
    hck_eq hc_max hci_find hchc_get hagree_Gc hm1 hm2 htouched ⟨hsb, hstate⟩
  rcases hstate with ⟨hpc, ⟨hrun, hsp_eq, hsp0, hsp, hx29, htr, hloaded, hvregs⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, _hx19, hmem⟩
  change s.pc = (blkPl_24).base + 1244#64 at hpc
  exact reaches_outcome_of_sepWPp (spec := cmkPlacedSpec F A lim) (x := (x, st_init)) hmem
    (advanceEpilogue_entry_placed_inv (Inv := LibsignalCodeLoaded lsmpl) hA hfind
      (hmac_placed_ok_at_state hhmac) x st_init st hsb Gc stc ckc ci chc R s0 s
      hpc hrun hsp_eq hsp0 hsp hx29 htr hloaded hvregs
      hx21 hx23 hx26 hx27 hx28 hck_eq hc_max hci_find hchc_get
      hagree_Gc hm1 hm2 htouched)

/-- Budget-threaded `.rodata`-backed correctness of the `consume_message_key` epilogue. -/
theorem advanceEpilogue_placed_ro_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) :
    AdvanceEpiloguePlacedRoSpec F A lim H := by
  intro hA hfind hhmac x st_init st Gc stc ckc ci chc R s0 s
    hck_eq hc_max hci_find hchc_get hagree_Gc hm1 hm2 htouched ⟨hsb, hstate⟩ hro
  rcases hstate with ⟨hpc, ⟨hrun, hsp_eq, hsp0, hsp, hx29, htr, hloaded, hvregs⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, _hx19, hmem⟩
  change s.pc = (blkPl_24).base + 1244#64 at hpc
  exact reaches_outcome_of_sepWPp (spec := cmkPlacedSpec F A lim) (x := (x, st_init)) hmem
    (advanceEpilogue_entry_placed_inv
      (Inv := fun m => LibsignalCodeLoaded lsmpl m ∧ LibsignalRoLoaded lsmpl m) hA hfind
      (fun h => hmac_placed_ro_ok_at_state hhmac h.1 h.2)
      x st_init st hsb Gc stc ckc ci chc R s0 s
      hpc hrun hsp_eq hsp0 hsp hx29 htr ⟨hloaded, hro⟩ hvregs
      hx21 hx23 hx26 hx27 hx28 hck_eq hc_max hci_find hchc_get
      hagree_Gc hm1 hm2 htouched)

end LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueBudget
