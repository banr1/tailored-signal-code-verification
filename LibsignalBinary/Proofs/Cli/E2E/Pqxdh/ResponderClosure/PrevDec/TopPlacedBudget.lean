/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmBytesPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Compose
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.KeyPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Top-Level Inlined `SessionStructure::decode`

Assembles the `[LibsignalPlacement]` budget-threaded `LibsignalCodeRoLoaded` decode loop, tag-6
(`sender_chain`) and tag-7 (`receiver_chains`) arms, and top-level `OverPrevDecodeCroPlacedAt` /
`OverPrevDecodePlacedStmt` contracts on Block `518` (`lsProg_518 ext`) under `RustCliAllocBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (maxReceiverChains)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement
  lsHandleErrorSym lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsRustReallocSym
  lsmpl withLsCl
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainG ChainMergeGenGhost GenField prostChainGAt
)
open Symbolic.Swarm.TRREF.B3DeserQ (ExtraGQ GenFieldQ SSGQ genFieldsQ ssgqOf)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3 (
  chain3GAt chainMerge3StackX
  overDecChain_bridge_ext overDecChain_heap_post_ext overDecChain_heap_pre_ext
  overDecChain_mem96 overDecChain_payload_suffix
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  OverDecAnyField OverDecBytesField OverDecFreshChain OverDecG OverDecRecvField
  OverDecRegsCroPlaced OverDecRegsPlaced OverDecSavedRegs OverDecSenderField OverDecVarintField
  SepWPp_exists_left_rc SepWPp_pure_left_rc
  default_cells_bf0_entail_chain3GAt_ext len_ne_cap_of_lt_rc
  memRegion104_bf0_join_rc memRegion104_eq_exists_chunks104_6QWAt_rc memRegion344_a90_split_rc
  ofNat_length_eq_cap_of_eq_rc
  overDecFreshChain_cons_inv overDecSavedRegs_of_calleeSaved overDecStackX
  overDec_encSession_eq overDec_encSession_length_lt overDec_enc_ne_nil overDec_exit_ext
  overDec_flatMap_cons overDec_flatMap_ne_nil overDec_fold_genFieldsQ
  overDec_freshChain_genFieldsQ overDec_genFieldsQ_ne_nil overDec_mem_genFieldsQ
  overDec_sepWPp_mono_post overDec_sepWPp_seq overDec_sepWPp_weaken_pre
  payload_append_length_lt62_of_suffix prostChainGAt_move_chunks104_rc
  prostSSGQAt_eq_recv_sep_rest suffix_payload_of_suffix_enc_recv
  vecAt_recv_open_q_ext vecBuf_recv_full_open_rc_ext vecBuf_recv_not_full_open_rc_ext
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget (
  ChainMergeGenEnv fitsEnv_step_boundedRustEvs
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  AllocContractsPlaced growOne104Events growOneChainSpecX growOneChainStackX
  growOneChain_placed_ok_cl growOneChain_placed_ok_x
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemmoveBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushAPlacedBudget (
  growOne_plain_post_elim_sp_q_ext growOne_plain_pre_eq_q_ext
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudgetAux (
  OverDecRecvSegBEnv fitsEnv_growOne_of_segB overDecHeapPlBudget
  overDecRecvPostMergeHeapPlBudget overDecRecvSegBEnv_nil recv2114HeapPlacedBudget
  stackAt_sub_eq_pl step_2310_to_2114_of_ne_placed_budget step_2310_to_growOne_of_eq_placed_budget
  step_234c_to_2114_placed_budget step_from_2114_to_2160_full_pl_budget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  OverDecArmCroPlacedAtTR OverDecArmPlacedStmtTR OverDecEntryCroPlacedAt OverDecFieldCroPlacedAt
  OverDecFieldEnv OverDecHeadConsCroPlacedAt OverDecHeadNilCroPlacedAt OverDecKeyCroPlacedAt
  OverPrevDecodeCroPlacedAt OverPrevDecodeEnv OverPrevDecodePlacedStmt
  overDecEntry_cro_of_placed overDecHeadCons_cro_of_placed overDecHeadNil_cro_of_placed
  overDecHeapBudget sepWPp_lift_cro_regs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWPlacedBudget (
  BytesMerge6Placed514OkExtW
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6PlacedBudget (
  bytes_merge_6_placed_ok_w_cro
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.KeyPlacedBudget (
  overDecKey_cro_placed_of_alloc
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintPlacedBudget (
  overDecArm_varint_cro_placed_of_alloc
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmBytesPlacedBudget (
  overDecArm_bytes_cro_placed_at_of_bm6w
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudgetAux (
  ChainMerge5CroPlacedOkExt SepWPp_bind_sepWP_frame SepWPp_bind_sepWP_frame_cro
  SepWPp_call_frame_cro_noPanic SepWPp_ret_sepWP_frame SepWPp_weaken_frame
  chainMerge3RawSpecW fitsEnv_chainMergeGen_of_recv fitsEnv_chainMergeGen_of_sender
  fitsEnv_segB_of_recv overDecChain_segA_placed_budget overDecChain_segB_placed_budget
  overDecEntry_placed overDecFieldEnv_of_recv_chain_segB overDecFieldEnv_of_sender_chainMergeGen
  overDecHeadCons_placed overDecHeadNil_placed overDecHeap_eq_recv_split_ext
  overDecRecvFrameRestExt overDecRecvPostMergeHeap_eq_unsplit_ext
  overDecRecv_pre_step_80_placed_budget toChain3GTop
)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  OverPrevDecodePlacedStmt OverPrevDecodeCroPlacedAt OverPrevDecodeEnv
  OverDecFieldEnv
)
export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudgetAux (
  chainMerge3RawSpecW ChainMerge5CroPlacedOkExt
  overDecEntry_placed overDecHeadCons_placed overDecHeadNil_placed
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 1. Budget-Threaded `LibsignalCodeRoLoaded` Loop Composition -/

theorem overDecField_cro_of_key_arm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {P : GenFieldQ → Prop}
    (hK : OverDecKeyCroPlacedAt A lim ext)
    (hA : OverDecArmCroPlacedAtTR A lim ext P)
    (hPA : ∀ fl, P fl → OverDecAnyField fl) :
    OverDecFieldCroPlacedAt A lim ext P := by
  intro st s0 s g v fl rest hP hok hfr hsuf hlen hfit hregs
  refine overDec_sepWPp_seq (hK st s0 s g v fl rest (hPA fl hP) hok hsuf hlen hregs) ?_
  rintro sm Pm - - ⟨hregs', hx0, hx22, hent⟩
  exact overDec_sepWPp_weaken_pre hent
    (hA st s0 sm g v fl rest hP hok hfr hsuf hlen hfit hregs' hx0 hx22)

theorem overDecArm_cro_any [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hV : OverDecArmCroPlacedAtTR A lim ext OverDecVarintField)
    (hB : OverDecArmCroPlacedAtTR A lim ext OverDecBytesField)
    (hS : OverDecArmCroPlacedAtTR A lim ext OverDecSenderField)
    (hR : OverDecArmCroPlacedAtTR A lim ext OverDecRecvField) :
    OverDecArmCroPlacedAtTR A lim ext OverDecAnyField := by
  intro st s0 s g v fl rest hP
  rcases hP with h | h | h | h
  · exact hV st s0 s g v fl rest h
  · exact hB st s0 s g v fl rest h
  · exact hS st s0 s g v fl rest h
  · exact hR st s0 s g v fl rest h

theorem overDec_cro_loop [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hField : OverDecFieldCroPlacedAt A lim ext OverDecAnyField)
    (hCons : OverDecHeadConsCroPlacedAt A lim ext)
    (hNil : OverDecHeadNilCroPlacedAt A lim ext)
    (s0 : State) (g : OverDecG) (hlen : g.enc.length < 2 ^ 62) :
    ∀ (fs : List GenFieldQ) (st : M.σ) (v : SSGQ) (s : State), fs ≠ [] →
      (∀ fl ∈ fs, OverDecAnyField fl ∧ fl.Ok) → OverDecFreshChain fs v →
      fs.flatMap GenFieldQ.enc <:+ g.enc →
      FitsEnv M lim st (BoundedRustEvs (8 * (fs.flatMap GenFieldQ.enc).length)
        (256 * (g.enc.length + 16))) →
      OverDecRegsCroPlaced ext s0 g 0x216c#64 s →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 9760#64) s
        (overDecHeapBudget A lim st s g (fs.flatMap GenFieldQ.enc) v)
        (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2620#64 sf ∧
          ∃ evs, BoundedRustEvs (8 * (fs.flatMap GenFieldQ.enc).length)
              (256 * (g.enc.length + 16)) evs ∧
            (P_f ⊢ overDecHeapBudget A lim (M.stepEvents evs st) sf g []
              (fs.foldl SSGQ.apply v)))
        (fun _ _ => False) := by
  intro fs
  induction fs with
  | nil => intro st v s hne; exact absurd rfl hne
  | cons fl fs ih =>
    intro st v s _ hmem hfr hsuf hfit hregs
    have hfl := hmem fl (List.mem_cons_self ..)
    obtain ⟨hfr1, hfr2⟩ := overDecFreshChain_cons_inv hfr
    rw [overDec_flatMap_cons] at hsuf hfit ⊢
    have hfl_le_enc : fl.enc.length ≤ g.enc.length := by
      rcases hsuf with ⟨pfx, hpfx⟩
      have := congrArg List.length hpfx
      rw [List.length_append, List.length_append] at this
      omega
    have hfit_fl : FitsEnv M lim st (OverDecFieldEnv fl) := by
      intro evs hevs
      unfold OverDecFieldEnv at hevs
      rw [List.length_append] at hfit
      exact hfit evs (BoundedRustEvs.mono (by omega) (by omega) hevs)
    refine overDec_sepWPp_seq
      (hField st s0 s g v fl _ hfl.1 hfl.2 hfr1 hsuf hlen hfit_fl hregs) ?_
    rintro sm Pm - - ⟨hregsm, evs₁, hevs₁, hentm⟩
    refine overDec_sepWPp_weaken_pre hentm ?_
    have hsuf' : fs.flatMap GenFieldQ.enc <:+ g.enc :=
      List.IsSuffix.trans (List.suffix_append _ _) hsuf
    rcases fs with _ | ⟨fl', fs'⟩
    · refine overDec_sepWPp_mono_post ?_
        (hNil (M.stepEvents evs₁ st) s0 sm g (v.apply fl) hlen hregsm)
      rintro sf P_f - - ⟨hregsf, hentf⟩
      refine ⟨hregsf, evs₁, ?_, hentf⟩
      unfold OverDecFieldEnv at hevs₁
      simp only [List.flatMap_nil, List.append_nil]
      exact BoundedRustEvs.mono (Nat.le_refl _) (by omega) hevs₁
    · have hne : (fl' :: fs').flatMap GenFieldQ.enc ≠ [] := by
        rw [overDec_flatMap_cons]
        intro h
        exact overDec_enc_ne_nil fl' (List.append_eq_nil_iff.mp h).1
      have hfit_rest : FitsEnv M lim (M.stepEvents evs₁ st)
          (BoundedRustEvs (8 * ((fl' :: fs').flatMap GenFieldQ.enc).length)
            (256 * (g.enc.length + 16))) := by
        unfold OverDecFieldEnv at hevs₁
        rw [List.length_append] at hfit
        exact fitsEnv_step_boundedRustEvs hevs₁ (by omega) (by omega) (Nat.le_refl _) hfit
      refine overDec_sepWPp_seq
        (hCons (M.stepEvents evs₁ st) s0 sm g (v.apply fl) _ hne hsuf' hlen hregsm) ?_
      rintro sn Pn - - ⟨hregsn, hentn⟩
      refine overDec_sepWPp_weaken_pre hentn ?_
      refine overDec_sepWPp_mono_post ?_
        (ih (M.stepEvents evs₁ st) (v.apply fl) sn (List.cons_ne_nil _ _)
          (fun f hf => hmem f (List.mem_cons_of_mem _ hf)) hfr2 hsuf' hfit_rest hregsn)
      rintro sf P_f - - ⟨hregsf, evs₂, hevs₂, hentf⟩
      refine ⟨hregsf, evs₁ ++ evs₂, ?_, ?_⟩
      · unfold OverDecFieldEnv at hevs₁
        rw [List.length_append]
        exact BoundedRustEvs.mono (by omega) (Nat.max_le.mpr ⟨by omega, Nat.le_refl _⟩)
          (BoundedRustEvs.append hevs₁ hevs₂)
      · rw [M.stepEvents_append]
        exact hentf

theorem overDec_cro_after_entry [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hField : OverDecFieldCroPlacedAt A lim ext OverDecAnyField)
    (hCons : OverDecHeadConsCroPlacedAt A lim ext)
    (hNil : OverDecHeadNilCroPlacedAt A lim ext)
    (st0 : M.σ) (s0 sm : State) (g : OverDecG) (sess : Session (List (BitVec 8)))
    (hencfs : g.enc = (genFieldsQ sess).flatMap GenFieldQ.enc)
    (hlen : g.enc.length < 2 ^ 62) (hfsne : genFieldsQ sess ≠ [])
    (hmem : ∀ fl ∈ genFieldsQ sess, OverDecAnyField fl ∧ fl.Ok)
    (hfresh : OverDecFreshChain (genFieldsQ sess) SSGQ.empty)
    (hfold : (genFieldsQ sess).foldl SSGQ.apply SSGQ.empty = ssgqOf sess)
    (hFit : FitsEnv M lim st0 (OverPrevDecodeEnv g.enc))
    (hregsm : OverDecRegsCroPlaced ext s0 g 0x216c#64 sm) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 9760#64) sm
      (overDecHeapBudget A lim st0 sm g g.enc SSGQ.empty)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2620#64 sf ∧
        ∃ evs, OverPrevDecodeEnv g.enc evs ∧
          (P_f ⊢ overDecHeapBudget A lim (M.stepEvents evs st0) sf g [] (ssgqOf sess)))
      (fun _ _ => False) := by
  have hsuf : (genFieldsQ sess).flatMap GenFieldQ.enc <:+ g.enc := by
    rw [← hencfs]
  have hfit_fs : FitsEnv M lim st0
      (BoundedRustEvs (8 * ((genFieldsQ sess).flatMap GenFieldQ.enc).length)
        (256 * (g.enc.length + 16))) := by
    rw [← hencfs]
    intro evs hevs
    exact hFit evs (BoundedRustEvs.mono (by omega) (Nat.le_refl _) hevs)
  have hloop := overDec_cro_loop hField hCons hNil s0 g hlen (genFieldsQ sess)
    st0 SSGQ.empty sm hfsne hmem hfresh hsuf hfit_fs hregsm
  rw [← hencfs, hfold] at hloop
  refine overDec_sepWPp_mono_post ?_ hloop
  rintro sf P_f - - ⟨hregsf, evs, hevs, hentf⟩
  refine ⟨hregsf, evs, BoundedRustEvs.mono (by omega) (Nat.le_refl _) hevs, hentf⟩

private theorem overPrevElemAtBudget_eq_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (prevCap prevPtr encCap encPtr : BitVec 64) (enc : List (BitVec 8)) :
    LoopDefsBudget.overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.overPrevElemAtExt
        (A.atState lim st s) prevCap prevPtr encCap encPtr enc :=
  rfl

private theorem overDecScratchPostBudget_eq_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (q : BitVec 64) (v : SSGQ) :
    LoopDefsBudget.overDecScratchPostBudget A q v =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.overDecScratchPostExt
        (A.atState lim st s) q v :=
  rfl

theorem overPrevDecode_cro_of_steps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hEntry : OverDecEntryCroPlacedAt A lim ext)
    (hField : OverDecFieldCroPlacedAt A lim ext OverDecAnyField)
    (hCons : OverDecHeadConsCroPlacedAt A lim ext)
    (hNil : OverDecHeadNilCroPlacedAt A lim ext) :
    OverPrevDecodeCroPlacedAt A lim ext := by
  intro st0 s0 s prevCap prevPtr encCap encPtr enc sess hok hFit hcro hcl hpc hrun
    hal htr hx21 hx24 hx25 hx27 hx29
  obtain ⟨henc, hscope, hver, hpp, hpk⟩ := hok
  have hencfs : enc = (genFieldsQ sess).flatMap GenFieldQ.enc :=
    henc.trans (overDec_encSession_eq sess hscope)
  have hfsne := overDec_genFieldsQ_ne_nil sess hver
  have hne : enc ≠ [] := hencfs ▸ overDec_flatMap_ne_nil _ hfsne
  have hlen : enc.length < 2 ^ 62 := henc ▸ overDec_encSession_length_lt sess hscope
  let g0 : OverDecG :=
    ⟨s.sp, s.readReg64 .x19, s.readReg64 .x20, s.readReg64 .x26,
     prevCap, prevPtr, encCap, encPtr, enc, s⟩
  have hEntry' := hEntry st0 s0 s g0 hne hlen hcro hcl hpc hrun rfl hal htr
    rfl rfl rfl hx21 hx24 hx25 hx27 hx29 rfl
  refine overDec_sepWPp_seq hEntry' ?_
  rintro sm Pm - - ⟨hregsm, hentm⟩
  refine overDec_sepWPp_weaken_pre hentm ?_
  refine overDec_sepWPp_mono_post ?_ (overDec_cro_after_entry hField hCons hNil st0 s0
    sm g0 sess hencfs hlen hfsne (overDec_mem_genFieldsQ sess hscope hpp hpk)
    (overDec_freshChain_genFieldsQ sess hscope) (overDec_fold_genFieldsQ sess hscope)
    hFit hregsm)
  rintro sf P_f - - ⟨⟨hcrof, -, -, hsp, -, htrf, hclf, h19, h20, h26, h21, h24, h25, h27, -, h29,
      hvregsf⟩, evs, hevs, hentf⟩
  have hexit :
      overDecHeapBudget A lim (M.stepEvents evs st0) sf g0 [] (ssgqOf sess) ⊢
        LoopDefsBudget.overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ∗
          LoopDefsBudget.overDecScratchPostBudget A s.sp (ssgqOf sess) ∗
          stackAt s.sp overDecStackX ∗
          A.pool lim (M.stepEvents evs st0) sf ∗ anyHeap := by
    rw [LoopDefsBudget.overDecHeapBudget_eq_atState,
        overPrevElemAtBudget_eq_atState A lim (M.stepEvents evs st0) sf,
        overDecScratchPostBudget_eq_atState A lim (M.stepEvents evs st0) sf]
    exact overDec_exit_ext (A := A.atState lim (M.stepEvents evs st0) sf) g0 (ssgqOf sess) hne
  exact ⟨⟨evs, hevs, Entails.trans hentf hexit⟩,
    hsp, htrf, hcrof, hclf, h19, h20, h21, h24, h25, h26, h27, h29, hvregsf⟩

theorem overPrevDecode_cro_of_key_arms [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hEntry : OverDecEntryCroPlacedAt A lim ext)
    (hCons : OverDecHeadConsCroPlacedAt A lim ext)
    (hNil : OverDecHeadNilCroPlacedAt A lim ext)
    (hKey : OverDecKeyCroPlacedAt A lim ext)
    (hVarint : OverDecArmCroPlacedAtTR A lim ext OverDecVarintField)
    (hBytes : OverDecArmCroPlacedAtTR A lim ext OverDecBytesField)
    (hSender : OverDecArmCroPlacedAtTR A lim ext OverDecSenderField)
    (hRecv : OverDecArmCroPlacedAtTR A lim ext OverDecRecvField) :
    OverPrevDecodeCroPlacedAt A lim ext :=
  overPrevDecode_cro_of_steps hEntry
    (overDecField_cro_of_key_arm hKey
      (overDecArm_cro_any hVarint hBytes hSender hRecv) (fun _ h => h))
    hCons hNil

theorem overPrevDecode_placed_of_key_arms [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hEntry : ∀ ext, OverDecEntryCroPlacedAt A lim ext)
    (hCons : ∀ ext, OverDecHeadConsCroPlacedAt A lim ext)
    (hNil : ∀ ext, OverDecHeadNilCroPlacedAt A lim ext)
    (hKey : ∀ ext, OverDecKeyCroPlacedAt A lim ext)
    (hVarint : OverDecArmPlacedStmtTR A lim OverDecVarintField)
    (hBytes : OverDecArmPlacedStmtTR A lim OverDecBytesField)
    (hSender : OverDecArmPlacedStmtTR A lim OverDecSenderField)
    (hRecv : OverDecArmPlacedStmtTR A lim OverDecRecvField) :
    OverPrevDecodePlacedStmt A lim :=
  fun ext => overPrevDecode_cro_of_key_arms (hEntry ext) (hCons ext) (hNil ext) (hKey ext)
    (hVarint ext) (hBytes ext) (hSender ext) (hRecv ext)

/-! ## 2. Budget-Threaded Tag-6 (`sender_chain`) Arm (`+0x2214 → +0x2160`) -/

private theorem prostChainGAt_repAlloc_eq_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a : BitVec 64) (c : ChainG) :
    prostChainGAt A.repAlloc a c = prostChainGAt (A.atState lim st s) a c :=
  rfl

private theorem overDecChainFrameExt_atState_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st₁ st₂ : M.σ) (s₁ s₂ : State)
    (g : CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.OverDecG)
    (pfx : List (BitVec 8)) (v : SSGQ) :
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overDecChainFrameExt
      (A.atState lim st₁ s₁) g pfx v =
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overDecChainFrameExt
      (A.atState lim st₂ s₂) g pfx v :=
  rfl

set_option maxHeartbeats 600000 in
/-- Tag 6 (`sender_chain`), `+0x2214 → +0x2160`, on `lsProg_518 ext` under `LibsignalCodeRoLoaded`. -/
theorem overDecArmSender_cro_core [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hC5 : ChainMerge5CroPlacedOkExt A lim ext)
    (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (hcok : c.Ok) (hnone : v.base.sender = none)
    (hsuf : ((GenFieldQ.base (.sender c)).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hfit : FitsEnv M lim st (OverDecFieldEnv (.base (.sender c))))
    (hregs : OverDecRegsCroPlaced ext s0 g 0x2214#64 s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
      (overDecHeapBudget A lim st s g ((GenFieldQ.base (.sender c)).payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        ∃ evs, OverDecFieldEnv (.base (.sender c)) evs ∧
          (P_f ⊢ overDecHeapBudget A lim (M.stepEvents evs st) sf g rest
            ⟨v.base.apply (.sender c), v.ext⟩))
      (fun _ _ => False) := by
  rcases hregs with ⟨hcro, hpc, hrun, hsp, hal, htr, _hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  refine sepWPp_lift_cro_regs hcro ?_
  obtain ⟨pfx, hpfx, hpay_len⟩ := overDecChain_payload_suffix hsuf hlen
  have hheap_eq :
      overDecHeapBudget A lim st s g ((GenFieldQ.base (.sender c)).payload ++ rest) v =
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overDecHeapExt
          (A.atState lim st s) (toChain3GTop g)
          ((GenFieldQ.base (.sender c)).payload ++ rest) v := rfl
  rw [hheap_eq,
      overDecChain_heap_pre_ext (A.atState lim st s) (toChain3GTop g) v pfx _ rest hpfx hnone,
      overDecChain_mem96 g.q]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun u9 => SepWPp.exists_elim fun u8 => SepWPp.exists_elim fun u7 =>
    SepWPp.exists_elim fun u6 => SepWPp.exists_elim fun u5 => SepWPp.exists_elim fun u4 =>
    SepWPp.exists_elim fun u3 => SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u1 => ?_
  have hstepA :=
    overDecChain_segA_placed_budget A lim st ext s g.q u1 u2 u3 u4 u5 u6 u7 u8 u9
      hpc hrun hsp hal hx0 hx21 hx24 hx25 hx29
  change _ at hstepA
  refine SepWPp_bind_sepWP_frame_cro hcro hstepA
    (by dsimp only [RustCliAllocBudget.atState, toChain3GTop]; sep_focus)
    fun s1 hpc1 hrun1 _hcl1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
  refine SepWPp_weaken_frame (overDecChain_bridge_ext A.repAlloc g.q)
    (by sep_focus) ?_
  have hsp1q : s1.sp = g.q := hsp1.trans hsp
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, hal]
  have hx0_w8 : (s1.readReg64 .x0).setWidth 8 = 2#8 := by rw [hx0_1]; rfl
  let xGhost : ChainMergeGenGhost :=
    ⟨g.q + 0x9c0#64, c, g.q + 0xbe8#64, g.q + 0x920#64,
     g.encPtr + BitVec.ofNat 64 pfx.length, rest⟩
  have hfit_cm : FitsEnv M lim st (ChainMergeGenEnv xGhost) :=
    fitsEnv_chainMergeGen_of_sender hfit
  refine SepWPp_call_frame_cro_noPanic
    (x := (xGhost, st))
    (φ := (s1.readReg64 .x0).setWidth 8 = 2#8 ∧ s1.readReg64 .x1 = g.q + 0x9c0#64 ∧
      s1.readReg64 .x2 = g.q + 0xbe8#64 ∧ c.Ok ∧ (c.payload ++ rest).length < 2 ^ 62 ∧
      FitsEnv M lim st (ChainMergeGenEnv xGhost))
    (T := chain3GAt A.repAlloc (g.q + 0x9c0#64) ChainG.empty ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
        (c.payload ++ rest) ∗
      A.pool lim st s1 ∗
      stackAt g.q chainMerge3StackX)
    hcro1 hC5 hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [chainMerge3RawSpecW, xGhost]; rw [hsp1q])
    ⟨hx0_w8, hx1_1, hx2_1, hcok, hpay_len, hfit_cm⟩
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 _hcl2 _hcro2 => ?_)
  dsimp only [chainMerge3RawSpecW, xGhost]
  apply SepWPp_exists_left_rc; intro evs
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; rintro ⟨htr2_1, hx0_2, hevs⟩
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1q
  have htr2 : s2.trace = s0.trace := htr2_1.trans (htr1.trans htr)
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs, hvregs_cs⟩
  have hstepB :=
    overDecChain_segB_placed_budget A lim (M.stepEvents evs st) ext s2 g.q g.r19 g.r20 g.r26 g.prevPtr
      hpc2 hrun2 hsp2 hx0_2
      ((hx19_cs.trans hx19_1).trans hx19) ((hx20_cs.trans hx20_1).trans hx20)
      ((hx21_cs.trans hx21_1).trans hx21) ((hx24_cs.trans hx24_1).trans hx24)
      ((hx25_cs.trans hx25_1).trans hx25) ((hx26_cs.trans hx26_1).trans hx26)
      ((hx27_cs.trans hx27_1).trans hx27) ((hx28_cs.trans hx28_1).trans hx28)
      ((hx29_cs.trans hx29_1).trans hx29)
  refine SepWPp_ret_sepWP_frame hstepB (by sep_focus)
    fun sf hpcf hrunf hclf hregsf => ?_
  rcases hregsf with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f,
    hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr2, hclf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f,
    ((hvregs_f.trans hvregs_cs).trans hvregs_1).trans hvregs⟩,
    evs, overDecFieldEnv_of_sender_chainMergeGen (x := xGhost) hevs, ?_⟩
  have hpay_s : (GenFieldQ.base (.sender c)).payload = c.payload := rfl
  have hpfx' : (toChain3GTop g).enc = pfx ++ (c.payload ++ rest) := by
    simpa only [hpay_s] using hpfx
  have hpost_eq :
      overDecHeapBudget A lim (M.stepEvents evs st) sf g rest ⟨v.base.apply (.sender c), v.ext⟩ =
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overDecHeapExt
          (A.atState lim (M.stepEvents evs st) sf) (toChain3GTop g) rest
          ⟨v.base.apply (.sender c), v.ext⟩ := rfl
  have hframe_eq :
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overDecChainFrameExt
        (A.atState lim st s) (toChain3GTop g) pfx v =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overDecChainFrameExt
        (A.atState lim (M.stepEvents evs st) sf) (toChain3GTop g) pfx v :=
    overDecChainFrameExt_atState_eq A lim st (M.stepEvents evs st) s sf (toChain3GTop g) pfx v
  have hto_q : (toChain3GTop g).q = g.q := rfl
  have hto_ep : (toChain3GTop g).encPtr = g.encPtr := rfl
  rw [hpost_eq,
      ← overDecChain_heap_post_ext (A.atState lim (M.stepEvents evs st) sf)
          (toChain3GTop g) v c pfx c.payload rest hpfx',
      ← hframe_eq, hsp1q,
      prostChainGAt_repAlloc_eq_atState A lim (M.stepEvents evs st) sf,
      RustCliAllocBudget.atState_pool, hto_q, hto_ep]
  exact Entails.of_eq (by sep_ac_rfl)

theorem overDecArmSender_cro_placed_of_chain5 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hC5 : ChainMerge5CroPlacedOkExt A lim ext) :
    OverDecArmCroPlacedAtTR A lim ext OverDecSenderField := by
  intro st s0 s g v fl rest hP hok hfresh hsuf hlen hfit hregs hx0 _hx22
  cases fl
  case base f =>
    cases f
    case sender c =>
      have hok' : c.Ok ∧ c.priv.length = 32 ∧ c.ck.isSome = true ∧ c.keys = [] := hok
      have hfresh' : v.ext = ExtraGQ.empty ∧ v.base.sender = none := hfresh
      exact overDecArmSender_cro_core ext hC5 st s0 s g v c rest
        hok'.1 hfresh'.2 hsuf hlen hfit hregs hx0
    all_goals exact False.elim hP
  all_goals exact False.elim hP

theorem overDecArmSender_placed_of_chain5 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hC5 : ∀ ext, ChainMerge5CroPlacedOkExt A lim ext) :
    OverDecArmPlacedStmtTR A lim OverDecSenderField :=
  fun ext => overDecArmSender_cro_placed_of_chain5 (hC5 ext)

/-! ## 3. Budget-Threaded Tag-7 (`receiver_chains`) Arm (`+0x22e0 → +0x2160`) -/

set_option maxHeartbeats 800000 in
/-- Budget-threaded Segment B (`(blkPl_518).base + 0x2310 → +0x2160`) of the tag-7
(`receiver_chains`) arm under `LibsignalCodeRoLoaded`, parameterized by `hGrow` at `lsmpl.base 43`. -/
theorem overDecRecv_segB_cro_placed_of_grow [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 43)
      (withLsCodeRoLoaded lsmpl (growOneChainSpecX M A lim)))
    (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (_hOk : (GenFieldQ.base (.recv c)).Ok)
    (hFresh : (GenFieldQ.base (.recv c)).Fresh v)
    (_hsuf : ((GenFieldQ.base (.recv c)).enc ++ rest) <:+ g.enc)
    (_hlen : g.enc.length < 2 ^ 62)
    (hfit : FitsEnv M lim st (OverDecRecvSegBEnv v.base.recv.length))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hregs : OverDecRegsPlaced ext s0 g 0x2310#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (overDecRecvPostMergeHeapPlBudget A lim st s g rest v c)
      (fun sf P_f => ∃ evs : List AllocEvent,
        OverDecRecvSegBEnv v.base.recv.length evs ∧
        OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapPlBudget A lim (M.stepEvents evs st) sf g rest
          (v.apply (.base (.recv c)))))
      (fun _ _ => False) := by
  have hfresh : v.base.recv.length < maxReceiverChains := hFresh.2
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hCL,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  unfold overDecRecvPostMergeHeapPlBudget
  rw [prostSSGQAt_eq_recv_sep_rest A.repAlloc (g.q + 0x930#64) v,
      memRegion344_a90_split_rc g.q]
  refine SepWPp_weaken_frame (vecAt_recv_open_q_ext A.repAlloc g.q v.base.recv)
    (by sep_focus) ?_
  apply SepWPp_exists_left_rc; intro cap
  apply SepWPp_exists_left_rc; intro ptr
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; rintro ⟨hlen_le, hcap_lt, hptr⟩
  refine SepWPp_weaken_frame (prostChainGAt_move_chunks104_rc A.repAlloc (g.q + 0xbf0#64) c)
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i q0 q1 q2 q3 q4 q5 w6 H_c
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; intro hmov_c
  refine SepWPp_weaken_frame
    (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_rc (g.q + 0xa90#64)))
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i d0 d1 d2 d3 d4 d5 dw6
  by_cases hfull : v.base.recv.length = cap.toNat
  · refine SepWPp_weaken_frame (vecBuf_recv_full_open_rc_ext A.repAlloc cap ptr v.base.recv hfull)
      (by sep_focus) ?_
    apply SepWPp_exists_left_rc; intro bs
    apply SepWPp_exists_left_rc; intro H_arr
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hbs_len, hmov_arr⟩
    simp only [A.repAlloc_live_norm]
    have hlen_cap : BitVec.ofNat 64 v.base.recv.length = cap := ofNat_length_eq_cap_of_eq_rc hfull
    have hmax_lt : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by
      have h5 : maxReceiverChains = 5 := rfl
      omega
    have hfit_grow := fitsEnv_growOne_of_segB hfull hfit
    rw [hlen_cap]
    have hstep1 := step_2310_to_growOne_of_eq_placed_budget A lim st ext s g cap
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame_cro hcro hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 _hCLs1 hcro1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx0s1, hlrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    have hals1 : s1.spAligned = true := by
      simp only [State.spAligned]
      rwa [hsps1, ← hsp]
    rw [stackAt_sub_eq_pl g.q overDecStackX growOneChainStackX]
    refine SepWPp_weaken_frame (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_call_frame_cro_noPanic
      (x := ((g.q + 0x978#64, cap, ptr, bs), st))
      hcro1 hGrow hpcs1 hruns1 hals1 hlrs1
      (growOne_plain_pre_eq_q_ext A lim st g.q cap ptr bs s1 hsps1)
      ⟨hbs_len, hx0s1, hptr, hmax_lt, hfit_grow⟩
      (by sep_focus)
      (hnext := fun sm hpcm hrunm hspm _halm hcsm _hCLm _hcrom => ?_)
    obtain ⟨hx19m, hx20m, hx21m, hx22m, _, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
    rw [hx19s1] at hx19m; rw [hx20s1] at hx20m; rw [hx21s1] at hx21m; rw [hx22s1] at hx22m
    rw [hx24s1] at hx24m; rw [hx25s1] at hx25m; rw [hx26s1] at hx26m; rw [hx27s1] at hx27m
    rw [hx28s1] at hx28m; rw [hx29s1] at hfpm; rw [hsps1] at hspm
    refine SepWPp_weaken_frame
      (growOne_plain_post_elim_sp_q_ext A lim st g.q cap ptr v.base.recv bs s1 sm hsps1 hfull hfresh hbs_len)
      rfl ?_
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; intro htrm
    have htrm' : sm.trace = s0.trace := htrm.trans (htrs1.trans htr)
    apply SepWPp_exists_left_rc; intro cap'
    apply SepWPp_exists_left_rc; intro p'
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hlt_cap', hcap_lt', hp'⟩
    refine SepWPp_weaken_frame (hmov_arr p') (by sep_focus) ?_
    have hstep2 := step_234c_to_2114_placed_budget A lim (M.stepEvents (growOne104Events cap) st) ext sm g cap
      hpcm hrunm hspm hx19m hx20m hx21m hx22m hx24m hx25m hx26m hx27m hx28m hfpm
    refine SepWPp_bind_sepWP_frame hstep2 (by sep_focus)
      fun s2 hpcs2 hruns2 hCLs2 hpost2 => ?_
    rcases hpost2 with ⟨hsps2, htrs2, hx19s2, hx20s2, hx21s2, hx22s2,
      hx24s2, hx25s2, hx26s2, hx27s2, hx28s2, hx29s2, hvregss2⟩
    have hals2 : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsps2, ← hsp]
    rw [← hlen_cap] at hx22s2 ⊢
    have hregs2 : OverDecRegsPlaced ext s0 g 0x2114#64 s2 :=
      ⟨hpcs2, hruns2, hsps2, hals2, htrs2.trans htrm', hCLs2,
       hx19s2, hx20s2, hx26s2, hx21s2, hx24s2, hx25s2, hx27s2, hx28s2, hx29s2,
       ((hvregss2.trans hvregsm).trans hvregss1).trans hvregs⟩
    refine SepWPp_weaken_frame
      (P₂ := recv2114HeapPlacedBudget A lim
        (M.stepEvents (growOne104Events (BitVec.ofNat 64 v.base.recv.length)) st)
        s2 g rest v cap' p' q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq ?_) (sepConj_emp _).symm ?_
    · unfold recv2114HeapPlacedBudget
      rw [stackAt_sub_eq_pl g.q overDecStackX growOneChainStackX]
      sep_ac_rfl
    · rw [sepConj_emp]
      refine overDec_sepWPp_mono_post ?_
        (step_from_2114_to_2160_full_pl_budget A lim
          (M.stepEvents (growOne104Events (BitVec.ofNat 64 v.base.recv.length)) st)
          ext s0 s2 g v c rest cap' p' q0 q1 q2 q3 q4 q5 w6 H_c
          hlt_cap' hcap_lt' hp' hmov_c hregs2 hx22s2)
      rintro sf P_f - - ⟨hregsf, hentf⟩
      exact ⟨growOne104Events (BitVec.ofNat 64 v.base.recv.length), Or.inr rfl, hregsf, hentf⟩
  · have hlt : v.base.recv.length < cap.toNat := by omega
    have hne : BitVec.ofNat 64 v.base.recv.length ≠ cap := len_ne_cap_of_lt_rc hlt
    rw [vecBuf_recv_not_full_open_rc_ext A.repAlloc cap ptr v.base.recv hlt hcap_lt]
    simp only [A.repAlloc_live_norm]
    have hstep1 := step_2310_to_2114_of_ne_placed_budget A lim st ext s g cap
      (BitVec.ofNat 64 v.base.recv.length)
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hne hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 hCLs1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    have hals1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsps1, ← hsp]
    have hregs1 : OverDecRegsPlaced ext s0 g 0x2114#64 s1 :=
      ⟨hpcs1, hruns1, hsps1, hals1, htrs1.trans htr, hCLs1,
       hx19s1, hx20s1, hx26s1, hx21s1, hx24s1, hx25s1, hx27s1, hx28s1, hx29s1,
       hvregss1.trans hvregs⟩
    refine SepWPp_weaken_frame (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_weaken_frame
      (P₂ := recv2114HeapPlacedBudget A lim st s1 g rest v cap ptr q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq (by unfold recv2114HeapPlacedBudget; sep_ac_rfl))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    refine overDec_sepWPp_mono_post ?_
      (step_from_2114_to_2160_full_pl_budget A lim st ext s0 s1 g v c rest cap ptr
        q0 q1 q2 q3 q4 q5 w6 H_c hlt hcap_lt hptr hmov_c hregs1 hx22s1)
    rintro sf P_f - - ⟨hregsf, hentf⟩
    exact ⟨[], overDecRecvSegBEnv_nil v.base.recv.length, hregsf, hentf⟩

private theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCl [LibsignalPlacement]
    {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCl lsmpl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hp
      dsimp only [withLsCl]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hfr.1, hpre⟩)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCl] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

theorem overDecRecv_segB_cro_placed_of_alloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext) :
    ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8)),
      (GenFieldQ.base (.recv c)).Ok →
      (GenFieldQ.base (.recv c)).Fresh v →
      ((GenFieldQ.base (.recv c)).enc ++ rest) <:+ g.enc →
      g.enc.length < 2 ^ 62 →
      FitsEnv M lim st (OverDecRecvSegBEnv v.base.recv.length) →
      LibsignalCodeRoLoaded lsmpl s.mem →
      OverDecRegsPlaced ext s0 g 0x2310#64 s →
      s.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
        (overDecRecvPostMergeHeapPlBudget A lim st s g rest v c)
        (fun sf P_f => ∃ evs : List AllocEvent,
          OverDecRecvSegBEnv v.base.recv.length evs ∧
          OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
          (P_f ⊢ overDecHeapPlBudget A lim (M.stepEvents evs st) sf g rest
            (v.apply (.base (.recv c)))))
        (fun _ _ => False) :=
  overDecRecv_segB_cro_placed_of_grow
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCl
      (growOneChain_placed_ok_cl (callerProg := lsProg_518 ext) (growOneChain_placed_ok_x hAlloc)))

private theorem recv_cells_pool_reassoc
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 pool m24 restF : SepProp) :
    (c0 ∗ c1 ∗ c2 ∗ c3 ∗ c4 ∗ c5 ∗ c6 ∗ c7 ∗ c8 ∗ c9 ∗ pool) ∗ (m24 ∗ restF) =
      ((c0 ∗ c1 ∗ c2 ∗ c3 ∗ c4 ∗ c5 ∗ c6 ∗ c7 ∗ c8 ∗ c9) ∗ m24) ∗ (pool ∗ restF) := by
  sep_ac_rfl

private theorem recv_call_frame_reassoc (ch pool hbe8 cur stk restF : SepProp) :
    ch ∗ (pool ∗ (hbe8 ∗ cur ∗ stk ∗ restF)) = (ch ∗ hbe8 ∗ cur ∗ pool ∗ stk) ∗ restF := by
  sep_ac_rfl

private theorem overDecHeapPlBudget_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : OverDecG) (rest : List (BitVec 8)) (w : SSGQ) :
    overDecHeapPlBudget A lim st s g rest w = overDecHeapBudget A lim st s g rest w :=
  rfl

set_option maxHeartbeats 600000 in
/-- Tag 7 (`receiver_chains`), `+0x22e0 → +0x2160`, on `lsProg_518 ext` under `LibsignalCodeRoLoaded`. -/
theorem overDecArmRecv_cro_core [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 43)
      (withLsCodeRoLoaded lsmpl (growOneChainSpecX M A lim)))
    (hChain5 : ChainMerge5CroPlacedOkExt A lim ext)
    (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (hok : (GenFieldQ.base (.recv c)).Ok)
    (hfresh : (GenFieldQ.base (.recv c)).Fresh v)
    (hsuf : ((GenFieldQ.base (.recv c)).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hfit : FitsEnv M lim st (OverDecFieldEnv (.base (.recv c))))
    (hregs_cro : OverDecRegsCroPlaced ext s0 g 0x22e0#64 s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (overDecHeapBudget A lim st s g ((GenFieldQ.base (.recv c)).payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        ∃ evs, OverDecFieldEnv (.base (.recv c)) evs ∧
          (P_f ⊢ overDecHeapBudget A lim (M.stepEvents evs st) sf g rest
            (v.apply (.base (.recv c)))))
      (fun _ _ => False) := by
  rcases hregs_cro with ⟨hcro, hregs⟩
  refine sepWPp_lift_cro_regs hcro ?_
  have hpay_eq : (GenFieldQ.base (.recv c)).payload = c.payload := rfl
  have hc_ok : c.Ok := hok.1
  have hrecv_lt : v.base.recv.length < maxReceiverChains := hfresh.2
  have hsuf_pay : (c.payload ++ rest) <:+ g.enc := by
    rw [← hpay_eq]; exact suffix_payload_of_suffix_enc_recv hsuf
  have hlen_pay : (c.payload ++ rest).length < 2 ^ 62 :=
    payload_append_length_lt62_of_suffix hsuf_pay hlen
  rw [hpay_eq, overDecHeap_eq_recv_split_ext A lim st s g v hsuf_pay]
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hCL,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have hsaved : OverDecSavedRegs (toChain3GTop g) s :=
    ⟨hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have hq_align : (g.q &&& 15#64 == 0#64) = true := by rwa [← hsp]
  have hstep := overDecRecv_pre_step_80_placed_budget A lim st (ext := ext) (g := toChain3GTop g)
    hpc hrun hsp hsp_align htr hsaved hx0
  refine SepWPp_bind_sepWP_frame_cro hcro hstep rfl
    fun s1 hpc1 hrun1 _hCL1 hcro1 ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1, hsaved1⟩ => ?_
  dsimp only [toChain3GTop] at hsp1 hx1_1 hx2_1 ⊢
  refine SepWPp_weaken_frame (default_cells_bf0_entail_chain3GAt_ext A.repAlloc g.q)
    (recv_cells_pool_reassoc _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, hq_align]
  have hx0_1_w8 : (s1.readReg64 .x0).setWidth 8 = 2#8 := by rw [hx0_1]; rfl
  let xGhost : ChainMergeGenGhost :=
    ⟨g.q + 0xbf0#64, c, g.q + 0xbe8#64, g.q + 0x920#64,
     g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length), rest⟩
  have hfit_cm : FitsEnv M lim st (ChainMergeGenEnv xGhost) :=
    fitsEnv_chainMergeGen_of_recv (x := xGhost) hfit
  refine SepWPp_call_frame_cro_noPanic
    (x := (xGhost, st))
    (φ := (s1.readReg64 .x0).setWidth 8 = 2#8 ∧ s1.readReg64 .x1 = g.q + 0xbf0#64 ∧
      s1.readReg64 .x2 = g.q + 0xbe8#64 ∧ c.Ok ∧ (c.payload ++ rest).length < 2 ^ 62 ∧
      FitsEnv M lim st (ChainMergeGenEnv xGhost))
    (T := chain3GAt A.repAlloc (g.q + 0xbf0#64) ChainG.empty ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
        (c.payload ++ rest) ∗
      A.pool lim st s1 ∗
      stackAt g.q chainMerge3StackX)
    (F := overDecRecvFrameRestExt A.repAlloc g v (c.payload ++ rest).length)
    hcro1 hChain5 hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [chainMerge3RawSpecW, xGhost]; rw [hsp1])
    ⟨hx0_1_w8, hx1_1, hx2_1, hc_ok, hlen_pay, hfit_cm⟩
    (recv_call_frame_reassoc _ _ _ _ _ _)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 hCL2 hcro2 => ?_)
  dsimp only [chainMerge3RawSpecW]
  rw [hsp1]
  apply SepWPp_exists_left_rc; intro evs₁
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; rintro ⟨htr2_1, hx0_2, hevs₁⟩
  dsimp only [xGhost]
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hq_align
  have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
  rcases hsaved1 with ⟨hx19_1, hx20_1, hx26_1, hx21_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs, hvregs_cs⟩
  have hregs2 : OverDecRegsPlaced ext s0 g 0x2310#64 s2 :=
    ⟨hpc2, hrun2, hsp2, hsp2_align, htr2, hCL2,
     hx19_cs.trans hx19_1, hx20_cs.trans hx20_1, hx26_cs.trans hx26_1,
     hx21_cs.trans hx21_1, hx24_cs.trans hx24_1, hx25_cs.trans hx25_1,
     hx27_cs.trans hx27_1, hx28_cs.trans hx28_1, hx29_cs.trans hx29_1,
     hvregs_cs.trans hvregs_1⟩
  have hpost_eq :
      (prostChainGAt A.repAlloc (g.q + 0xbf0#64) c ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAfter (g.q + 0x920#64)
          (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
          (c.payload ++ rest) rest ∗
        A.pool lim (M.stepEvents evs₁ st) s2 ∗
        stackAt g.q chainMerge3StackX) ∗
      overDecRecvFrameRestExt A.repAlloc g v (c.payload ++ rest).length =
      overDecRecvPostMergeHeapPlBudget A lim (M.stepEvents evs₁ st) s2 g rest v c := by
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    exact overDecRecvPostMergeHeap_eq_unsplit_ext A lim (M.stepEvents evs₁ st) s2 g v hsuf_pay
  rw [hpost_eq]
  have hfit_segB : FitsEnv M lim (M.stepEvents evs₁ st) (OverDecRecvSegBEnv v.base.recv.length) :=
    fitsEnv_segB_of_recv (x := xGhost) hrecv_lt hevs₁ hfit
  refine overDec_sepWPp_mono_post ?_
    (overDecRecv_segB_cro_placed_of_grow hGrow (M.stepEvents evs₁ st) s0 s2 g v c rest
      hok hfresh hsuf hlen hfit_segB hcro2 hregs2 hx0_2)
  rintro sf P_f - - ⟨evs₂, hevs₂, hregsf, hentf⟩
  refine ⟨hregsf, evs₁ ++ evs₂, overDecFieldEnv_of_recv_chain_segB (x := xGhost) hrecv_lt hevs₁ hevs₂, ?_⟩
  rw [← overDecHeapPlBudget_eq, M.stepEvents_append]
  exact hentf

/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded Tag-7 (`receiver_chains`) arm
(`OverDecArmCroPlacedAtTR A lim ext OverDecRecvField`), parameterized by `hGrow` at `lsmpl.base 43`
and `hChain5` at `lsmpl.base 516`. -/
theorem overDecArmRecv_cro_placed_of_callees [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 43)
      (withLsCodeRoLoaded lsmpl (growOneChainSpecX M A lim)))
    (hChain5 : ChainMerge5CroPlacedOkExt A lim ext) :
    OverDecArmCroPlacedAtTR A lim ext OverDecRecvField := by
  intro st s0 s g v fl rest hfl hok hfresh hsuf hlen hfit hregs hx0 _hx22
  cases fl
  case base bf =>
    cases bf
    case recv c =>
      exact overDecArmRecv_cro_core ext hGrow hChain5 st s0 s g v c rest
        hok hfresh hsuf hlen hfit hregs hx0
    all_goals exact False.elim hfl
  all_goals exact False.elim hfl

theorem overDecArmRecv_cro_placed_of_alloc_chain5 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext)
    (hChain5 : ChainMerge5CroPlacedOkExt A lim ext) :
    OverDecArmCroPlacedAtTR A lim ext OverDecRecvField :=
  overDecArmRecv_cro_placed_of_callees
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCl
      (growOneChain_placed_ok_cl (callerProg := lsProg_518 ext) (growOneChain_placed_ok_x hAlloc)))
    hChain5

theorem overDecArmRecv_placed_of_callees [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hGrow : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 43)
      (withLsCodeRoLoaded lsmpl (growOneChainSpecX M A lim)))
    (hChain5 : ∀ ext, ChainMerge5CroPlacedOkExt A lim ext) :
    OverDecArmPlacedStmtTR A lim OverDecRecvField :=
  fun ext => overDecArmRecv_cro_placed_of_callees (hGrow ext) (hChain5 ext)

/-! ## 4. Bytes-Arm Wrappers & Top-Level `SessionStructure::decode` Assembly -/

private theorem sessionShim_of_noAllocShim {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym noAllocShimBudgetSpec) :
    HookSat H sym sessionShimBudgetSpec := by
  obtain ⟨f, hf, hsat⟩ := h
  refine ⟨f, hf, ?_⟩
  intro x R s0 hrun hpre hal
  dsimp only [sessionShimBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hpre
  have hpre' : s0.mem ⊨ noAllocShimBudgetSpec.pre () s0 ∗ R := by
    dsimp only [noAllocShimBudgetSpec]
    exact hpre
  obtain ⟨hret, hcc, hout⟩ := hsat () R s0 hrun hpre' hal
  refine ⟨hret, hcc, ?_⟩
  rcases hout with ⟨h1, h2, hpost⟩ | ⟨hp1, hp2⟩ | ⟨c, he1, he2⟩ | ⟨ho1, ho2⟩
  · refine Or.inl ⟨h1, h2, ?_⟩
    dsimp only [noAllocShimBudgetSpec] at hpost
    dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    rw [satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hpost.1.2, hpost.1.1, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hp1, hp2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he1, he2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho1, ho2⟩))

theorem overDecArm_bytes_cro_placed_of_bm6w [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hBM6W : BytesMerge6Placed514OkExtW A lim ext) :
    OverDecArmCroPlacedAtTR A lim ext OverDecBytesField :=
  overDecArm_bytes_cro_placed_at_of_bm6w hBM6W

theorem overDecArm_bytes_cro_placed_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    OverDecArmCroPlacedAtTR A lim ext OverDecBytesField :=
  overDecArm_bytes_cro_placed_at_of_bm6w
    (bytes_merge_6_placed_ok_w_cro (callerProg := lsProg_518 ext)
      hshim halloc hrealloc hdealloc hmc hpanic_raw)

/-- Top-level fixed-`ext` `[LibsignalPlacement]` budget-threaded `SessionStructure::decode`
(`OverPrevDecodeCroPlacedAt A lim ext`) under `LibsignalCodeRoLoaded`, from `AllocContractsPlaced`,
`BytesMerge6Placed514OkExtW` (Block `514`), and `ChainMerge5CroPlacedOkExt` (Block `516`). -/
theorem overPrevDecode_cro_placed_of_alloc_bm6w_chain5 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext)
    (hBM6W : BytesMerge6Placed514OkExtW A lim ext)
    (hChain5 : ChainMerge5CroPlacedOkExt A lim ext) :
    OverPrevDecodeCroPlacedAt A lim ext :=
  overPrevDecode_cro_of_key_arms
    (overDecEntry_cro_of_placed overDecEntry_placed ext)
    (overDecHeadCons_cro_of_placed overDecHeadCons_placed ext)
    (overDecHeadNil_cro_of_placed overDecHeadNil_placed ext)
    (overDecKey_cro_placed_of_alloc hAlloc)
    (overDecArm_varint_cro_placed_of_alloc hAlloc)
    (overDecArm_bytes_cro_placed_of_bm6w hBM6W)
    (overDecArmSender_cro_placed_of_chain5 hChain5)
    (overDecArmRecv_cro_placed_of_alloc_chain5 hAlloc hChain5)

/-- Top-level fixed-`ext` `[LibsignalPlacement]` budget-threaded `SessionStructure::decode`
(`OverPrevDecodeCroPlacedAt A lim ext`) discharged from the single-step hooks on `ext` and
`ChainMerge5CroPlacedOkExt` (Block `516`). -/
theorem overPrevDecode_cro_placed_of_hooks_chain5 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hmemmove : HookSat ext "memmove" (sessionMemmoveBudgetSpec extHookStack))
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked)
    (hChain5 : ChainMerge5CroPlacedOkExt A lim ext) :
    OverPrevDecodeCroPlacedAt A lim ext :=
  overPrevDecode_cro_placed_of_alloc_bm6w_chain5
    (AllocContractsPlaced.of_hooks halloc hdealloc hrealloc
      (sessionShim_of_noAllocShim hshim) hmemmove)
    (bytes_merge_6_placed_ok_w_cro (callerProg := lsProg_518 ext)
      hshim halloc hrealloc hdealloc hmc hpanic_raw)
    hChain5

/-- `ext`-quantified `[LibsignalPlacement]` budget-threaded `SessionStructure::decode`
(`OverPrevDecodePlacedStmt A lim`). -/
theorem overPrevDecode_placed_of_alloc_bm6w_chain5 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hAlloc : ∀ ext, AllocContractsPlaced M A lim ext)
    (hBM6W : ∀ ext, BytesMerge6Placed514OkExtW A lim ext)
    (hChain5 : ∀ ext, ChainMerge5CroPlacedOkExt A lim ext) :
    OverPrevDecodePlacedStmt A lim :=
  fun ext => overPrevDecode_cro_placed_of_alloc_bm6w_chain5 (hAlloc ext) (hBM6W ext) (hChain5 ext)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudget
