/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7kPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7gPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7hPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7jPlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part K

Budget-threaded relocatable post-call stage compositions (`+3720`, `+7348`, `+7404`), `+4632`
error-exit sequencing, and discharge of `V7Ok7404PropPlaced` for Variant 7 (`InnerState.ct1Sampled`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7kPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsProg_333 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Error PolyDecoder PolyEncoder PolynomialDecoder PolynomialEncoder States V1State
   pbToProtoPolyDecoder pbToProtoPolyEncoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt (Ct1Sent)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderSize polyEncoderAt protoPolynomialDecoderAt protoPolynomialDecoderSize
   resultPolyDecoderFromPbAt resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack fromPbResult)
open CryptoVerification.SpqrV1.States.FromPb
  (DecoderFromPbGhost TraceCalleeSaved collapse_step collapse_top decoderFromPbResult
   decoderFromPbStack resultChunkedStatesAt sp_sub_2400_align spqrErrorByte
   statesFromPbJumpTablePlacedAt statesFromPbSavedCells statesFromPbStack v7_ct1SentHeap
   v7_ct1SentWordsAt v7_from_pb_ct1Sampled_dec_err v7_from_pb_ct1Sampled_dec_none
   v7_from_pb_ct1Sampled_enc_err v7_from_pb_ct1Sampled_ok v7_optDecoderCapProp
   v7_optProtoPolyDecoderTail v7_pbA_128_56_40_to_224 v7_polyEncoderTag v7_receivingEkPtsOk
   v7_stackGapsEncDec v7_stackGapsEncDec_unsplit)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (statesFromPbVariantPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2 (seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlacedBudget (v7_err_4632_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7gPlacedBudget
  (v7_enc_err_3720_to_4632_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7hPlacedBudget
  (v7_bl_decoder_7400_to_35448_placed_budget v7_copy_dec_7348_to_7400_placed_budget
   v7_dec_err_7404_to_4632_placed v7_enc_ok_move_3720_to_7348_of_budgetHooks
   v7_enc_ok_none_dec_7348_to_4632_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7jPlacedBudget
  (v7_dec_ok_7404_to_ret_placed)

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333

/-- Sequence a clean state-dependent `SepWP` step before a `SepWPp` continuation while threading
`LibsignalCodeLoaded lsmpl`. -/
theorem v7_sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program}
    {mid target_pc : BitVec 64} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P : SepProp} {P_mid : State → SepProp} {Q_regs : State → Prop}
    {post Qpan : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog target_pc sm (P_mid sm) post Qpan) :
    SepWPp prog target_pc s P post Qpan :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
      SepWPp.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

/-- Placed `subroutine_ok` call combinator in `SepWPp` that threads `LibsignalCodeLoaded lsmpl`
into the post-call continuation. -/
theorem v7_sepWPp_call_wpp_lscl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    {x : α} {s : State} {P_step F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf R', (sf.mem ⊨ (spec.onPanic x s sf ∗ F) ∗ R') → (sf.mem ⊨ Qpan sf ∗ R'))
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R') := by
    rw [sepConj_assoc] at hm
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre (F ∗ R') hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre' hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_s, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm (hcl.of_keepsFrozen hsteps.keepsFrozen) hspm hcsm R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, _, hpost, fun hm_f => hpan sm R hm_f⟩)⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hexit_eq] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost; rw [hoom_eq] at hpost; exact (not_satisfies_false_sepConj hpost).elim

/-- Compose a budget-threaded `SepWP` reaching `lsmpl.base 333 + 4632#64` with
`v7_err_4632_placed_budget` and `sepWPp_of_states_exit_placed`. -/
theorem v7_seq_err_4632_wpp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (st0 : M.σ) (s0 s1 : State) (out pbA : BitVec 64) (s : V1State.Chunked.Ct1Sampled)
    (err : Error) (P R : SepProp)
    (hfrom_pb : States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err err))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hstep : SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1 P
      (fun sm Pm =>
        ∃ evs : List AllocEvent, Env evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 2304 ∗
            statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st0) sm) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err ∧
          TraceCalleeSaved sm s0)) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1 P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env).post
              ((out, pbA), st0) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env).onPanic
              ((out, pbA), st0) s0 sf ∗ R)) := by
  apply DefsBudget.sepWPp_of_states_exit_placed st0 s0 s1 out pbA { innerState := some (.ct1Sampled s) } Env P R
  refine SepWP.seq hstep fun sm _Pm hpcm hrunm ⟨evs, henv, hPm, hspm, hx19m, hx28m, htrm⟩ => ?_
  refine SepWP.weaken_pre
    (Entails.trans hPm (Entails.of_eq (show _ =
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) ∗
      A.pool lim (M.stepEvents evs st0) sm by sep_ac_rfl)))
    (SepWP.mono
      (v7_err_4632_placed_budget A lim (M.stepEvents evs st0) (F := F) (ext := ext) s0 sm out err
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hsp0_align hpcm hrunm hspm hx19m hx28m htrm) ?_)
  intro sf Pf _ _ ⟨hPf, _hvm, hq⟩
  rw [hfrom_pb]
  exact ⟨⟨evs, henv, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hq⟩

/-- Budget-threaded placed hypothesis for the final `Ok(dec)` success path
(`+7404 -> +7468 -> +8180 -> s0.x30`) of Variant 7 (`InnerState.ct1Sampled`). -/
def V7Ok7404PropPlaced [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {F : ShaCompress}
    {ext : String → Option (State → State)} (s0 : State) (out pbA : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) : Prop :=
  ∀ (st : M.σ) (s1 : State) (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (uc : Ct1Sent (spqrAuthApi F))
    (enc : PolyEncoder) (dec : PolyDecoder),
    (s0.sp &&& 15#64 == 0#64) = true →
    c1.toNat < 2 ^ 63 →
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .ok (.ct1Sampled { uc := uc, sending_ct1 := enc, receiving_ek := dec }) →
    s1.pc = lsmpl.base 333 + 7404#64 →
    s1.status = .Running →
    s1.sp = s0.sp - 2400#64 →
    s1.readReg64 .x19 = out →
    s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 →
    s1.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64 →
    s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 →
    s1.readReg64 .x24 = c2 →
    s1.readReg64 .x26 = l1 →
    s1.readReg64 .x27 = pbA →
    TraceCalleeSaved s1 s0 →
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (.ok dec) ∗
        polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
        v7_stackGapsEncDec (s0.sp - 2400#64) ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool lim st sf ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)

/-- Budget-threaded stage at `+7404` after `<PolyDecoder>::from_pb` returns. -/
theorem v7_after_dec_call_7404_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st0 : M.σ) (evs_sofar : List AllocEvent)
    (s0 s1 : State) (out pbA c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Ct1Sent (spqrAuthApi F))
    (e : PolynomialEncoder) (enc : PolyEncoder)
    (d : PolynomialDecoder) (R : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (h7404_ok : V7Ok7404PropPlaced M A lim (F := F) (ext := ext) s0 out pbA s)
    (henv_ok : ∀ dec, decoderFromPbResult (pbToProtoPolyDecoder d) = .ok dec → Env evs_sofar)
    (henv_err : ∀ err evs_free,
      decoderFromPbResult (pbToProtoPolyDecoder d) = .error err →
      FreeOnlyEvs evs_free → Env (evs_sofar ++ evs_free))
    (hpts : (d.ptsNeeded == 576#32) = true)
    (hs_uc : s.uc = some u)
    (huc : Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (hs_enc : s.sendingCt1 = some e)
    (henc : fromPbResult (pbToProtoPolyEncoder e) = .ok enc)
    (hs_dec : s.receivingEk = some d)
    (hc1 : c1.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7404#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64)
          (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
        polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
        v7_stackGapsEncDec (s0.sp - 2400#64) ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs_sofar st0) s1)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env).post
              ((out, pbA), st0) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env).onPanic
              ((out, pbA), st0) s0 sf ∗ R)) := by
  cases hdec : decoderFromPbResult (pbToProtoPolyDecoder d) with
  | error err =>
    have hfrom_pb := v7_from_pb_ct1Sampled_dec_err F s u uc e enc d err
      hpts hs_uc huc hs_enc henc hs_dec hdec
    apply v7_seq_err_4632_wpp_placed st0 s0 s1 out pbA s .stateDecode _ R hfrom_pb hsp0_align
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono
        (v7_dec_err_7404_to_4632_placed hA s0 s1 out c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
          uc enc err (M.stepEvents evs_sofar st0)
          ((((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
           (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
           memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
           v7_stackGapsEncDec (s0.sp - 2400#64) ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           memRegion pbA optProtoInnerStateSize ∗
           statesFromPbJumpTablePlacedAt)
          hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 htr1) ?_)
    intro sm Pm _ _ ⟨evs_free, hevs_free, hPm, hspm, hx19m, hx28m, htrm⟩
    rw [← M.stepEvents_append evs_sofar evs_free st0] at hPm
    have hx28_b : (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx28m]; rfl
    refine ⟨evs_sofar ++ evs_free, henv_err err evs_free hdec hevs_free, Entails.trans hPm ?_,
      hspm, hx19m, hx28_b, htrm⟩
    have hunsplit := v7_stackGapsEncDec_unsplit (s0.sp - 2400#64) (v7_polyEncoderTag enc) c1 p1
    refine Entails.trans (Entails.of_eq (show _ =
      ((((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
       memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
       memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
       memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
       memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
       v7_stackGapsEncDec (s0.sp - 2400#64)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents (evs_sofar ++ evs_free) st0) sm) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hunsplit) (Entails.of_eq (by sep_ac_rfl))
  | ok dec =>
    have hfrom_pb := v7_from_pb_ct1Sampled_ok F s u uc e enc d dec
      hpts hs_uc huc hs_enc henc hs_dec hdec
    apply DefsBudget.sepWPp_of_states_exit_placed st0 s0 s1 out pbA { innerState := some (.ct1Sampled s) } Env _ R
    refine SepWP.mono
      (h7404_ok (M.stepEvents evs_sofar st0) s1 c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc enc dec
        hsp0_align hc1 hfrom_pb hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 htr1) ?_
    intro sf Pf _ _ ⟨hPf, hq⟩
    exact ⟨⟨evs_sofar, henv_ok dec hdec, hPf⟩, hq⟩

/-- Budget-threaded stage at `+7348` after `Ok(enc)` has been moved to `fsp + 1392..1792`. -/
theorem v7_after_enc_ok_7348_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec_sub : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st0 : M.σ) (evs_prev : List AllocEvent)
    (s0 s1 : State) (out pbA cap_dec c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Ct1Sent (spqrAuthApi F))
    (e : PolynomialEncoder) (enc : PolyEncoder) (R : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (h7404_ok : V7Ok7404PropPlaced M A lim (F := F) (ext := ext) s0 out pbA s)
    (hfits_dec : ∀ d, s.receivingEk = some d →
      FitsEnv M lim (M.stepEvents evs_prev st0) (FromPbDecAllocEnv (pbToProtoPolyDecoder d)))
    (henv_dec_none : s.receivingEk = none →
      ∀ evs_free, FreeOnlyEvs evs_free → Env (evs_prev ++ evs_free))
    (henv_dec_ok : ∀ d dec evs_dec,
      s.receivingEk = some d →
      FromPbDecEnv (pbToProtoPolyDecoder d) evs_dec →
      decoderFromPbResult (pbToProtoPolyDecoder d) = .ok dec →
      Env (evs_prev ++ evs_dec))
    (henv_dec_err : ∀ d err evs_dec evs_free,
      s.receivingEk = some d →
      FromPbDecEnv (pbToProtoPolyDecoder d) evs_dec →
      decoderFromPbResult (pbToProtoPolyDecoder d) = .error err →
      FreeOnlyEvs evs_free →
      Env (evs_prev ++ evs_dec ++ evs_free))
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (hcap_dec : v7_optDecoderCapProp cap_dec (s.receivingEk.map pbToProtoPolyDecoder))
    (hs_uc : s.uc = some u)
    (huc : Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (hs_enc : s.sendingCt1 = some e)
    (henc : fromPbResult (pbToProtoPolyEncoder e) = .ok enc)
    (hc1 : c1.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hpstate1 : s1.pstate = addsPState64 cap_dec 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
        v7_stackGapsEncDec (s0.sp - 2400#64) ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA 128 ∗
        memRegion (pbA + 128#64) 56 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs_prev st0) s1)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env).post
              ((out, pbA), st0) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env).onPanic
              ((out, pbA), st0) s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  cases hs_dec : s.receivingEk with
  | none =>
    have hfrom_pb := v7_from_pb_ct1Sampled_dec_none F s u uc e enc hs_uc huc hs_enc henc hs_dec
    have henv_none := henv_dec_none hs_dec
    rw [hs_dec] at hcap_dec
    dsimp only [Option.map, v7_optDecoderCapProp] at hcap_dec
    subst hcap_dec
    simp only [Option.map]
    apply v7_seq_err_4632_wpp_placed st0 s0 s1 out pbA s .stateDecode _ R hfrom_pb hsp0_align
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono
        (v7_enc_ok_none_dec_7348_to_4632_placed hA s0 s1 out pbA c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
          uc enc (M.stepEvents evs_prev st0)
          (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
           (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
           memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
           v7_stackGapsEncDec (s0.sp - 2400#64) ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           memRegion pbA 128 ∗
           memRegion (pbA + 128#64) 56 ∗
           statesFromPbJumpTablePlacedAt)
          hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx24_1 hpstate1 htr1) ?_)
    intro sm Pm _ _ ⟨evs_free, hevs_free, hPm, hspm, hx19m, hx28m, htrm⟩
    rw [← M.stepEvents_append evs_prev evs_free st0] at hPm
    have hx28_b : (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx28m]; rfl
    refine ⟨evs_prev ++ evs_free, henv_none evs_free hevs_free, Entails.trans hPm ?_,
      hspm, hx19m, hx28_b, htrm⟩
    have hunsplit := v7_stackGapsEncDec_unsplit (s0.sp - 2400#64) (v7_polyEncoderTag enc) c1 p1
    have hpb224 := v7_pbA_128_56_40_to_224 pbA
    refine Entails.trans (Entails.of_eq (show _ =
      ((((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
       memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
       memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
       memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
       memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
       v7_stackGapsEncDec (s0.sp - 2400#64)) ∗
      (memRegion pbA 128 ∗ memRegion (pbA + 128#64) 56 ∗ memRegion (pbA + 184#64) 40) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents (evs_prev ++ evs_free) st0) sm) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hunsplit (sepConj_mono_left hpb224)) (Entails.of_eq (by sep_ac_rfl))
  | some d =>
    have hfits_d := hfits_dec d hs_dec
    rw [hs_dec] at hcap_dec hpts
    dsimp only [v7_receivingEkPtsOk] at hpts
    dsimp only [Option.map, v7_optDecoderCapProp] at hcap_dec
    simp only [Option.map]
    have hcap_dec_lt : cap_dec.toNat < 2 ^ 63 := by omega
    refine v7_sepWPp_seq_clean_lscl hcl1
      (mid := lsmpl.base 376)
      (P_mid := fun sm =>
        (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
         protoPolynomialDecoderAt A.repAlloc ((s0.sp - 2400#64) + 1848#64) (pbToProtoPolyDecoder d) ∗
         A.pool lim (M.stepEvents evs_prev st0) sm ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗
        (polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
         v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
         v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
         (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
         (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
         memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
         memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
         v7_stackGapsEncDec (s0.sp - 2400#64) ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗
         statesFromPbJumpTablePlacedAt))
      (Q_regs := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
        sm.readReg64 .x1 = (s0.sp - 2400#64) + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 ∧
        sm.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64 ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 7404#64 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · refine seq_clean_st
        (mid := lsmpl.base 333 + 7400#64)
        (P_mid := fun sm =>
          (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
           protoPolynomialDecoderAt A.repAlloc ((s0.sp - 2400#64) + 1848#64) (pbToProtoPolyDecoder d) ∗
           A.pool lim (M.stepEvents evs_prev st0) sm ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗
          (polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
           v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
           v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
           (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
           (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
           memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
           v7_stackGapsEncDec (s0.sp - 2400#64) ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           memRegion pbA optProtoInnerStateSize ∗
           statesFromPbJumpTablePlacedAt))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
          sm.readReg64 .x1 = (s0.sp - 2400#64) + 1848#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 ∧
          sm.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64 ∧
          sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧
          sm.readReg64 .x24 = c2 ∧
          sm.readReg64 .x26 = l1 ∧
          sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (SepWP.mono
            (v7_copy_dec_7348_to_7400_placed_budget A lim (M.stepEvents evs_prev st0) (ext := ext)
              s0 s1 (s0.sp - 2400#64) out pbA cap_dec c2 l1
              ((s0.sp - 2400#64) + 1392#64) ((s0.sp - 2400#64) + 848#64)
              (pbToProtoPolyDecoder d)
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
               polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
               v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
               v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
               (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
               (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
               (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
               memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
               memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
               v7_stackGapsEncDec (s0.sp - 2400#64) ∗
               statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗
               memRegion pbA 128 ∗
               memRegion (pbA + 128#64) 56 ∗
               statesFromPbJumpTablePlacedAt)
              hfsp_align hcap_dec_lt hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 hpstate1 htr1) ?_)
        intro sm Pm _ _ ⟨hPm, _hvm, hq⟩
        refine ⟨Entails.trans hPm ?_, hq⟩
        have hpb224 := v7_pbA_128_56_40_to_224 pbA
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion pbA 128 ∗ memRegion (pbA + 128#64) 56 ∗ memRegion (pbA + 184#64) 40) ∗
          ((memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
            protoPolynomialDecoderAt A.repAlloc ((s0.sp - 2400#64) + 1848#64) (pbToProtoPolyDecoder d) ∗
            A.pool lim (M.stepEvents evs_prev st0) sm ∗
            stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗
           (polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
            v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
            v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
            (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
            (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
            memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
            memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
            v7_stackGapsEncDec (s0.sp - 2400#64) ∗
            statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗
            statesFromPbJumpTablePlacedAt)) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hpb224) (Entails.of_eq (by sep_ac_rfl))
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, htr2⟩
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (SepWP.mono
            (v7_bl_decoder_7400_to_35448_placed_budget A lim (M.stepEvents evs_prev st0) (ext := ext)
              s0 s2 (s0.sp - 2400#64) out pbA c2 l1
              ((s0.sp - 2400#64) + 1392#64) ((s0.sp - 2400#64) + 848#64)
              (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
               protoPolynomialDecoderAt A.repAlloc ((s0.sp - 2400#64) + 1848#64) (pbToProtoPolyDecoder d) ∗
               stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
               v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
               v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
               (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
               (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
               (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
               memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
               memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
               v7_stackGapsEncDec (s0.sp - 2400#64) ∗
               statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗
               memRegion pbA optProtoInnerStateSize ∗
               statesFromPbJumpTablePlacedAt)
              hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 htr2) ?_)
        intro sm Pm _ _ ⟨hPm, _hvm, hq⟩
        exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hq⟩
    · intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx0_3, hx1_3, hx19_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx30_3, htr3⟩
      have halign3 : s3.spAligned = true := by
        unfold State.spAligned; rw [hsp3]; exact hfsp_align
      refine v7_sepWPp_call_wpp_lscl (Variant4PlacedBudget.v4_sub_ok_decoder_from_pb_placed hdec_sub)
        (x := (DecoderFromPbGhost.mk ((s0.sp - 2400#64) + 1888#64) ((s0.sp - 2400#64) + 1848#64) (pbToProtoPolyDecoder d),
               M.stepEvents evs_prev st0))
        hcl3 hpc3 hrun3 halign3 hx30_3
        (fun R' hm => by
          dsimp only [DefsBudget.decoderFromPbSpec]
          rw [show polyDecoderSize = 400 from rfl, show decoderFromPbStack = encoderFromPbStack from rfl]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_3, hx1_3, hfits_d,
            by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s3.readReg64 .x30); rw [show s3.readReg64 .x30 = _ from hx30_3]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩, ?_⟩
          rw [hsp3]
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
        (fun sf R' hm => by
          change sf.mem ⊨ (⌜False⌝ ∗ _) ∗ R' at hm
          rw [sepConj_assoc] at hm
          exact (not_satisfies_false_sepConj hm).elim)
        (fun _ _ => rfl)
        ?_
      intro s4 hpc4 hrun4 hcl4 hsp4 hcs4
      have hsp4' : s4.sp = s0.sp - 2400#64 := hsp4.trans hsp3
      have hx19_4 : s4.readReg64 .x19 = out := (hcs4.1).trans hx19_3
      have hx21_4 : s4.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := (hcs4.2.2.1).trans hx21_3
      have hx22_4 : s4.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64 := (hcs4.2.2.2.1).trans hx22_3
      have hx23_4 : s4.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := (hcs4.2.2.2.2.1).trans hx23_3
      have hx24_4 : s4.readReg64 .x24 = c2 := (hcs4.2.2.2.2.2.1).trans hx24_3
      have hx26_4 : s4.readReg64 .x26 = l1 := (hcs4.2.2.2.2.2.2.2.1).trans hx26_3
      have hx27_4 : s4.readReg64 .x27 = pbA := (hcs4.2.2.2.2.2.2.2.2.1).trans hx27_3
      dsimp only [DefsBudget.decoderFromPbSpec]
      rw [show protoPolynomialDecoderSize = 40 from rfl,
          show decoderFromPbStack = encoderFromPbStack from rfl,
          hsp3, sepExists_sepConj_left]
      apply SepWPp.exists_elim; intro evs_dec
      rw [← M.stepEvents_append evs_prev evs_dec st0]
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        ⌜s4.trace = s3.trace ∧ AllocCallPreserved s3 s4 ∧ FromPbDecEnv (pbToProtoPolyDecoder d) evs_dec⌝ ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         resultPolyDecoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64)
           (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
         polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
         v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
         v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
         (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
         (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
         memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
         memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
         memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
         v7_stackGapsEncDec (s0.sp - 2400#64) ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗
         statesFromPbJumpTablePlacedAt ∗
         A.pool lim (M.stepEvents (evs_prev ++ evs_dec) st0) s4) by sep_ac_rfl)) ?_
      apply SepWPp.pure_elim; rintro ⟨htr4, _hacp4, hdec_env⟩
      exact v7_after_dec_call_7404_placed hA st0 (evs_prev ++ evs_dec)
        s0 s4 out pbA c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
        s u uc e enc d R hcl4 h7404_ok
        (fun dec hdec_res => henv_dec_ok d dec evs_dec hs_dec hdec_env hdec_res)
        (fun err evs_free hdec_res hfree =>
          henv_dec_err d err evs_dec evs_free hs_dec hdec_env hdec_res hfree)
        hpts hs_uc huc hs_enc henc hs_dec hc1 hsp0_align
        hpc4 hrun4 hsp4' hx19_4 hx21_4 hx22_4 hx23_4 hx24_4 hx26_4 hx27_4
        ⟨htr4.trans htr3.1, hcs4.2.2.2.2.2.2.2.2.2.2.2.trans htr3.2⟩

/-- Budget-threaded stage at `+3720` after `<PolyEncoder>::from_pb` returns. -/
theorem v7_after_enc_call_3720_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec_sub : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st0 : M.σ) (evs_prev : List AllocEvent)
    (s0 s1 : State) (out pbA cap_dec slot16 slot200 c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Ct1Sent (spqrAuthApi F))
    (e : PolynomialEncoder) (R : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (h7404_ok : V7Ok7404PropPlaced M A lim (F := F) (ext := ext) s0 out pbA s)
    (henv_enc_err : ∀ err evs_free,
      fromPbResult (pbToProtoPolyEncoder e) = .error err →
      FreeOnlyEvs evs_free →
      Env (evs_prev ++ evs_free))
    (hfits_dec : ∀ enc d,
      fromPbResult (pbToProtoPolyEncoder e) = .ok enc →
      s.receivingEk = some d →
      FitsEnv M lim (M.stepEvents evs_prev st0) (FromPbDecAllocEnv (pbToProtoPolyDecoder d)))
    (henv_dec_none : ∀ enc evs_free,
      fromPbResult (pbToProtoPolyEncoder e) = .ok enc →
      s.receivingEk = none →
      FreeOnlyEvs evs_free →
      Env (evs_prev ++ evs_free))
    (henv_dec_ok : ∀ enc d dec evs_dec,
      fromPbResult (pbToProtoPolyEncoder e) = .ok enc →
      s.receivingEk = some d →
      FromPbDecEnv (pbToProtoPolyDecoder d) evs_dec →
      decoderFromPbResult (pbToProtoPolyDecoder d) = .ok dec →
      Env (evs_prev ++ evs_dec))
    (henv_dec_err : ∀ enc d err evs_dec evs_free,
      fromPbResult (pbToProtoPolyEncoder e) = .ok enc →
      s.receivingEk = some d →
      FromPbDecEnv (pbToProtoPolyDecoder d) evs_dec →
      decoderFromPbResult (pbToProtoPolyDecoder d) = .error err →
      FreeOnlyEvs evs_free →
      Env (evs_prev ++ evs_dec ++ evs_free))
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (hcap_dec : v7_optDecoderCapProp cap_dec (s.receivingEk.map pbToProtoPolyDecoder))
    (hs_uc : s.uc = some u)
    (huc : Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (hs_enc : s.sendingCt1 = some e)
    (hc1 : c1.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3720#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = (s0.sp - 2400#64) + 1792#64)
    (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = (s0.sp - 2400#64) + 1888#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64)
          (fromPbResult (pbToProtoPolyEncoder e)) ∗
        memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
        memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
        v7_stackGapsEncDec (s0.sp - 2400#64) ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA 128 ∗
        memRegion (pbA + 128#64) 56 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs_prev st0) s1)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env).post
              ((out, pbA), st0) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env).onPanic
              ((out, pbA), st0) s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  cases henc : fromPbResult (pbToProtoPolyEncoder e) with
  | error err =>
    have hfrom_pb := v7_from_pb_ct1Sampled_enc_err F s u uc e err hpts hs_uc huc hs_enc henc
    apply v7_seq_err_4632_wpp_placed st0 s0 s1 out pbA s .stateDecode _ R hfrom_pb hsp0_align
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono
        (v7_enc_err_3720_to_4632_placed hA s0 s1 out pbA cap_dec c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
          uc err (s.receivingEk.map pbToProtoPolyDecoder) (M.stepEvents evs_prev st0)
          (memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
           (((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
           memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
           v7_stackGapsEncDec (s0.sp - 2400#64) ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           memRegion pbA 128 ∗
           memRegion (pbA + 128#64) 56 ∗
           statesFromPbJumpTablePlacedAt)
          hcap_dec hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx24_1 hx27_1 hx28_1 htr1) ?_)
    intro sm Pm _ _ ⟨evs_free, hevs_free, hPm, hspm, hx19m, hx28m, htrm⟩
    rw [← M.stepEvents_append evs_prev evs_free st0] at hPm
    have hx28_b : (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx28m]; rfl
    refine ⟨evs_prev ++ evs_free, henv_enc_err err evs_free henc hevs_free, Entails.trans hPm ?_,
      hspm, hx19m, hx28_b, htrm⟩
    have hunsplit := v7_stackGapsEncDec_unsplit (s0.sp - 2400#64) slot16 c1 slot200
    have hpb224 := v7_pbA_128_56_40_to_224 pbA
    refine Entails.trans (Entails.of_eq (show _ =
      ((((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
       memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
       memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
       memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
       memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
       v7_stackGapsEncDec (s0.sp - 2400#64)) ∗
      (memRegion pbA 128 ∗ memRegion (pbA + 128#64) 56 ∗ memRegion (pbA + 184#64) 40) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents (evs_prev ++ evs_free) st0) sm) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hunsplit (sepConj_mono_left hpb224)) (Entails.of_eq (by sep_ac_rfl))
  | ok enc =>
    refine v7_sepWPp_seq_clean_lscl hcl1
      (mid := lsmpl.base 333 + 7348#64)
      (P_mid := fun sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
        v7_stackGapsEncDec (s0.sp - 2400#64) ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA 128 ∗
        memRegion (pbA + 128#64) 56 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs_prev st0) sm)
      (Q_regs := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = v7_polyEncoderTag enc ∧
        sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = (s0.sp - 2400#64) + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.pstate = addsPState64 cap_dec 1#64 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (SepWP.mono
          (v7_enc_ok_move_3720_to_7348_of_budgetHooks hA (M.stepEvents evs_prev st0)
            s0 s1 (s0.sp - 2400#64) out pbA cap_dec c2 l1 p1
            ((s0.sp - 2400#64) + 1392#64) slot16 slot200 enc
            (v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
             v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
             (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
             memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
             memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
             v7_stackGapsEncDec (s0.sp - 2400#64) ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             memRegion pbA 128 ∗
             memRegion (pbA + 128#64) 56 ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
             statesFromPbJumpTablePlacedAt)
            hfsp_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1) ?_)
      intro sm Pm _ _ ⟨hPm, _hvm, hq⟩
      exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hq⟩
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, _, hx21_2, hx22_2, hx23_2, hx24_2, _, hx26_2, hx27_2, hpstate2, htr2⟩
      exact v7_after_enc_ok_7348_placed hA hdec_sub st0 evs_prev s0 s2 out pbA cap_dec
        c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 s u uc e enc R
        hcl2 h7404_ok
        (fun d hs_d => hfits_dec enc d henc hs_d)
        (fun hs_none evs_free hfree => henv_dec_none enc evs_free henc hs_none hfree)
        (fun d dec evs_dec hs_d hdec_env hdec_res => henv_dec_ok enc d dec evs_dec henc hs_d hdec_env hdec_res)
        (fun d err evs_dec evs_free hs_d hdec_env hdec_res hfree =>
          henv_dec_err enc d err evs_dec evs_free henc hs_d hdec_env hdec_res hfree)
        hpts hcap_dec hs_uc huc hs_enc henc hc1 hsp0_align
        hpc2 hrun2 hsp2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 hpstate2 htr2

/-- `V7Ok7404PropPlaced` holds unconditionally via `Variant7jPlacedBudget.v7_dec_ok_7404_to_ret_placed`. -/
theorem v7_ok7404Prop_holds_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (s0 : State) (out pbA : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) :
    V7Ok7404PropPlaced M A lim (F := F) (ext := ext) s0 out pbA s := by
  intro st s1 c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc enc dec
    hsp0_align _ hfrom_pb hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 htr1
  have h208_1056 :
      memRegion ((s0.sp - 2400#64) + 208#64) 688 ∗
      memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
      memRegion ((s0.sp - 2400#64) + 952#64) 312 ⊢
      memRegion ((s0.sp - 2400#64) + 208#64) 1056 := by
    exact collapse_top <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      Entails.refl _
  have h1792_96 :
      memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
      memRegion ((s0.sp - 2400#64) + 1848#64) 40 ⊢
      memRegion ((s0.sp - 2400#64) + 1792#64) 96 := by
    exact collapse_top <|
      collapse_step (Entails.refl _) <|
      Entails.refl _
  unfold v7_stackGapsEncDec
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 2400#64) + 208#64) 688 ∗
       memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 952#64) 312) ∗
      (memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1848#64) 40) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 16 ∗
       (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       memRegion ((s0.sp - 2400#64) + 32#64) 168 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
       v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
       polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
       resultPolyDecoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (.ok dec) ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
       (memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTablePlacedAt) ∗
       A.pool lim st s1) by sep_ac_rfl))
      (Entails.trans (sepConj_mono h208_1056 (sepConj_mono_left h1792_96))
        (Entails.of_eq (by sep_ac_rfl))))
    (SepWP.mono
      (v7_dec_ok_7404_to_ret_placed hA st s0 s1 out pbA c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
        uc enc dec
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 htr1) ?_)
  intro sf Pf _ _ ⟨hPf, _hvm, hq⟩
  rw [hfrom_pb]
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hq⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7kPlacedBudget
