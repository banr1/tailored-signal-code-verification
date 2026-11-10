/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4a
import GeneratedLean.LibsignalSessionCode -- shake: keep
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 4a: Relocation `memcpy` Helper & Arm 5 (`States.noHeaderReceived`)

Provides the `VmPreserved` partial-relocation helper `call_memcpy_keep_relocate_wp` shared across
Arms 2, 4, 5, and 6, and verifies Arm 5 (`States.noHeaderReceived`, tag `7`,
`+0 -> +60 -> +1108 -> +1176 -> +1540 -> +1544 -> ret`) under `RustCliAllocBudget M` and
`NoHeaderReceivedEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.LibsignalSpqrV1 (PolyDecoder States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (NoHeaderReceived)
open CryptoVerification.LibsignalTripleRatchet
  (memcpyName sessionMemcpyRegionSpec tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize protoPolynomialDecoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (Relocatable TraceCalleeSaved authenticatorHeap bv_add_add_lit' bv_sub_sub_lit'
   chunkedNoHeaderReceived_expose epilogueStagingCells fnAddr_adrp_5ce6c
   memcpy_keep_relocate_recombine memcpy_keep_relocate_split outWords28
   outWords28_entails_noHeaderReceived protoPolynomialDecoderHeap relocatedHeap
   stA_noHeaderReceived_entails_928 stack_1416_split_noHeaderReceived
   statesIntoPbJumpTableAt statesIntoPbJumpTableBytes statesIntoPbName
   statesIntoPbSavedCells statesIntoPbStack statesIntoPb_fnOff)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbAllocEnv DecoderIntoPbEnv DecoderIntoPbOkExt
   fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (statesIntoPbVariantSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
  (call_decoderIntoPb_expose_wp sepWPp_of_states_into_pb_exit_of_env
   states_into_pb_epilogue states_into_pb_prologue_60
   sub_ok_decoderIntoPb_raw sub_ok_memcpy_raw)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec)

private theorem rebase_fnAddr_eq (P : Program) (b : BitVec 64)
    (H₁ H₂ : String → Option (State → State)) :
    (P.rebase b H₁).fnAddr = (P.rebase b H₂).fnAddr :=
  rfl

private theorem withSvc_fetch_eq {prog : Program} (svc : State → State) {pc : BitVec 64}
    {inst : Instr} (h : prog.fetch pc = some inst) :
    (prog.withSvc svc).fetch pc = some inst :=
  h

local elab "lift_fetches_withSvc" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut hyps : Array Lean.Meta.Hypothesis := #[]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← Lean.instantiateMVars decl.type
        if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Arm64.Program.fetch 2 then
          let progE := (ty.getArg! 1).getArg! 0
          if !progE.isAppOfArity ``Arm64.Program.withSvc 2 then
            let prf ← Lean.Meta.mkAppM ``withSvc_fetch_eq #[Lean.mkConst ``Arm64.noSyscalls, decl.toExpr]
            let newTy ← Lean.Meta.inferType prf
            hyps := hyps.push { userName := `this, type := newTy, value := prf }
    if !hyps.isEmpty then
      let g ← Lean.Elab.Tactic.getMainGoal
      let (_, g') ← g.assertHypotheses hyps
      Lean.Elab.Tactic.replaceMainGoal [g']

local macro "into_pb_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| (
      code_fetches_range CryptoVerification.libsignalSessionCode
        CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbBin
        $b $H CryptoVerification.SpqrV1.States.IntoPb.statesIntoPb_fnOff
        (ls_off% "<spqr::v1::chunked::states::States>::into_pb") $k0 $len
      lift_fetches_withSvc))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem align_entails_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P ⊢ P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨htp, hp, hq⟩ => ⟨htp, Entails.trans hp h, hq⟩

private theorem seq_clean_wp {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

/-! ## 1. Shared Budget Partial-Relocation `memcpy` Helper (`call_memcpy_keep_relocate_wp`) -/

/-- Total-correctness (`SepWP`) partial-relocation `memcpy` helper with `VmPreserved` pool
    transport: keeps `F src` (`k` bytes) at `src`, relocates `G (src + off)` (`m` bytes) to
    `dst + off`, and transports `A.pool lim st s` to `A.pool lim st sf`. -/
theorem call_memcpy_keep_relocate_wp
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {b memcpy_pc : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      memcpy_pc
      sessionMemcpyRegionBudgetSpec)
    {k m n : Nat} {off : BitVec 64}
    {F G : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 k)
    (hkm : k + m = n)
    (hF : Relocatable k F)
    (hG : Relocatable m G)
    (dst src : BitVec 64)
    {s0 s : State} {ret_pc target_pc : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = memcpy_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (F src ∗ G (src + off)) ∗ A.pool lim st s) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      VmPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (((memRegion dst k ∗ G (dst + off)) ∗
          (F src ∗ memRegion (src + off) m) ∗
          A.pool lim st sf) ∗ Frame)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s P post := by
  have hpre_split :
      P ⊢ ∃∗ bs1 : List (BitVec 8), ∃∗ bs2 : List (BitVec 8),
        ⌜bs1.length = k ∧ bs2.length = m ∧ (bs1 ++ bs2).length = n⌝ ∗
        (memRegion dst n ∗ (src ↦ₛ (bs1 ++ bs2))) ∗
        (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ A.pool lim st s ∗ Frame) := by
    rw [hsplit]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (memcpy_keep_relocate_split hoff hkm hF hG dst src)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs1
    apply Entails.sepExists_elim; intro bs2
    have hcomm :
        (memRegion dst n ∗
          ((⌜bs1.length = k ∧ bs2.length = m ∧ (bs1 ++ bs2).length = n⌝ ∗
            (src ↦ₛ (bs1 ++ bs2)) ∗ relocatedHeap F bs1 ∗ relocatedHeap G bs2) ∗
           A.pool lim st s)) ∗ Frame =
        ⌜bs1.length = k ∧ bs2.length = m ∧ (bs1 ++ bs2).length = n⌝ ∗
        (memRegion dst n ∗ (src ↦ₛ (bs1 ++ bs2))) ∗
        (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ A.pool lim st s ∗ Frame) := by sep_ac_rfl
    rw [hcomm]
    apply Entails.pure_left; intro hpure
    refine Entails.sepExists_right bs1 (Entails.sepExists_right bs2 ?_)
    exact Entails.pure_right hpure (Entails.refl _)
  refine SepWP.weaken_pre hpre_split ?_
  refine SepWP.exists_elim fun bs1 => SepWP.exists_elim fun bs2 => ?_
  refine SepWP.pure_elim fun ⟨hlen1, hlen2, hlen12⟩ => ?_
  refine SepWP.call_subroutine_frame hmemcpy_raw (x := (dst, src, bs1 ++ bs2))
    (F := relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ A.pool lim st s ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen12, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro _ _ _ hpan
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpan
    exact not_satisfies_false_sepConj hpan
  · intro _ _ _ _ hex
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hex
    exact not_satisfies_false_sepConj hex
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜VmPreserved s sf⌝ ∗ ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s.trace⌝ ∗
      (((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
        relocatedHeap F bs1 ∗ relocatedHeap G bs2) ∗
       A.pool lim st s ∗ Frame) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim fun hvm_sf => SepWP.pure_elim fun ⟨_, htr_sf⟩ => ?_
    rw [← A.pool_of_vmPreserved hvm_sf]
    have hrec := memcpy_keep_relocate_recombine (F := F) (G := G) hoff hlen1 hlen2 dst src
    have hpost_ent :
        ((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
          relocatedHeap F bs1 ∗ relocatedHeap G bs2) ∗
        A.pool lim st sf ∗ Frame ⊢
        (((memRegion dst k ∗ G (dst + off)) ∗
          (F src ∗ memRegion (src + off) m) ∗
          A.pool lim st sf) ∗ Frame) := by
      refine Entails.trans (sepConj_mono_left hrec) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWP.weaken_pre hpost_ent ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hvm_sf
      ⟨htr_sf.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩
  · intro _ _ _ ho
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at ho
    exact (not_satisfies_false_sepConj ho).elim

/-! ## 2. Envelope & Spec Definitions for Arm 5 (`States.noHeaderReceived`) -/

/-- Tight allocator event envelope of `<States>::into_pb` on Arm 5 (`States.noHeaderReceived`):
    identical to `<PolyDecoder>::into_pb` on `s.receiving_hdr`. -/
def NoHeaderReceivedEnv {F : ShaCompress}
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F)) : List AllocEvent → Prop :=
  DecoderIntoPbEnv s.receiving_hdr

abbrev statesIntoPbNoHeaderReceivedSpec
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (b : BitVec 64)
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantSpecOfEnv M A lim F b (.noHeaderReceived s) (NoHeaderReceivedEnv s)

/-! ## 3. Step Lemmas for Arm 5 (`States.noHeaderReceived`, tag `7`) -/

/-- Step 1 of Arm 5 (`+60 -> +96 -> +1108 -> +1124 -> memcpy`) with `VmPreserved` pool transport. -/
theorem states_into_pb_noHeaderReceived_pre1
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out stA : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 60#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1520#64)
    (hx29 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s1.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s1.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s1.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s1.readReg64 .x20 = stA)
    (hx19 : s1.readReg64 .x19 = out)
    (hx8 : s1.readReg64 .x8 = 7#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (Rest : SepProp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy")) s1
      (statesIntoPbJumpTableAt b ∗ A.pool lim st s1 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ statesIntoPbJumpTableAt b ∗ A.pool lim st s2 ∗ Rest) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1128#64 ∧
        s2.readReg64 .x0 = s0.sp - 1360#64 ∧
        s2.readReg64 .x1 = stA + 8#64 ∧
        (s2.readReg64 .x2).toNat = 456 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x28 = s0.sp - 256#64 ∧
        s2.readReg64 .x26 = s0.sp - 480#64 ∧
        s2.readReg64 .x21 = s0.sp - 1360#64 ∧
        s2.readReg64 .x20 = stA ∧
        s2.readReg64 .x19 = out ∧
        TraceCalleeSaved s2 s0 ∧
        VmPreserved s1 s2) := by
  rcases htr1 with ⟨htr1, hvregs⟩
  let Rest' : SepProp := A.pool lim st s1 ∗ Rest
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  have hwp : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy")) s1
      (statesIntoPbJumpTableAt b ∗ Rest')
      (fun s2 P2 =>
        VmPreserved s1 s2 ∧
        (P2 ⊢ statesIntoPbJumpTableAt b ∗ Rest') ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1128#64 ∧
         s2.readReg64 .x0 = s0.sp - 1360#64 ∧
         s2.readReg64 .x1 = stA + 8#64 ∧
         (s2.readReg64 .x2).toNat = 456 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x28 = s0.sp - 256#64 ∧
         s2.readReg64 .x26 = s0.sp - 480#64 ∧
         s2.readReg64 .x21 = s0.sp - 1360#64 ∧
         s2.readReg64 .x20 = stA ∧
         s2.readReg64 .x19 = out ∧
         TraceCalleeSaved s2 s0)) := by
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
      statesIntoPbJumpTableAt, statesIntoPbJumpTableBytes, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [hfn_eq] at hpc1
    simp only [hfn_eq]
    apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved
    have hadrp := fnAddr_adrp_5ce6c (H := trapHooks) hb
    dsimp only [statesIntoPbName] at hadrp
    into_pb_fetches_range b trapHooks 60 80
    into_pb_fetches_range b trapHooks 1108 20
    generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_done
  dsimp only [Rest'] at hwp
  refine SepWP.mono hwp fun s2 P2 _ _
    ⟨hvm2, hP2, hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx21_2, hx20_2, hx19_2, htr2⟩ => ?_
  refine ⟨?_, hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx21_2, hx20_2, hx19_2, htr2, hvm2⟩
  rw [A.pool_of_vmPreserved hvm2]
  exact hP2

/-- Step 2 of Arm 5 (`+1128 -> +1172 -> PolyDecoder::into_pb`) with `VmPreserved` pool transport. -/
theorem states_into_pb_noHeaderReceived_pre2
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s2 : State) (out stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 epoch : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1128#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 1520#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s2.readReg64 .x28 = s0.sp - 256#64)
    (hx26 : s2.readReg64 .x26 = s0.sp - 480#64)
    (hx21 : s2.readReg64 .x21 = s0.sp - 1360#64)
    (hx20 : s2.readReg64 .x20 = stA)
    (hx19 : s2.readReg64 .x19 = out)
    (htr2 : TraceCalleeSaved s2 s0)
    (Rest : SepProp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64) s2
      (cells (s0.sp - 256#64) 6 ∗
       ((s0.sp - 1312#64) ↦₆₄ epoch) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
       A.pool lim st s2 ∗ Rest)
      (fun s3 P3 =>
        (P3 ⊢
          (((s0.sp - 256#64) ↦₆₄ a0) ∗ ((s0.sp - 248#64) ↦₆₄ a1) ∗
           ((s0.sp - 240#64) ↦₆₄ a2) ∗ ((s0.sp - 232#64) ↦₆₄ a3) ∗
           ((s0.sp - 224#64) ↦₆₄ a4) ∗ ((s0.sp - 216#64) ↦₆₄ a5)) ∗
          ((s0.sp - 1312#64) ↦₆₄ epoch) ∗
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
           ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
           ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
          A.pool lim st s3 ∗ Rest) ∧
        s3.sp = s0.sp - 1520#64 ∧
        s3.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1176#64 ∧
        s3.readReg64 .x0 = s0.sp - 480#64 ∧
        s3.readReg64 .x1 = s0.sp - 1304#64 ∧
        s3.readReg64 .x29 = s0.sp - 96#64 ∧
        s3.readReg64 .x26 = s0.sp - 480#64 ∧
        s3.readReg64 .x20 = epoch ∧
        s3.readReg64 .x19 = out ∧
        TraceCalleeSaved s3 s0 ∧
        VmPreserved s2 s3) := by
  rcases htr2 with ⟨htr2, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  cells_unfold
  wp_pull_exists
  rename_i m0 m1 m2 m3 m4 m5
  let Rest' : SepProp := A.pool lim st s2 ∗ Rest
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  have hwp : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64) s2
      ((((s0.sp - 256#64) ↦₆₄ m0) ∗ ((s0.sp - 248#64) ↦₆₄ m1) ∗
        ((s0.sp - 240#64) ↦₆₄ m2) ∗ ((s0.sp - 232#64) ↦₆₄ m3) ∗
        ((s0.sp - 224#64) ↦₆₄ m4) ∗ ((s0.sp - 216#64) ↦₆₄ m5)) ∗
       ((s0.sp - 1312#64) ↦₆₄ epoch) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
       Rest')
      (fun s3 P3 =>
        VmPreserved s2 s3 ∧
        (P3 ⊢
          (((s0.sp - 256#64) ↦₆₄ a0) ∗ ((s0.sp - 248#64) ↦₆₄ a1) ∗
           ((s0.sp - 240#64) ↦₆₄ a2) ∗ ((s0.sp - 232#64) ↦₆₄ a3) ∗
           ((s0.sp - 224#64) ↦₆₄ a4) ∗ ((s0.sp - 216#64) ↦₆₄ a5)) ∗
          ((s0.sp - 1312#64) ↦₆₄ epoch) ∗
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
           ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
           ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
          Rest') ∧
        (s3.sp = s0.sp - 1520#64 ∧
         s3.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1176#64 ∧
         s3.readReg64 .x0 = s0.sp - 480#64 ∧
         s3.readReg64 .x1 = s0.sp - 1304#64 ∧
         s3.readReg64 .x29 = s0.sp - 96#64 ∧
         s3.readReg64 .x26 = s0.sp - 480#64 ∧
         s3.readReg64 .x20 = epoch ∧
         s3.readReg64 .x19 = out ∧
         TraceCalleeSaved s3 s0)) := by
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
    rw [hfn_eq] at hpc2
    simp only [hfn_eq]
    apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved
    into_pb_fetches_range b trapHooks 1128 48
    generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    refine align_entails_vm (s0 := s2) (Entails.of_eq (by sep_ac_rfl)) ?_
    wp_done
  dsimp only [Rest'] at hwp
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono hwp fun s3 P3 _ _
      ⟨hvm3, hP3, hsp3, hlr3, hx0_3, hx1_3, hx29_3, hx26_3, hx20_3, hx19_3, htr3⟩ => ?_)
  refine ⟨?_, hsp3, hlr3, hx0_3, hx1_3, hx29_3, hx26_3, hx20_3, hx19_3, htr3, hvm3⟩
  rw [A.pool_of_vmPreserved hvm3]
  exact Entails.trans hP3 (Entails.of_eq (by sep_ac_rfl))

/-- Step 3 of Arm 5 (`+1176 -> +1236 -> +1540 -> +1544 -> ret`) with `VmPreserved` pool transport
    and `states_into_pb_epilogue`. -/
theorem states_into_pb_noHeaderReceived_post
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (F : ShaCompress)
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 sf : State) (out stA : BitVec 64)
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpcf : sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1176#64)
    (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 1520#64)
    (hx29 : sf.readReg64 .x29 = s0.sp - 96#64)
    (hx26 : sf.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : sf.readReg64 .x20 = s.uc.epoch)
    (hx19 : sf.readReg64 .x19 = out)
    (htrf : TraceCalleeSaved sf s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
      (cells (s0.sp - 1512#64) 19 ∗
       cells (s0.sp - 440#64) 6 ∗
       cells (s0.sp - 304#64) 6 ∗
       (((s0.sp - 480#64) ↦₆₄ d0) ∗ ((s0.sp - 472#64) ↦₆₄ d1) ∗
        ((s0.sp - 464#64) ↦₆₄ d2) ∗ ((s0.sp - 456#64) ↦₆₄ d3) ∗
        ((s0.sp - 448#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_hdr.intoPb ∗
        memRegion (s0.sp - 1304#64) polyDecoderSize ∗
        A.pool lim st sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       (((s0.sp - 256#64) ↦₆₄ a0) ∗ ((s0.sp - 248#64) ↦₆₄ a1) ∗
        ((s0.sp - 240#64) ↦₆₄ a2) ∗ ((s0.sp - 232#64) ↦₆₄ a3) ∗
        ((s0.sp - 224#64) ↦₆₄ a4) ∗ ((s0.sp - 216#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 208#64) 112 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1360#64) 48 ∗
       ((s0.sp - 1312#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 904#64) 424 ∗
       memRegion (s0.sp - 392#64) 88 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 7#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
       memRegion (stA + 56#64) 408 ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion (stA + 464#64) 464 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTableAt b)
      (fun s_ret P_ret =>
        (P_ret ⊢
          optProtoInnerStateAt A.repAlloc out (States.noHeaderReceived s).into_pb.innerState ∗
          memRegion stA chunkedStatesSize ∗
          statesIntoPbJumpTableAt b ∗
          A.pool lim st s_ret ∗ stackAt s0.sp statesIntoPbStack) ∧
        s_ret.sp = s0.sp ∧
        CalleeSavedPreserved s0 s_ret ∧
        s_ret.trace = s0.trace) := by
  rcases htrf with ⟨htrf, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  cells_unfold
  wp_pull_exists
  rename_i u0 u1 u2 u3 u4 u5
    c5 c6 c7 c8 c9 c10
    w200 w208 w216 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
  have hrejoin880 :
      memRegion (s0.sp - 1360#64) 48 ∗
      ((s0.sp - 1312#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (s0.sp - 1304#64) polyDecoderSize ∗
      memRegion (s0.sp - 904#64) 424 ⊢
      memRegion (s0.sp - 1360#64) 880 := by
    change memRegion (s0.sp - 1360#64) 48 ∗
      ((s0.sp - 1312#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (s0.sp - 1304#64) 400 ∗
      memRegion (s0.sp - 904#64) 424 ⊢
      memRegion (s0.sp - 1360#64) 880
    rw [ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 48) (k := 832)
          (b' := s0.sp - 1312#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1312#64) (n := 8) (k := 824)
          (b' := s0.sp - 1304#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1304#64) (n := 400) (k := 424)
          (b' := s0.sp - 904#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  have hrejoin176 :
      (((s0.sp - 480#64) ↦₆₄ d0) ∗ ((s0.sp - 472#64) ↦₆₄ d1) ∗
       ((s0.sp - 464#64) ↦₆₄ d2) ∗ ((s0.sp - 456#64) ↦₆₄ d3) ∗
       ((s0.sp - 448#64) ↦₆₄ d4) ∗ ((s0.sp - 440#64) ↦₆₄ a0) ∗
       ((s0.sp - 432#64) ↦₆₄ a1) ∗ ((s0.sp - 424#64) ↦₆₄ c7) ∗
       ((s0.sp - 416#64) ↦₆₄ c8) ∗ ((s0.sp - 408#64) ↦₆₄ a4) ∗
       ((s0.sp - 400#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 392#64) 88 ⊢
      memRegion (s0.sp - 480#64) 176 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 88) (k := 88)
          (b' := s0.sp - 392#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 480#64) 11 (by decide)]
    refine sepConj_mono_left ?_
    cells_unfold
    exact Entails.sepExists_right d0 (Entails.sepExists_right d1
      (Entails.sepExists_right d2 (Entails.sepExists_right d3
        (Entails.sepExists_right d4 (Entails.sepExists_right a0
          (Entails.sepExists_right a1 (Entails.sepExists_right c7
            (Entails.sepExists_right c8 (Entails.sepExists_right a4
              (Entails.sepExists_right a5 (Entails.refl _)))))))))))
  have hrejoin160 :
      (((s0.sp - 256#64) ↦₆₄ a0) ∗ ((s0.sp - 248#64) ↦₆₄ a1) ∗
       ((s0.sp - 240#64) ↦₆₄ a2) ∗ ((s0.sp - 232#64) ↦₆₄ a3) ∗
       ((s0.sp - 224#64) ↦₆₄ a4) ∗ ((s0.sp - 216#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 208#64) 112 ⊢
      memRegion (s0.sp - 256#64) 160 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 256#64) (n := 48) (k := 112)
          (b' := s0.sp - 208#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 256#64) 6 (by decide)]
    refine sepConj_mono_left ?_
    cells_unfold
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))
  have hstA := stA_noHeaderReceived_entails_928 stA a0 a1 a2 a3 a4 a5
  have hrejoin_all :
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        d0 d1 d2 d3 d4 a0
        a2 a3 a4 a5 s.uc.epoch w104 w112
        w120 w128 w136 w144 w152 w160 w168 w176
        w184 0#64 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 48 ∗
       ((s0.sp - 1312#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1304#64) polyDecoderSize ∗
       memRegion (s0.sp - 904#64) 424) ∗
      ((((s0.sp - 480#64) ↦₆₄ d0) ∗ ((s0.sp - 472#64) ↦₆₄ d1) ∗
        ((s0.sp - 464#64) ↦₆₄ d2) ∗ ((s0.sp - 456#64) ↦₆₄ d3) ∗
        ((s0.sp - 448#64) ↦₆₄ d4) ∗ ((s0.sp - 440#64) ↦₆₄ a0) ∗
        ((s0.sp - 432#64) ↦₆₄ a1) ∗ ((s0.sp - 424#64) ↦₆₄ c7) ∗
        ((s0.sp - 416#64) ↦₆₄ c8) ∗ ((s0.sp - 408#64) ↦₆₄ a4) ∗
        ((s0.sp - 400#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 392#64) 88) ∗
      ((((s0.sp - 256#64) ↦₆₄ a0) ∗ ((s0.sp - 248#64) ↦₆₄ a1) ∗
        ((s0.sp - 240#64) ↦₆₄ a2) ∗ ((s0.sp - 232#64) ↦₆₄ a3) ∗
        ((s0.sp - 224#64) ↦₆₄ a4) ∗ ((s0.sp - 216#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 208#64) 112) ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      A.pool lim st sf ∗
      (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_hdr.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       ((stA ↦₆₄ 7#64) ∗
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
         ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
         ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
        memRegion (stA + 56#64) 408 ∗
        memRegion (stA + 464#64) 464) ∗
       statesIntoPbJumpTableAt b) ⊢
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        d0 d1 d2 d3 d4 a0
        a2 a3 a4 a5 s.uc.epoch w104 w112
        w120 w128 w136 w144 w152 w160 w168 w176
        w184 0#64 w200 w208 w216 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      A.pool lim st sf ∗
      (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_hdr.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTableAt b) :=
    sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hrejoin880
        (sepConj_mono hrejoin176
          (sepConj_mono hrejoin160
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstA))))))))))
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  have hstep_vm : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1544#64) sf
      ((((s0.sp - 1512#64) ↦₆₄ w200) ∗ ((s0.sp - 1504#64) ↦₆₄ w208) ∗
        ((s0.sp - 1496#64) ↦₆₄ w216) ∗ ((s0.sp - 1488#64) ↦₆₄ w64) ∗
        ((s0.sp - 1480#64) ↦₆₄ w72) ∗ ((s0.sp - 1472#64) ↦₆₄ w80) ∗
        ((s0.sp - 1464#64) ↦₆₄ w88) ∗ ((s0.sp - 1456#64) ↦₆₄ w96) ∗
        ((s0.sp - 1448#64) ↦₆₄ w104) ∗ ((s0.sp - 1440#64) ↦₆₄ w112) ∗
        ((s0.sp - 1432#64) ↦₆₄ w120) ∗ ((s0.sp - 1424#64) ↦₆₄ w128) ∗
        ((s0.sp - 1416#64) ↦₆₄ w136) ∗ ((s0.sp - 1408#64) ↦₆₄ w144) ∗
        ((s0.sp - 1400#64) ↦₆₄ w152) ∗ ((s0.sp - 1392#64) ↦₆₄ w160) ∗
        ((s0.sp - 1384#64) ↦₆₄ w168) ∗ ((s0.sp - 1376#64) ↦₆₄ w176) ∗
        ((s0.sp - 1368#64) ↦₆₄ w184)) ∗
       (((s0.sp - 440#64) ↦₆₄ c5) ∗ ((s0.sp - 432#64) ↦₆₄ c6) ∗
        ((s0.sp - 424#64) ↦₆₄ c7) ∗ ((s0.sp - 416#64) ↦₆₄ c8) ∗
        ((s0.sp - 408#64) ↦₆₄ c9) ∗ ((s0.sp - 400#64) ↦₆₄ c10)) ∗
       (((s0.sp - 304#64) ↦₆₄ u0) ∗ ((s0.sp - 296#64) ↦₆₄ u1) ∗
        ((s0.sp - 288#64) ↦₆₄ u2) ∗ ((s0.sp - 280#64) ↦₆₄ u3) ∗
        ((s0.sp - 272#64) ↦₆₄ u4) ∗ ((s0.sp - 264#64) ↦₆₄ u5)) ∗
       (((s0.sp - 480#64) ↦₆₄ d0) ∗ ((s0.sp - 472#64) ↦₆₄ d1) ∗
        ((s0.sp - 464#64) ↦₆₄ d2) ∗ ((s0.sp - 456#64) ↦₆₄ d3) ∗
        ((s0.sp - 448#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_hdr.intoPb ∗
        memRegion (s0.sp - 1304#64) polyDecoderSize ∗
        A.pool lim st sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       (((s0.sp - 256#64) ↦₆₄ a0) ∗ ((s0.sp - 248#64) ↦₆₄ a1) ∗
        ((s0.sp - 240#64) ↦₆₄ a2) ∗ ((s0.sp - 232#64) ↦₆₄ a3) ∗
        ((s0.sp - 224#64) ↦₆₄ a4) ∗ ((s0.sp - 216#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 208#64) 112 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1360#64) 48 ∗
       ((s0.sp - 1312#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 904#64) 424 ∗
       memRegion (s0.sp - 392#64) 88 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 7#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
       memRegion (stA + 56#64) 408 ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion (stA + 464#64) 464 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTableAt b)
      (fun s2 P2 =>
        VmPreserved sf s2 ∧
        (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          epilogueStagingCells s0.sp
            d0 d1 d2 d3 d4 a0
            a2 a3 a4 a5 s.uc.epoch w104 w112
            w120 w128 w136 w144 w152 w160 w168 w176
            w184 0#64 w200 w208 w216 ∗
          memRegion (s0.sp - 1360#64) 880 ∗
          memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗
          statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗
          A.pool lim st sf ∗
          (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_hdr.intoPb ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           memRegion stA chunkedStatesSize ∗
           statesIntoPbJumpTableAt b)) ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x19 = out ∧
         s2.readReg64 .x22 = 0x8000000000000005#64 ∧
         s2.readReg64 .x21 = a1 ∧
         TraceCalleeSaved s2 s0)) := by
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpcf ⊢
    rw [hfn_eq] at hpcf
    conv => enter [2]; rw [hfn_eq]
    apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved
    into_pb_fetches_range b trapHooks 1176 64
    into_pb_fetches_range b trapHooks 1540 8
    generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    refine align_entails_vm (s0 := sf) (Entails.trans ?_ hrejoin_all) ?_
    · dsimp only [epilogueStagingCells]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  have hstep := SepWP.mono
    (post' := fun s2 P2 =>
      (P2 ⊢
        stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
        epilogueStagingCells s0.sp
          d0 d1 d2 d3 d4 a0
          a2 a3 a4 a5 s.uc.epoch w104 w112
          w120 w128 w136 w144 w152 w160 w168 w176
          w184 0#64 w200 w208 w216 ∗
        memRegion (s0.sp - 1360#64) 880 ∗
        memRegion (s0.sp - 480#64) 176 ∗
        memRegion (s0.sp - 256#64) 160 ∗
        statesIntoPbSavedCells s0 ∗
        memRegion out optProtoInnerStateSize ∗
        A.pool lim st s2 ∗
        (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_hdr.intoPb ∗
         authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         memRegion stA chunkedStatesSize ∗
         statesIntoPbJumpTableAt b)) ∧
      (s2.sp = s0.sp - 1520#64 ∧
       s2.readReg64 .x29 = s0.sp - 96#64 ∧
       s2.readReg64 .x19 = out ∧
       s2.readReg64 .x22 = 0x8000000000000005#64 ∧
       s2.readReg64 .x21 = a1 ∧
       TraceCalleeSaved s2 s0))
    hstep_vm
    fun s2 P2 _ _ ⟨hvm2, hP2, hregs⟩ => ⟨by rw [A.pool_of_vmPreserved hvm2]; exact hP2, hregs⟩
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hstep fun s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx22_2, hx21_2, htr2⟩ => ?_)
  have hep := states_into_pb_epilogue A lim st s0 s2 out
    d0 d1 d2 d3 d4 a0
    a2 a3 a4 a5 s.uc.epoch w104 w112
    w120 w128 w136 w144 w152 w160 w168 w176
    w184 0#64 w200 w208 w216
    (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_hdr.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b)
    hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
  rw [hx22_2, hx21_2] at hep
  refine SepWP.mono hep fun s_ret P_ret _ _ ⟨hPf, hsp_ret, hcs_ret, htr_ret, _⟩ =>
    ⟨?_, hsp_ret, hcs_ret, htr_ret⟩
  refine Entails.trans hPf ?_
  have hout := outWords28_entails_noHeaderReceived A.repAlloc out
    d0 d1 d2 d3 d4 a0 a1 a2 a3 a4 a5
    w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 0#64 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
      0x8000000000000005#64
      d0 d1 d2 d3 d4 a0
      a1 a2 a3 a4 a5 s.uc.epoch w104 w112
      w120 w128 w136 w144 w152 w160 w168 w176
      w184 0#64 w200 w208 w216 ∗
     protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_hdr.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗
     A.pool lim st s_ret ∗ stackAt s0.sp statesIntoPbStack) by sep_ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hout) (Entails.of_eq (by sep_ac_rfl))

/-! ## 4. Top-Level `subroutine_ok` Theorems for Arm 5 (`States.noHeaderReceived`) -/

set_option maxHeartbeats 800000 in
/-- Envelope-parametric `subroutine_ok` for `<States>::into_pb` on `.noHeaderReceived s`
    (Arm 5, tag `7`). -/
theorem states_into_pb_noHeaderReceived_of_env
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hdec : DecoderIntoPbOkExt b M A lim ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionBudgetSpec)
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, NoHeaderReceivedEnv s evs → Env evs) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpecOfEnv M A lim F b (.noHeaderReceived s) Env) := by
  have hdec_raw := sub_ok_decoderIntoPb_raw hdec
  have hmemcpy_raw := sub_ok_memcpy_raw hmemcpy
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb, hfit_outer⟩, hmem⟩
  have hfit_dec : FitsEnv M lim st (DecoderIntoPbAllocEnv s.receiving_hdr) :=
    fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv (FitsEnv.mono hEnv hfit_outer)
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.noHeaderReceived s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_of_env st s0 s0 out stA (.noHeaderReceived s) Env _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedNoHeaderReceived_expose A.repAlloc stA s))) ?_
  wp_pull_exists
  rename_i a0 a1 a2 a3 a4 a5
  have hpro := states_into_pb_prologue_60 A lim st s0 out stA 7#64
    ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
     (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (stA + 64#64) s.receiving_hdr) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTableAt b)
    hsp0_align hpc hrun hx8 hx0
  refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [authenticatorHeap]; sep_ac_rfl))
    (seq_clean_wp hpro fun s1 hpc1 hrun1
      ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _⟩ => ?_)
  rw [stack_1416_split_noHeaderReceived s0.sp]
  have hpre1 := states_into_pb_noHeaderReceived_pre1 A lim st s0 s1 out stA
    hb hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 1360#64) 456 ∗
     memRegion (s0.sp - 904#64) 424 ∗
     memRegion (s0.sp - 480#64) protoPolynomialDecoderSize ∗
     cells (s0.sp - 440#64) 6 ∗
     memRegion (s0.sp - 392#64) 88 ∗
     cells (s0.sp - 304#64) 6 ∗
     cells (s0.sp - 256#64) 6 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 7#64) ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
     (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (stA + 64#64) s.receiving_hdr) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize)
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hpre1 fun s2 hpc2 hrun2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx21_2, hx20_2, hx19_2, htr2, _⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_words : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
    ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5)
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (a + 8#64) s.receiving_hdr
  have hF_src : F_words (stA + 8#64) =
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) := by
    dsimp only [F_words]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 48#64) =
      (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A.repAlloc (stA + 64#64) s.receiving_hdr) := by
    dsimp only [G_dec]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 48#64) =
      (((s0.sp - 1312#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A.repAlloc (s0.sp - 1304#64) s.receiving_hdr) := by
    dsimp only [G_dec]
    simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 48#64 = stA + 56#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy_keep_relocate_wp A lim st hmemcpy_raw
    (k := 48) (m := 408) (n := 456) (off := 48#64)
    (F := F_words) (G := G_dec)
    rfl rfl
    (Relocatable.words6 a0 a1 a2 a3 a4 a5)
    (Relocatable.epoch_polyDecoderAt A.repAlloc s.uc.epoch s.receiving_hdr)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 904#64) 424 ∗
      memRegion (s0.sp - 480#64) protoPolynomialDecoderSize ∗
      cells (s0.sp - 440#64) 6 ∗
      memRegion (s0.sp - 392#64) 88 ∗
      cells (s0.sp - 304#64) 6 ∗
      cells (s0.sp - 256#64) 6 ∗
      memRegion (s0.sp - 208#64) 112 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 7#64) ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      memRegion (stA + 464#64) 464 ∗
      memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTableAt b)
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; sep_ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 _hvm3 htr3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = s0.sp - 1360#64 := hcs3.2.2.1.trans hx21_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpre2 := states_into_pb_noHeaderReceived_pre2 A lim st s0 s3 out stA
    a0 a1 a2 a3 a4 a5 s.uc.epoch
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx21_3 hx20_3 hx19_3 htr3
    (memRegion (s0.sp - 1360#64) 48 ∗
     polyDecoderAt A.repAlloc (s0.sp - 1304#64) s.receiving_hdr ∗
     memRegion (stA + 56#64) 408 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 904#64) 424 ∗
     memRegion (s0.sp - 480#64) protoPolynomialDecoderSize ∗
     cells (s0.sp - 440#64) 6 ∗
     memRegion (s0.sp - 392#64) 88 ∗
     cells (s0.sp - 304#64) 6 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 7#64) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTableAt b)
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hpre2 fun s4 hpc4 hrun4
      ⟨hsp4, hlr4, hx0_4, hx1_4, hx29_4, hx26_4, hx20_4, hx19_4, htr4, _⟩ => ?_)
  refine call_decoderIntoPb_expose_wp hdec_raw st (s0.sp - 480#64) (s0.sp - 1304#64) s.receiving_hdr
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗
      cells (s0.sp - 440#64) 6 ∗
      cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ a0) ∗ ((s0.sp - 248#64) ↦₆₄ a1) ∗
       ((s0.sp - 240#64) ↦₆₄ a2) ∗ ((s0.sp - 232#64) ↦₆₄ a3) ∗
       ((s0.sp - 224#64) ↦₆₄ a4) ∗ ((s0.sp - 216#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 208#64) 112 ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 48 ∗
      ((s0.sp - 1312#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (s0.sp - 904#64) 424 ∗
      memRegion (s0.sp - 392#64) 88 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 7#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
      memRegion (stA + 56#64) 408 ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      memRegion (stA + 464#64) 464 ∗
      memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTableAt b)
    hpc4 hrun4 hsp4 hfsp_align hlr4 htr4 hx0_4 hx1_4 hfit_dec
    (by sep_ac_rfl)
    fun sf evs d0 d1 d2 d3 d4 hpcf hrunf hspf hcsf _hacpf htrf henv_dec => ?_
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_4
  have hx20_f : sf.readReg64 .x20 = s.uc.epoch := hcsf.2.1.trans hx20_4
  have hx26_f : sf.readReg64 .x26 = s0.sp - 480#64 := hcsf.2.2.2.2.2.2.2.1.trans hx26_4
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_4
  have hpost_step := states_into_pb_noHeaderReceived_post A lim (M.stepEvents evs st) F
    s0 sf out stA s a0 a1 a2 a3 a4 a5 d0 d1 d2 d3 d4
    hsp0_align hpcf hrunf hspf hx29_f hx26_f hx20_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_)
    (SepWP.mono hpost_step fun s_ret P_ret _ _ ⟨hPf, hsp_ret, hcs_ret, htr_ret⟩ =>
      ⟨⟨evs, hEnv evs henv_dec, hPf⟩, hsp_ret, hcs_ret, htr_ret⟩)
  simp only [arm64_norm]
  sep_ac_rfl

/-- Verifies `<States>::into_pb` on `.noHeaderReceived s`
    (Arm 5, tag `7`). -/
theorem states_into_pb_noHeaderReceived
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec : DecoderIntoPbOkExt b M A lim ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionBudgetSpec)
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbNoHeaderReceivedSpec M A lim F b s) :=
  states_into_pb_noHeaderReceived_of_env hdec hmemcpy s (fun _ h => h)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aBudget
