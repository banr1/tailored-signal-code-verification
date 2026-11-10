/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Final
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WPp


/-!
# Auxiliary `.rodata`, Early-Return Envelope, & Panic-Polymorphic Phase 1 Wrappers (Block `427`)

Provides `.rodata` extraction/restoration lemmas, early-return budget envelopes, and
panic-polymorphic Phase 1 continuation wrappers for `FinalPlacedBudget`.
-/


@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false


namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement LibsignalRoLoaded lsmpl)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded SendCall VecArg spqrSendResultAt spqrSendStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB Error MlKem PqRatchetState States V1State VersionNegotiationPB
   spqrAuthApi spqrDecodeState spqrPolyApi)
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt optProtoInnerStateAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.States.FromPb (StatesFromPbGhost v1StatePtsBound)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred decodeStateResultAt none2Cap optProtoPqRatchetInnerAt
   optVersionNegotiationPBTailAt relocOptVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.Send
  (chunkedStatesWord0 spqrSendCalleeStack spqrSendSavedRegs statesSendArmOffset)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (lsro_spqrSendFullRoPlacedAt spqrLogLevelZeroPlacedAt spqrSendFullRoPlacedAt
   statesFromPbJumpTablePlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrSendPlacedEntry spqrSendPlacedProg spqrSendStatesJumpTablePlacedAt)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudget
  (decodeStatePlacedSpecXOfPrePostEnv
   spqr_send_from_156_placed spqr_send_from_224_placed spqr_send_from_80_placed
   spqr_send_phase1_step_placed spqr_send_phase1_step_placed_ofEnv
   spqr_send_phase1_step_placed_ofPrePostEnv spqr_send_phase1_step_placed_tight)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (DecodeStatePlacedEnv SpqrSendCoinsEnv StatesFromPbEnv decodeStatePlacedSpecX
   decodeStatePlacedSpecXOfEnv statesFromPbPlacedSpecX statesFromPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
  (call_lscro_calleeStack call_lscro_calleeStack_evs)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoSpqrChainSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (spqrDecodeStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp] do
    Lean.Attribute.erase nm `arm64_norm
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero


/-! ## 1. `.rodata` + Global Invariant (`tokenInitPlacedAt`, `spqrLogLevelZeroPlacedAt`) Helpers -/

/-- `oom`-polymorphic introduction of `spqrSendFullRoPlacedAt` into the precondition of a
    `SepWPp` obligation from `tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗ P` under
    `LibsignalRoLoaded lsmpl s0.mem`. -/
theorem sepWPp_intro_spqrSendFullRoPlacedAt_oom
    {prog : Program} {ret : BitVec 64} {s0 : State} (hro : LibsignalRoLoaded lsmpl s0.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog ret s0 (spqrSendFullRoPlacedAt ∗ P) Q Qp oom) :
    SepWPp prog ret s0 (tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗ P) Q Qp oom := by
  intro R0 hm hL
  have hm_assoc : s0.mem ⊨ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗ (P ∗ R0) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  have hm' : s0.mem ⊨ (spqrSendFullRoPlacedAt ∗ P) ∗ R0 := by
    rw [sepConj_assoc]
    exact lsro_spqrSendFullRoPlacedAt hro hm_assoc
  exact h R0 hm' hL

theorem sepWPp_intro_spqrSendFullRoPlacedAt
    {prog : Program} {ret : BitVec 64} {s0 : State} (hro : LibsignalRoLoaded lsmpl s0.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s0 (spqrSendFullRoPlacedAt ∗ P) Q Qp) :
    SepWPp prog ret s0 (tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗ P) Q Qp :=
  sepWPp_intro_spqrSendFullRoPlacedAt_oom hro h


/-! ## 2. Early-Return `SpqrSendCoinsEnv` Closure Lemmas -/

omit [LibsignalPlacement] in
/-- On `spqrDecodeState = .error _`, `DecodeStatePlacedEnv` embeds directly into `SpqrSendCoinsEnv`. -/
theorem spqrSendCoinsEnv_of_decodeStatePlacedEnv
    (x : SendCall) (outPtr : BitVec 64) {evs_dec : List AllocEvent}
    (hdec : DecodeStatePlacedEnv { st := x.st, outPtr := outPtr } evs_dec) :
    SpqrSendCoinsEnv x evs_dec :=
  SpqrBoundedEvs.mono (by omega) (by dsimp; omega) hdec

omit [LibsignalPlacement] in
/-- On `pq.inner = none`, `DecodeStatePlacedEnv` followed by `FreeOnlyEvs` drop events embeds
    directly into `SpqrSendCoinsEnv`. -/
theorem spqrSendCoinsEnv_of_decodeStatePlacedEnv_append_freeOnly
    (x : SendCall) (outPtr : BitVec 64) {evs_dec evs_drop : List AllocEvent}
    (hdec : DecodeStatePlacedEnv { st := x.st, outPtr := outPtr } evs_dec)
    (hdrop : FreeOnlyEvs evs_drop) :
    SpqrSendCoinsEnv x (evs_dec ++ evs_drop) :=
  SpqrBoundedEvs.mono (by omega) (by dsimp; omega)
    (SpqrBoundedEvs.append hdec (SpqrBoundedEvs.of_freeOnly hdrop))

omit [LibsignalPlacement] in
/-- On `States.from_pb = .error (.err _)`, `DecodeStatePlacedEnv` + `StatesFromPbEnv` + `FreeOnlyEvs`
    embeds into `SpqrSendCoinsEnv` whenever `(V1State.encodeRaw v1).length ≤ 2048`. -/
theorem spqrSendCoinsEnv_of_statesFromPbEnv_of_encodeRaw_le
    (x : SendCall) (outPtr pbA : BitVec 64) (v1 : V1State)
    {evs_dec evs_fpb evs_drop : List AllocEvent}
    (hle : (V1State.encodeRaw v1).length ≤ 2048)
    (hdec : DecodeStatePlacedEnv { st := x.st, outPtr := outPtr } evs_dec)
    (hfpb : StatesFromPbEnv { out := outPtr, pbA := pbA, pb := v1 } evs_fpb)
    (hdrop : FreeOnlyEvs evs_drop) :
    SpqrSendCoinsEnv x ((evs_dec ++ evs_fpb) ++ evs_drop) :=
  SpqrBoundedEvs.mono (by omega) (by dsimp; omega)
    (SpqrBoundedEvs.append (SpqrBoundedEvs.append hdec hfpb) (SpqrBoundedEvs.of_freeOnly hdrop))


/-! ## 3. Budget-Threaded Panic-Polymorphic Call & Phase 1 Continuation Wrappers -/

/-- Budget-threaded (`onOom = ⌜False⌝`) companion of `FinalPlaced.call_lscro_calleeStack_panic`,
    weakening a callee panic condition `φ_callee` into the outer panic predicate `φ_panic` via
    `hpan_imp : φ_callee → φ_panic`. -/
theorem call_lscro_calleeStack_panic {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : State → SepProp} {Q : State → SepProp → Prop} {Fr F : SepProp}
    {φ_pre φ_callee φ_panic : Prop} {φ_post : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜φ_callee ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hpan_imp : φ_callee → φ_panic)
    (hspec_post : ∀ sf, spec.post x s sf = (⌜φ_post sf⌝ ∗ T_post sf ∗ stackAt s.sp n))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  call_lscro_calleeStack (Pan := φ_panic) sp n hle
    hcall hcrl hpc hrun hsp hsp_align htr hlr hspec_pre hφ hP hexit_eq
    (fun sf => Entails.trans (hpan sf)
      (Entails.pure_left fun ⟨hc, htr'⟩ =>
        Entails.pure_right ⟨hpan_imp hc, htr'⟩ (Entails.refl anyHeap)))
    hspec_post hnext hoom_eq

/-- Outer-`∃∗ evs : List AllocEvent` companion of `call_lscro_calleeStack_panic` for budget
    callees whose postcondition quantifies over emitted allocator events. -/
theorem call_lscro_calleeStack_evs_panic {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : List AllocEvent → State → SepProp}
    {Q : State → SepProp → Prop} {Fr F : SepProp}
    {φ_pre φ_callee φ_panic : Prop} {φ_post : List AllocEvent → State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜φ_callee ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hpan_imp : φ_callee → φ_panic)
    (hspec_post : ∀ sf,
      spec.post x s sf = (∃∗ evs : List AllocEvent, ⌜φ_post evs sf⌝ ∗ T_post evs sf ∗ stackAt s.sp n))
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post evs sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post evs sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  call_lscro_calleeStack_evs (Pan := φ_panic) sp n hle
    hcall hcrl hpc hrun hsp hsp_align htr hlr hspec_pre hφ hP hexit_eq
    (fun sf => Entails.trans (hpan sf)
      (Entails.pure_left fun ⟨hc, htr'⟩ =>
        Entails.pure_right ⟨hpan_imp hc, htr'⟩ (Entails.refl anyHeap)))
    hspec_post hnext hoom_eq

/-- Budget-threaded relocatable continuation from `+224` with panic predicate `φ_panic`
    (matching `FinalPlaced.spqr_send_from_224_placed_panic`). -/
theorem spqr_send_from_224_placed_panic {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {φ_panic : Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    {s0 s : State} (st : M.σ) (ret w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB) (v1 : V1State)
    (hpts : v1StatePtsBound v1)
    (hfits : FitsEnv M lim st
      (StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                         pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 224#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (herr_post : ∀ (err : Error) (evs_fpb evs_drop : List AllocEvent),
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                        pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb st)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (st0 : States spqrPolyApi (spqrAuthApi F)) (evs_fpb : List AllocEvent),
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                        pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 → sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = ret → sf.readReg64 .x20 = chunkedStatesWord0 st0 →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool lim (M.stepEvents evs_fpb st) sf ∗
            statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗ Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        optProtoInnerStateAt A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1f20 - 0x190) ∗
        memRegion ret 72 ∗ A.pool lim st s ∗ statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_from_224_placed (Pan := φ_panic) ext hA hfrom_pb hdropChain st ret w0 w1 vn chain v1
    hpts hfits hcrl hsp0_align hpc hrun hsp htr hx19 hx20 hx23 hx26 herr_post hok_next hvregs

/-- Budget-threaded relocatable continuation from `+156` with panic predicate `φ_panic`
    (matching `FinalPlaced.spqr_send_from_156_placed_panic`). -/
theorem spqr_send_from_156_placed_panic {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {φ_panic : Prop}
    (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    {s0 s : State} (st : M.σ) (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (pq : PqRatchetState)
    (hpts_of_v1 : ∀ v1 : V1State, pq.inner = some (.v1 v1) → v1StatePtsBound v1)
    (hfits_from_pb : ∀ v1 : V1State, pq.inner = some (.v1 v1) →
      FitsEnv M lim st
        (StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                           pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 156#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hlen16 : bs16.length = 16)
    (hnone_post : ∀ evs_drop : List AllocEvent, pq.inner = none → FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop st) sf ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (herr_post : ∀ (v1 : V1State) (err : Error) (evs_fpb evs_drop : List AllocEvent),
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                        pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb st)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi F)) (evs_fpb : List AllocEvent),
      pq.inner = some (.v1 v1) → States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                        pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 → sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = ret → sf.readReg64 .x20 = chunkedStatesWord0 st0 →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool lim (M.stepEvents evs_fpb st) sf ∗
            statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗ Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗ (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        optProtoPqRatchetInnerAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) pq.inner ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗ (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        memRegion ret 72 ∗ A.pool lim st s ∗ statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_from_156_placed (Pan := φ_panic) ext h_inner_eq hA hfrom_pb hdropChain st ret
    w0 w1 w2 w3 w30 w38 w40 w48 bs16 pq hpts_of_v1 hfits_from_pb
    hcrl hsp0_align hpc hrun hsp htr hx19 hx20 hx23 hx26 hlen16
    hnone_post herr_post hok_next hvregs

/-- Budget-threaded relocatable continuation from `+80` with panic predicate `φ_panic`
    (matching `FinalPlaced.spqr_send_from_80_placed_panic`). -/
theorem spqr_send_from_80_placed_panic {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {φ_panic : Prop}
    (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    {s0 s : State} (st : M.σ) (ret : BitVec 64) (stBytes : Bytes)
    (hlen : stBytes.length < 2 ^ 32)
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State),
      spqrDecodeState stBytes = .ok pq → pq.inner = some (.v1 v1) →
      FitsEnv M lim st
        (StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                           pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 80#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hdec_err_post : ∀ e : Error, spqrDecodeState stBytes = .error e →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗ A.pool lim st sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hnone_post : ∀ (pq : PqRatchetState) (evs_drop : List AllocEvent),
      spqrDecodeState stBytes = .ok pq → pq.inner = none → FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop st) sf ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error) (evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState stBytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                        pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb st)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st0 : States spqrPolyApi (spqrAuthApi F)) (evs_fpb : List AllocEvent),
      spqrDecodeState stBytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                        pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 → sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = ret → sf.readReg64 .x20 = chunkedStatesWord0 st0 →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool lim (M.stepEvents evs_fpb st) sf ∗
            statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗ Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64) (spqrDecodeState stBytes) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        memRegion ret 72 ∗ A.pool lim st s ∗ statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_from_80_placed (F := F) (K := K) (Pan := φ_panic) ext h_inner_eq hA hfrom_pb hdropChain st
    ret stBytes hlen hfits_from_pb hcrl hsp0_align hpc hrun hsp htr hx19 hx21 hx26
    hdec_err_post hnone_post herr_post hok_next hvregs

/-- Two-envelope (`PreEnvDecode` / `PostEnvDecode`) relocatable full Phase 1 execution of
    `spqr::send::<signal_session_ratchet::Coins>` (Block `427`) with panic predicate `φ_panic`. -/
theorem spqr_send_phase1_step_placed_panic_ofPrePostEnv {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {φ_panic : Prop}
    (ext : String → Option (State → State))
    {PreEnvDecode PostEnvDecode : DecodeStateGhost → List AllocEvent → Prop}
    {EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop}
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hdecode : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfPrePostEnv H_inner M A lim PreEnvDecode PostEnvDecode)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F EnvFromPb)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 : State) (st0 : M.σ) (ret : BitVec 64) (st : VecArg)
    (hlen : st.bytes.length < 2 ^ 32)
    (hfits_decode : FitsEnv M lim st0
      (PreEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      PostEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FitsEnv M lim (M.stepEvents evs_dec st0)
        (EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                     pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = st.v)
    (hdec_err_post : ∀ (e : Error) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .error e →
      PostEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_dec st0) sf ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hnone_post : ∀ (pq : PqRatchetState) (evs_dec evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = none →
      PostEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_dec st0)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error)
        (evs_dec evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      PostEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb (M.stepEvents evs_dec st0))) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi F)) (evs_dec evs_fpb : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st_states →
      PostEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st_states → sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = ret → sf.readReg64 .x20 = chunkedStatesWord0 st_states →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st_states ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool lim (M.stepEvents evs_fpb (M.stepEvents evs_dec st0)) sf ∗
            statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest))
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s0
      (stackAt s0.sp spqrSendStack ∗ st.at A.repAlloc ∗ memRegion ret 72 ∗
        A.pool lim st0 s0 ∗ v1StateJumpTablesPlacedAt ∗ statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_phase1_step_placed_ofPrePostEnv
    (PreEnvDecode := PreEnvDecode) (PostEnvDecode := PostEnvDecode) (EnvFromPb := EnvFromPb)
    (F := F) (K := K) (Pan := φ_panic) ext h_inner_eq hA hdecode hfrom_pb hdropChain
    s0 st0 ret st hlen hfits_decode hfits_from_pb
    hcrl hsp0_align hpc hrun hx0 hx1
    hdec_err_post hnone_post herr_post hok_next

/-- Single-envelope (`EnvDecode` / `EnvFromPb`) relocatable full Phase 1 execution of
    `spqr::send::<Coins>` with panic predicate `φ_panic`. -/
theorem spqr_send_phase1_step_placed_panic_ofEnv {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {φ_panic : Prop}
    (ext : String → Option (State → State))
    {EnvDecode : DecodeStateGhost → List AllocEvent → Prop}
    {EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop}
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hdecode : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecXOfEnv H_inner M A lim EnvDecode)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F EnvFromPb)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 : State) (st0 : M.σ) (ret : BitVec 64) (st : VecArg)
    (hlen : st.bytes.length < 2 ^ 32)
    (hfits_decode : FitsEnv M lim st0
      (EnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      EnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FitsEnv M lim (M.stepEvents evs_dec st0)
        (EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                     pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = st.v)
    (hdec_err_post : ∀ (e : Error) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .error e →
      EnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_dec st0) sf ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hnone_post : ∀ (pq : PqRatchetState) (evs_dec evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = none →
      EnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_dec st0)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error)
        (evs_dec evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      EnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb (M.stepEvents evs_dec st0))) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi F)) (evs_dec evs_fpb : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st_states →
      EnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st_states → sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = ret → sf.readReg64 .x20 = chunkedStatesWord0 st_states →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st_states ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool lim (M.stepEvents evs_fpb (M.stepEvents evs_dec st0)) sf ∗
            statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest))
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s0
      (stackAt s0.sp spqrSendStack ∗ st.at A.repAlloc ∗ memRegion ret 72 ∗
        A.pool lim st0 s0 ∗ v1StateJumpTablesPlacedAt ∗ statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_phase1_step_placed_ofEnv
    (EnvDecode := EnvDecode) (EnvFromPb := EnvFromPb)
    (F := F) (K := K) (Pan := φ_panic) ext h_inner_eq hA hdecode hfrom_pb hdropChain
    s0 st0 ret st hlen hfits_decode hfits_from_pb
    hcrl hsp0_align hpc hrun hx0 hx1
    hdec_err_post hnone_post herr_post hok_next

/-- Peer-seam default (`DecodeStatePlacedEnv` + `StatesFromPbEnv`) relocatable full Phase 1
    execution of `spqr::send::<signal_session_ratchet::Coins>` (Block `427`) with panic predicate
    `φ_panic` (matching `FinalPlaced.spqr_send_phase1_step_placed_panic`). -/
theorem spqr_send_phase1_step_placed_panic {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {φ_panic : Prop}
    (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hdecode : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX H_inner M A lim)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 : State) (st0 : M.σ) (ret : BitVec 64) (st : VecArg)
    (hlen : st.bytes.length < 2 ^ 32)
    (hfits_decode : FitsEnv M lim st0
      (DecodeStatePlacedEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      DecodeStatePlacedEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FitsEnv M lim (M.stepEvents evs_dec st0)
        (StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                           pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = st.v)
    (hdec_err_post : ∀ (e : Error) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .error e →
      DecodeStatePlacedEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_dec st0) sf ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hnone_post : ∀ (pq : PqRatchetState) (evs_dec evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = none →
      DecodeStatePlacedEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_dec st0)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error)
        (evs_dec evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      DecodeStatePlacedEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                        pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb (M.stepEvents evs_dec st0))) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi F)) (evs_dec evs_fpb : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st_states →
      DecodeStatePlacedEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                        pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st_states → sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = ret → sf.readReg64 .x20 = chunkedStatesWord0 st_states →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st_states ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool lim (M.stepEvents evs_fpb (M.stepEvents evs_dec st0)) sf ∗
            statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest))
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s0
      (stackAt s0.sp spqrSendStack ∗ st.at A.repAlloc ∗ memRegion ret 72 ∗
        A.pool lim st0 s0 ∗ v1StateJumpTablesPlacedAt ∗ statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_phase1_step_placed (F := F) (K := K) (Pan := φ_panic) ext h_inner_eq hA hdecode
    hfrom_pb hdropChain s0 st0 ret st hlen hfits_decode hfits_from_pb
    hcrl hsp0_align hpc hrun hx0 hx1 hdec_err_post hnone_post herr_post hok_next

/-- Tight (`spqrDecodeStatePlacedSpec` + `States.FromPb.DefsBudget.statesFromPbPlacedSpecX`)
    relocatable full Phase 1 execution of `spqr::send::<Coins>` with panic predicate `φ_panic`. -/
theorem spqr_send_phase1_step_placed_panic_tight {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {φ_panic : Prop}
    (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hdecode : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec H_inner A lim)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecX M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 : State) (st0 : M.σ) (ret : BitVec 64) (st : VecArg)
    (hlen : st.bytes.length < 2 ^ 32)
    (hfits_decode : FitsEnv M lim st0
      (DecodeStateEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      DecodeStateEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FitsEnv M lim (M.stepEvents evs_dec st0)
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = st.v)
    (hdec_err_post : ∀ (e : Error) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .error e →
      DecodeStateEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_dec st0) sf ∗ stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hnone_post : ∀ (pq : PqRatchetState) (evs_dec evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = none →
      DecodeStateEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_dec st0)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error)
        (evs_dec evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      DecodeStateEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1 evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb (M.stepEvents evs_dec st0))) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi F)) (evs_dec evs_fpb : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st_states →
      DecodeStateEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1 evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st_states → sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = ret → sf.readReg64 .x20 = chunkedStatesWord0 st_states →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st_states ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool lim (M.stepEvents evs_fpb (M.stepEvents evs_dec st0)) sf ∗
            statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest))
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s0
      (stackAt s0.sp spqrSendStack ∗ st.at A.repAlloc ∗ memRegion ret 72 ∗
        A.pool lim st0 s0 ∗ v1StateJumpTablesPlacedAt ∗ statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜φ_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_phase1_step_placed_tight (F := F) (K := K) (Pan := φ_panic) ext h_inner_eq hA hdecode
    hfrom_pb hdropChain s0 st0 ret st hlen hfits_decode hfits_from_pb
    hcrl hsp0_align hpc hrun hx0 hx1 hdec_err_post hnone_post herr_post hok_next

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudgetAux
