/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled3Placed
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Top.Send.ContractsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1FromPbPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1StepsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1TopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure

/-!
# Relocatable Phase 1 Entry Wrapper for `spqr::send::<HookRng>` (Block 124)

Provides `spqrSendFullRoPlacedAt` extraction/restoration and the panic-polymorphic
relocatable Phase 1 step `spqr_send_phase1_step_placed_panic` (`+0..+368`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Send.Placed

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `.rodata` and Global Invariant Extraction -/

/-- Full `.rodata` + global invariant bundle for `spqr::send::<HookRng>` (Block `124`):
    combines `spqrSendRoPlacedAt` with `spqrLogLevelZeroPlacedAt` (`lsLogFilterAddr ↦₆₄ 0#64`).
    Note that `GF.Mul2U16.tokenInitPlacedAt` is already included inside `spqrSendRoPlacedAt`. -/
def spqrSendFullRoPlacedAt : SepProp :=
  spqrSendRoPlacedAt ∗
  spqrLogLevelZeroPlacedAt

/-- Extract `spqrSendFullRoPlacedAt` from `GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗ P`
    under `LibsignalRoLoaded lsmpl s.mem`. -/
theorem lsro_spqrSendFullRoPlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp}
    (hP : s.mem ⊨ GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗ P) :
    s.mem ⊨ spqrSendFullRoPlacedAt ∗ P := by
  have hro' := lsro_spqrSendRoPlacedAt hro hP
  refine Satisfies.mono (Entails.of_eq ?_) hro'
  dsimp only [spqrSendFullRoPlacedAt]
  ac_rfl

/-- Discard the read-only `.rodata` tables in `spqrSendRoPlacedAt`, recovering
    `GF.Mul2U16.tokenInitPlacedAt ∗ P`. -/
theorem spqrSendRoPlacedAt_discard {m : Memory} {P : SepProp}
    (hm : m ⊨ spqrSendRoPlacedAt ∗ P) :
    m ⊨ GF.Mul2U16.tokenInitPlacedAt ∗ P :=
  spqrSendRoPlacedAt_restore hm

/-- Discard the read-only `.rodata` tables in `spqrSendFullRoPlacedAt`, recovering
    `GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗ P`. -/
theorem spqrSendFullRoPlacedAt_restore {m : Memory} {P : SepProp}
    (hm : m ⊨ spqrSendFullRoPlacedAt ∗ P) :
    m ⊨ GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗ P := by
  have hm' : m ⊨ spqrSendRoPlacedAt ∗ (spqrLogLevelZeroPlacedAt ∗ P) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    dsimp only [spqrSendFullRoPlacedAt]
    ac_rfl
  exact spqrSendRoPlacedAt_restore hm'

/-! ## Panic-Polymorphic Relocatable Phase 1 Step -/

/-- Generalization of `call_lscro_calleeStack` allowing an additional panic disjunct `φ_panic`
    (such as `(spqrV1 C.F K).sendPanics x.st.bytes x.rest`) in the continuation's panic clause. -/
theorem call_lscro_calleeStack_panic {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : State → SepProp} {Q : State → SepProp → Prop} {Fr F : SepProp}
    {φ_pre φ_panic : Prop} {φ_post : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
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
          (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  let F_ext := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  have h_step : SepWPp prog ret_pc s P
      (fun sm Pm => Pm = ((withLsCodeRoLoaded lsmpl spec).post x s sm ∗ F_ext) ∧
        sm.sp = s.sp ∧ CalleeSavedPreserved s sm)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
    ProofLib.SepWPp.call_wpp (x := x) (F := F_ext) hcall hpc hrun hsp_al hlr
      (fun R' hm => by
        change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ (F_ext ∗ R')
        rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
        rw [hP, stackAt_spqrSendCallee_split sp n hle] at hm
        exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; ac_rfl)) hm)
      (fun sm code R' _ hpost => by
        change sm.mem ⊨ spec.onExit x code s sm ∗ R' at hpost; rw [hexit_eq code sm] at hpost
        exact allowPanic_not_exited hpost)
      (fun sm _ _ hmFr => by
        change sm.mem ⊨ (spec.onPanic x s sm ∗ F_ext) ∗ Fr at hmFr; rw [hpan_eq sm] at hmFr
        refine allowPanic_frame ?_ hmFr
        rintro ⟨haf, hpr⟩; unfold allocFailedIn at haf ⊢; rw [htr] at haf hpr; exact ⟨Or.inl haf, hpr⟩)
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨rfl, hspm, hcsm⟩)
      (fun sm R' _ hpost => by
        change sm.mem ⊨ spec.onOom x s sm ∗ (F_ext ∗ R') at hpost; rw [hoom_eq sm] at hpost
        exact (allowPanic_not_exited hpost).elim)
  intro R' hm hL
  rcases h_step R' hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, rfl, hspm, hcsm⟩ | hpan | hoom⟩
  · change sm.mem ⊨ (spec.post x s sm ∗ F_ext) ∗ R' at hpost
    rw [sepConj_assoc, hspec_post sm, hsp] at hpost
    have hpost' : sm.mem ⊨ ⌜φ_post sm⌝ ∗ (((stackAt sp spqrSendCalleeStack ∗ T_post sm) ∗ F) ∗ R') := by
      rw [stackAt_spqrSendCallee_split sp n hle]
      exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost'; rcases hpost' with ⟨hφ_post, hpost_mem⟩
    rw [hsp] at hspm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hφ_post (hcrl.of_keepsFrozen hsteps.keepsFrozen)
        hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs R' hpost_mem (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem spqr_send_from_224_placed_panic {F : ShaCompress} {φ_panic : Prop}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (Top.Recv.statesFromPbPlacedSpecX A F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 136)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec A)))
    {s0 s : State} (ret w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB) (v1 : V1State)
    (hpts : v1StatePtsBound v1) {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 224#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0) (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (herr_post : ∀ err : LibsignalSpqrV1.Error,
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ st0 : States spqrPolyApi (spqrAuthApi F),
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
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
            DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
            ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗ Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        Drop.optProtoInnerStateAt A ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1f20 - 0x190) ∗
        memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  refine of_sepWP_lscro (mid := lsmpl.base 333) hcrl ?_
  refine spqr_send_pre_states_from_pb_224_placed hpc hrun hsp hfsp_align htr hx20 ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx19_1 hx20_1 hx21_1 _ hx23_1 _ _ hx26_1 _ _ hx29_1 hx30_1
  refine finish_sepWP_lscro hpc1 hrun1 (fun hcrl1 => ?_) (Entails.refl _)
  rw [hx19] at hx19_1; rw [hx23] at hx23_1; rw [hx26] at hx26_1
  rw [memRegion_190_1f20_split_states_from_pb (s0.sp - 0x1f80#64)]
  refine call_lscro_calleeStack_panic (spec := Top.Recv.statesFromPbPlacedSpecX A F)
    (s0.sp - 0x1f80#64) statesFromPbStackX (by decide)
    (x := ({ out := (s0.sp - 0x1f80#64) + 0x1260#64, pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } : StatesFromPbGhost))
    (φ_pre := s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
      s1.readReg64 .x0 = (s0.sp - 0x1f80#64) + 0xb0#64 ∧ v1StatePtsBound v1)
    (φ_post := fun sf => sf.trace = s1.trace)
    (T_pre := memRegion ((s0.sp - 0x1f80#64) + 0x1260#64) chunkedStatesSize ∗
      Drop.optProtoInnerStateAt A ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
      Top.Recv.statesFromPbJumpTablePlacedAt ∗ A.pool)
    (T_post := fun _ =>
      resultChunkedStatesAt A (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64)
        (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) Drop.optProtoInnerStateSize ∗
      Top.Recv.statesFromPbJumpTablePlacedAt ∗ A.pool)
    (F := memRegion (s0.sp - 0x1f80#64) 0x30 ∗
      (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
      ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
      memRegion ret 72 ∗ spqrSendStatesJumpTablePlacedAt ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
    hfrom_pb hcrl1 hpc1 hrun1 hsp1 hfsp_align htr1 hx30_1
    (by dsimp only [Top.Recv.statesFromPbPlacedSpecX]; rw [hsp1]; ac_rfl)
    ⟨hx8_1, hx0_1, hpts⟩ (by dsimp only [chunkedStatesSize]; ac_rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => by dsimp only [Top.Recv.statesFromPbPlacedSpecX]; rw [hsp1]; ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hcrl2 hx19_2 hx20_2 hx21_2 _ hx23_2 _ _ hx26_2 _ _ hvregs2
  have htr2' : s2.trace = s0.trace := htr2.trans htr1
  have hvregs2' : calleeSavedVRegs s2 = calleeSavedVRegs s0 := (hvregs2.trans hx29_1.2).trans hvregs
  rw [hx19_1] at hx19_2; rw [hx20_1] at hx20_2; rw [hx21_1] at hx21_2
  rw [hx23_1] at hx23_2; rw [hx26_1] at hx26_2
  rcases hres : States.from_pb spqrPolyApi (spqrAuthApi F) v1 with (err | _) | st0
  · refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
      (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
      ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
      (memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) Drop.optProtoInnerStateSize ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190)) ∗
      resultChunkedStatesAt A (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64) (.error (.err err)) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
      memRegion ret 72 ∗ A.pool ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) by ac_rfl)) ?_
    rw [memRegion_b0_rejoin_190 (s0.sp - 0x1f80#64)]
    have herr := spqr_send_states_from_pb_err_step_placed (F := F) hA hdropChain s0 s2 ret w0 w1 vn chain err
      (Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest)
      hcrl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 hvregs2'
    refine sepWPp_of_early_return (SepWP.mono herr ?_) (herr_post err hres)
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    exact ⟨hPf, hsp_f, hcc_f, htr_f.trans htr2'⟩
  · dsimp only [resultChunkedStatesAt]
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      ⌜False⌝ ∗
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
       memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) Drop.optProtoInnerStateSize ∗
       Top.Recv.statesFromPbJumpTablePlacedAt ∗ A.pool ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
       (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
       DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
       ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190) ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
       memRegion ret 72 ∗ spqrSendStatesJumpTablePlacedAt ∗
       spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest) by ac_rfl)) ?_
    exact SepWPp.pure_left fun hfalse => False.elim hfalse
  · rw [← hres]
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) Drop.optProtoInnerStateSize ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190)) ∗
      resultChunkedStatesAt A (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64)
        (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
      spqrSendStatesJumpTablePlacedAt ∗
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
       (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
       DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
       ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
       memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
       spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest) by ac_rfl)) ?_
    rw [memRegion_b0_rejoin_190 (s0.sp - 0x1f80#64),
        memRegion_b0_1260_split_930_950 (s0.sp - 0x1f80#64)]
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      (resultChunkedStatesAt A (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64)
          (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x930#64) 24 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x950#64) 928 ∗
        spqrSendStatesJumpTablePlacedAt) ∗
      (memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x930 - 0xb0) ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x948#64) 8 ∗
       memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1260 - 0xcf0) ∗
       stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
       (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
       DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
       ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
       memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
       spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest) by ac_rfl)) ?_
    refine of_sepWP_lscro (mid := spqrSendPlacedEntry + statesSendArmOffset st0) hcrl2 ?_
    refine spqr_send_states_from_pb_ok_step_placed hA hpc2 hrun2 hsp2 hfsp_align htr2' hx21_2 hx26_2 hres ?_
    intro sf hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f _ hx23_f hx24_f hx25_f hx26_f hx28_f hx29_f
    rw [hx19_2] at hx19_f; rw [hx23_2] at hx23_f
    refine finish_sepWP_lscro hpc_f hrun_f
      (fun hcrl_f => hok_next st0 hres sf hcrl_f hpc_f hrun_f hsp_f htr_f
        hx19_f hx20_f hx21_f hx23_f hx24_f hx25_f hx26_f hx28_f (hx29_f.2.trans hvregs2')) ?_
    refine Entails.trans (Entails.of_eq (show _ =
      ((memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x930 - 0xb0) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x930#64) 24 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x948#64) 8) ∗
       (memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1260 - 0xcf0) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1260#64) 928 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600))) ∗
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
       (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
       DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
       ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
       chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
       memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
       spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
       Rest) by ac_rfl)) ?_
    rw [memRegion_b0_950_and_cf0_1f20_rejoin (s0.sp - 0x1f80#64)]
    exact Entails.of_eq (by ac_rfl)

theorem spqr_send_from_156_placed_panic {H_inner : V1InnerHeapPred} {F : ShaCompress} {φ_panic : Prop}
    (A : RustAlloc) (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st, DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st)
    (hA : AllocContractsPlaced A ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (Top.Recv.statesFromPbPlacedSpecX A F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 136)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec A)))
    {s0 s : State} (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (pq : PqRatchetState)
    (hpts_of_v1 : ∀ v1 : V1State, pq.inner = some (.v1 v1) → v1StatePtsBound v1)
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 156#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0) (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hlen16 : bs16.length = 16)
    (hnone_post : pq.inner = none →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret (some ([], none, [])) ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (herr_post : ∀ (v1 : V1State) (err : LibsignalSpqrV1.Error),
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi F)),
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
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
            DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗ Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗ (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        DecodeState.optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) pq.inner ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗ (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A w0 w1 pq.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  rcases hinner : pq.inner with _ | ⟨⟨v1⟩⟩
  · refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
      (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
      (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗ (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
      (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
      ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
      DecodeState.optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) none ∗
      (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗ (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
      (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
      (relocOptVersionNegotiationPBTailAt A w0 w1 pq.versionNegotiation).1
        ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
      memRegion ret 72 ∗ A.pool ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) by ac_rfl)) ?_
    have hnone := spqr_send_inner_none_step_placed (H_inner := H_inner) hA hdropChain s0 s ret
      w0 w1 w2 w3 w30 w38 w40 w48 bs16 pq.versionNegotiation pq.chain
      (Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest)
      hcrl hsp0_align hpc hrun hsp hx19 hx20 hx23 hlen16 hvregs
    refine sepWPp_of_early_return (SepWP.mono hnone ?_) (hnone_post hinner)
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    exact ⟨hPf, hsp_f, hcc_f, htr_f.trans htr⟩
  · refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
      (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
      (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗ (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
      (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
      ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
      DecodeState.optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) (some (.v1 v1)) ∗
      (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗ (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
      (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
      (relocOptVersionNegotiationPBTailAt A w0 w1 pq.versionNegotiation).1
        ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
       spqrSendStatesJumpTablePlacedAt ∗ Rest) by ac_rfl)) ?_
    refine of_sepWP_lscro (mid := spqrSendPlacedEntry + 224#64) hcrl ?_
    have h224 := spqr_send_inner_some_to_224_placed (ext := ext) h_inner_eq s0 s ret
      w0 w1 w2 w3 w30 w38 w40 w48 bs16 pq.versionNegotiation pq.chain v1
      (memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest)
      hsp0_align hpc hrun hsp hx19 hx20 hx23 hx26 hlen16
    refine SepWP.mono h224 ?_
    intro sm Pm hpc_m hrun_m ⟨hPm, hsp_m, hx19_m, hx20_m, hx23_m, hx26_m, htr_m, hvregs_m⟩ hcrl_m
    refine SepWPp.weaken_pre hPm (SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (spqr_send_from_224_placed_panic A ext hA hfrom_pb hdropChain ret w0 w1
        pq.versionNegotiation pq.chain v1 (hpts_of_v1 v1 hinner)
        hcrl_m hsp0_align hpc_m hrun_m hsp_m (htr_m.trans htr)
        hx19_m hx20_m hx23_m hx26_m
        (fun err hres => herr_post v1 err hinner hres)
        (fun st0 hres => hok_next v1 st0 hinner hres)
        (hvregs_m.trans hvregs)))

theorem spqr_send_from_80_placed_panic {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem} {φ_panic : Prop}
    (A : RustAlloc) (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st, DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st)
    (hA : AllocContractsPlaced A ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (Top.Recv.statesFromPbPlacedSpecX A F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 136)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec A)))
    {s0 s : State} (ret : BitVec 64) (stBytes : Bytes) (hlen : stBytes.length < 2 ^ 32)
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 80#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hdec_err_post : ∀ e : Error,
      spqrDecodeState stBytes = .error e →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hnone_post : ∀ pq : PqRatchetState,
      spqrDecodeState stBytes = .ok pq → pq.inner = none →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret (some ([], none, [])) ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : LibsignalSpqrV1.Error),
      spqrDecodeState stBytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi F)),
      spqrDecodeState stBytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      ∀ w0 w1 : BitVec 64, w0 ≠ DecodeState.none2Cap →
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
            DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗ Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (spqrDecodeState stBytes) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  rcases hdec : spqrDecodeState stBytes with e | pq
  · refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
      decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (.error e) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ memRegion ret 72 ∗
      (A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) by ac_rfl)) ?_
    have herr := spqr_send_decode_state_err_step_placed (H_inner := H_inner) (A := A) (ext := ext)
      s0 s ret e (A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest)
      hsp0_align hpc hrun hsp hx19 hx26 hvregs
    refine sepWPp_of_early_return (SepWP.mono herr ?_) (hdec_err_post e hdec)
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr⟩
  · refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
      decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (.ok pq) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
       spqrSendStatesJumpTablePlacedAt ∗ Rest) by ac_rfl)) ?_
    refine of_sepWP_lscro (mid := spqrSendPlacedEntry + 156#64) hcrl ?_
    have h156 := spqr_send_decode_state_ok_to_156_placed (H_inner := H_inner) hA s0 s ret pq
      (memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest)
      hsp0_align hpc hrun hsp hx19 hx21 hx26
    refine SepWP.mono h156 ?_
    rintro sm Pm hpc_m hrun_m ⟨w0, w1, w2, w3, w30, w38, w40, w48, bs16, hw0, hl16, hPm, hsp_m, hx19_m, hx20_m, hx23_m, hx26_m, htr_m, hvregs_m⟩ hcrl_m
    refine SepWPp.weaken_pre hPm (SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (spqr_send_from_156_placed_panic A ext h_inner_eq hA hfrom_pb hdropChain
        ret w0 w1 w2 w3 w30 w38 w40 w48 bs16 pq
        (fun v1 hinner => v1StatePtsBound_of_spqrDecodeState (F := F) (K := K) hlen hdec hinner)
        hcrl_m hsp0_align hpc_m hrun_m hsp_m (htr_m.trans htr)
        hx19_m hx20_m hx23_m hx26_m hl16 (hnone_post pq hdec)
        (fun v1 err hinner hres => herr_post pq v1 err hdec hinner hres)
        (fun v1 st0 hinner hres => hok_next pq v1 st0 hdec hinner hres w0 w1 hw0)
        (hvregs_m.trans hvregs)))

/-- Full relocatable Phase 1 execution of `spqr::send::<libsignal_session::HookRng>` (Block `124`)
    supporting an additional panic disjunct `φ_panic` in `hok_next`. -/
theorem spqr_send_phase1_step_placed_panic {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem}
    {φ_panic : Prop}
    (A : RustAlloc) (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st, DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st)
    (hA : AllocContractsPlaced A ext)
    (hdecode : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (Top.Recv.decodeStatePlacedSpecX H_inner A)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (Top.Recv.statesFromPbPlacedSpecX A F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 136)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec A)))
    (s0 : State) (ret : BitVec 64) (st : VecArg) (hlen : st.bytes.length < 2 ^ 32)
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = st.v)
    (hdec_err_post : ∀ e : Error,
      spqrDecodeState st.bytes = .error e →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hnone_post : ∀ pq : PqRatchetState,
      spqrDecodeState st.bytes = .ok pq → pq.inner = none →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret (some ([], none, [])) ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : LibsignalSpqrV1.Error),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi F)),
      spqrDecodeState st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      ∀ w0 w1 : BitVec 64, w0 ≠ DecodeState.none2Cap →
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
            DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗ Rest))
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s0
      (stackAt s0.sp spqrSendStack ∗ st.at A ∗ memRegion ret 72 ∗ A.pool ∗
        Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ φ_panic) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  refine of_sepWP_lscro (mid := lsmpl.base 325) hcrl ?_
  have hpro := spqr_send_prologue_to_decode_state_placed (ext := ext) s0 ret st.v
    (st.at A ∗ memRegion ret 72 ∗ A.pool ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
     Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest)
    hsp0_align hpc hrun hx0 hx1
  refine SepWP.mono hpro ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, ⟨_, hvregs1⟩, hx19_1, hx0_1, hx8_1, hx21_1, hx26_1, hx30_1, htr1⟩ hcrl1
  refine SepWPp.weaken_pre hP1 ?_
  rw [memRegion_1f20_split_decode_state (s0.sp - 0x1f80#64)]
  refine call_lscro_calleeStack_panic (spec := Top.Recv.decodeStatePlacedSpecX H_inner A)
    (s0.sp - 0x1f80#64) decodeStateStackX (by decide)
    (x := ({ st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } : DecodeStateGhost))
    (φ_pre := s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
      s1.readReg64 .x0 = st.v ∧ st.bytes.length < 2 ^ 32)
    (φ_post := fun sf => sf.trace = s1.trace)
    (T_pre := Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗ st.at A ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x1260#64) 352 ∗ A.pool)
    (T_post := fun _ => Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗ st.at A ∗
      decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (spqrDecodeState st.bytes) ∗ A.pool)
    (F := memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
      memRegion ret 72 ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
      spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
    hdecode hcrl1 hpc1 hrun1 hsp1 hfsp_align htr1 hx30_1
    (by dsimp only [Top.Recv.decodeStatePlacedSpecX]; rw [hsp1]; ac_rfl)
    ⟨hx8_1, hx0_1, hlen⟩ (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => by dsimp only [Top.Recv.decodeStatePlacedSpecX]; rw [hsp1]; ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hcrl2 hx19_2 _ hx21_2 _ _ _ _ hx26_2 _ _ hvregs2
  rw [hx19_1] at hx19_2; rw [hx21_1] at hx21_2; rw [hx26_1] at hx26_2
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
    decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (spqrDecodeState st.bytes) ∗
    memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
    memRegion ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
    spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
    (st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗ Rest) by ac_rfl)) ?_
  exact spqr_send_from_80_placed_panic (F := F) (K := K) A ext h_inner_eq hA hfrom_pb hdropChain
    ret st.bytes hlen hcrl2 hsp0_align hpc2 hrun2 hsp2 (htr2.trans htr1)
    hx19_2 hx21_2 hx26_2 hdec_err_post hnone_post herr_post hok_next
    (hvregs2.trans hvregs1)

end CryptoVerification.SpqrV1.Top.Send
