/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReservePlaced
import ProofLib.SepLogic.WPp

/-!
# Relocatable Scaffolding for Inlined `States::send` `.keysUnsampled` Arm (Block `427`)

Provides `[LibsignalPlacement]` callee contracts for `<Authenticator>::mac_hdr` (Block `342`)
and `do_reserve_and_handle [local#7]` (Block `460`) on `spqrSendPlacedProg ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CryptoVerification.Cli.SpqrV1.Top.Send

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced

variable [LibsignalPlacement]

namespace KeysUnsampledHelpers

/-- Relocatable register and state conditions at the post-`States::send` join point
    `spqrSendPlacedEntry + 3068#64`. -/
structure SpqrSendJoinStatePlaced {F : ShaCompress} (sp : BitVec 64)
    (ext : String → Option (State → State)) (s0 sf : State) (msg : Message spqrPolyApi)
    (st1 : States spqrPolyApi (spqrAuthApi F)) : Prop where
  pc : sf.pc = spqrSendPlacedEntry + 3068#64
  run : sf.status = .Running
  sp_eq : sf.sp = sp
  trace : sf.trace = s0.trace
  x19 : sf.readReg64 .x19 = s0.readReg64 .x19
  x20 : sf.readReg64 .x20 = chunkedStatesWord0 st1
  x22 : sf.readReg64 .x22 = msg.epoch
  x25 : sf.readReg64 .x25 = sp + 0x550#64
  x26 : sf.readReg64 .x26 = sp + 0x1260#64
  x28 : sf.readReg64 .x28 = s0.readReg64 .x28
  vregs : calleeSavedVRegs sf = calleeSavedVRegs s0

/-- Derive `subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") sessionMemcpyRegionSpec`
    from `AllocContractsPlaced A ext`. -/
theorem spqrSend_session_memcpy_region_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") sessionMemcpyRegionSpec := by
  have h0 : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") (sessionMemcpySpec 0) :=
    spqr_hook_ok_of_mem (hA.session_memcpy 0)
  refine subroutine_ok_mono h0 ?_ ?_
  · intro ⟨dst, src, srcBytes⟩ R s hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec, sessionMemcpySpec, libcMemcpySpec, stackAt] at hm ⊢
    rw [ProofLib.memRegion_zero]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro ⟨dst, src, srcBytes⟩ R s0 sf hm
    dsimp only [sessionMemcpyRegionSpec, sessionMemcpySpec, stackAt] at hm ⊢
    rw [ProofLib.memRegion_zero] at hm
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm

/-- Run a non-panicking `SepWP` segment to `mid`, propagating `LibsignalCodeRoLoaded lsmpl` to the continuation. -/
theorem of_sepWP_lscro {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_seq_lscro hcrl h

/-- Call a panic-capable subroutine (`withLsCodeRoLoaded lsmpl spec`) that uses `n ≤ spqrSendCalleeStack` bytes of stack. -/
theorem call_lscro_calleeStack {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : State → SepProp} {Q : State → SepProp → Prop} {Fr F : SepProp}
    {φ_pre : Prop} {φ_post : State → Prop}
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
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hcall' : subroutine_ok prog entry
      { withLsCodeRoLoaded lsmpl spec with
        post := fun x' s0' sf => ⌜LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗ spec.post x' s0' sf } := by
    refine Arm64.subroutine_ok.of_codeLoaded fun x' R s0' hpc0 hrun0 hpre0 hsp0 hL0 => ?_
    have ⟨hcrl0, _⟩ := extract_withLsCodeRoLoaded hpre0
    obtain ⟨sf, hsteps, hout, -⟩ := hcall.no_fault_before_outcome x' R s0' hpc0 hrun0 hpre0 hsp0 hL0
    refine Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hcrl0.of_keepsFrozen hsteps.keepsFrozen, hpost⟩
    · exact Or.inr hrest
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  refine SepWPp.call_wpp (x := x)
    (F := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)
    hcall' hpc hrun hsp_al hlr
    (fun R' hm => by
      change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗
        ((memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) ∗ R')
      rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
      rw [hP, stackAt_spqrSendCallee_split sp n hle] at hm
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)
    (fun sm code R' _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost; rw [hexit_eq code sm] at hpost
      exact allowPanic_not_exited hpost)
    (fun sm _ _ hmFr => by
      dsimp only [withLsCodeRoLoaded] at hmFr; rw [hpan_eq sm] at hmFr
      refine allowPanic_frame ?_ hmFr
      rintro ⟨haf, hpr⟩; unfold allocFailedIn at haf ⊢; rw [htr] at haf hpr; exact ⟨haf, hpr⟩)
    (fun sm hpcm hrunm hspm hcsm => ?_)
    (fun sm R' _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost; rw [hoom_eq sm] at hpost
      exact (allowPanic_not_exited hpost).elim)
  rw [hsp] at hspm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
  have hpeq : (⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ spec.post x s sm) ∗
      (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) =
      ⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
        (⌜φ_post sm⌝ ∗ ((stackAt sp spqrSendCalleeStack ∗ T_post sm) ∗ F)) := by
    rw [hspec_post sm, hsp, stackAt_spqrSendCallee_split sp n hle]; ac_rfl
  dsimp only
  exact SepWPp.congr_pre hpeq (SepWPp.pure_left fun hcrl_m => SepWPp.pure_left fun hφ_post =>
    hnext sm hpcm hrunm hspm hφ_post hcrl_m hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs)

theorem finish_sepWP_lscro {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q onPanic : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hnext : LibsignalCodeRoLoaded lsmpl s.mem → SepWPp prog ret s P' Q onPanic) (hent : P ⊢ P') :
    SepWP prog mid s P (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q onPanic) := by
  refine SepWP.fold hent (sepConj_emp _).symm ?_; rw [sepConj_emp]; exact SepWP.done hpc hrun hnext

end KeysUnsampledHelpers

/-- Lift `subroutine_ok prog entry spec` to `subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec)`. -/
theorem subroutine_ok_withLsCodeRoLoaded {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain h

/-- Lift `subroutine_ok prog entry (withLsCodeLoaded lsmpl spec)` to
    `subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec)`. -/
theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) :=
  CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded h

/-- `<spqr::authenticator::Authenticator>::mac_hdr` (Block `342`) meets
`withLsCodeRoLoaded lsmpl (authMacHdrPinnedSpec F A)` on `spqrSendPlacedProg ext`. -/
def AuthMacHdrPinnedPlacedOkX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 342)
    (withLsCodeRoLoaded lsmpl (authMacHdrPinnedSpec F A))

/-- `alloc::raw_vec::RawVecInner<A>::do_reserve_and_handle [local#7]` (Block `460`) meets
`withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec A)` on `spqrSendPlacedProg ext`. -/
def DoReserve2PlacedOkX (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 460)
    (withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec A))

theorem doReserve2_placed_ok_ext_x {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext) :
    DoReserve2PlacedOkX A ext := by
  have hraw : subroutine_ok ((Cli.SpqrV1.Alloc.Placed.blkPC_460).rebase (Cli.SpqrV1.Alloc.Placed.blkPl_460).base (Rust.withPanics ext))
      (lsmpl.base 460) (withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec A)) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (Cli.SpqrV1.Alloc.do_reserve_2_raw32_placed_ok (A := A) (H := Rust.withPanics ext)
        hA.handle_error hA.shim hA.alloc hA.realloc)
  exact ls_subroutine_ok_of_blockProgram_cro
    (ls_subroutine_ok_to_blockProgram hraw)

end CryptoVerification.Cli.SpqrV1.Top.Send
