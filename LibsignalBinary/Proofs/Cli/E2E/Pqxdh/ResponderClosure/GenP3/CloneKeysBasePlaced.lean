/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysBase
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Placed Shared Keys Base (Block `518`)

Relocatable `[LibsignalPlacement]` OOM panic tails (`+0x375c`, `+0x3768`, `+0x3774`) and
OOM-aware `__rust_alloc(sz, 1)` wrappers on `lsProg_518 ext`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-- Mangled symbol name for `__rustc::__rust_no_alloc_shim_is_unstable_v2` in `signal_cli`. -/
abbrev lsShimSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"

/-- Mangled symbol name for `__rustc::__rust_alloc` in `signal_cli`. -/
abbrev lsAllocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"

open Arm64.Obj ProofLib.GenPlacedFetches in
theorem closure_panic_at_handle_error_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked) :
    (lsProg_518 ext).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked :=
  (ls_externAt?_of_mem (prog := lsProg_518 ext) (sym := lsHandleErrorSym)).trans hpanic

theorem closure_shim_placed_ok [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec) :
    subroutine_ok (lsProg_518 ext) (lsρ lsShimSym)
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec := by
  refine subroutine_ok_mono hshim (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  simpa only [noAllocShimSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
    satisfies_pure_sepConj] using hpost

theorem closure_memcpy_4k_placed_ok [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym)
      (withStack sessionMemcpyRegionSpec allocHookStack) :=
  subroutine_ok_withStack_of_subroutine_ok hmemcpy allocHookStack

theorem lscro_of_steps_placed [LibsignalPlacement] {prog : Program} {s sm : State}
    (hsteps : Steps prog s sm) (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
  hcro.of_keepsFrozen hsteps.keepsFrozen

theorem bind_sepWP_lscro_frame_placed [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim hoom | exact (not_satisfies_false_sepConj hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpcm hrunm (lscro_of_steps_placed hsteps hcro) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem call_raw_nopanic_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right; · rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (lscro_of_steps_placed hsteps hcro) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_false] at hpost; exact (allowPanic_not_exited hpost).elim
  · rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

theorem call_lscl_nopanic_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  refine call_raw_nopanic_placed (spec := withLsCodeLoaded lsmpl spec) (x := x)
    (φ := φ ∧ LibsignalCodeLoaded lsmpl s.mem) (T := T) (F := F)
    hcro hcall hpc hrun hsp hlr
    (by dsimp only [withLsCodeLoaded]; rw [hspec, sepConj_assoc, sepConj_comm T, ← sepConj_assoc, pure_sepConj_pure])
    ⟨hφ, hcro.1⟩ hP hpan_false hexit_false hnext hoom_false

theorem call_lscl_oom_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_oom : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (P3P4.PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (P3P4.PanicOomProp s0) := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro.1, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right; · dsimp only [withLsCodeLoaded] at hoom_post; rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim
  · dsimp only [withLsCodeLoaded] at hpost; rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (lscro_of_steps_placed hsteps hcro) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hpan_oom, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm, _, hpost,
      allowPanic_oom_of_prefix (F := F) (htr ▸ List.prefix_refl _)⟩)⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

theorem chainClone3_at_518 [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State)) (hcc : ChainClone3OkPlaced A ext) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 524) (withLsCodeLoaded lsmpl (chainCloneSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_518 ext)
    (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl) hcc) (by decide)

theorem senderChainClone3_at_518 [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State)) (hscc : SenderChainClone3OkPlaced A ext) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 524) (withLsCodeLoaded lsmpl (senderChainCloneSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_518 ext)
    (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl) hscc) (by decide)

/-! ## OOM Panic Tails (`+0x375c`, `+0x3768`, `+0x3774`) and `__rust_alloc(sz, 1)` Wrapper -/

set_option maxHeartbeats 400000 in
theorem oom_tail_375c_placed_ok [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x375c#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_518 ext) ret s P Q (P3P4.PanicOomProp s0) := by
  have hp := closure_panic_at_handle_error_placed ext hpanic
  have hstep : SepWP (lsProg_518 ext) (lsρ lsHandleErrorSym) s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.trace = s.trace) := by
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine bind_sepWP_lscro_frame_placed hcro hstep (emp_sepConj P).symm
    fun s1 hpc1 hrun1 _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hp) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

set_option maxHeartbeats 400000 in
theorem oom_tail_3768_placed_ok [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x3768#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_518 ext) ret s P Q (P3P4.PanicOomProp s0) := by
  have hp := closure_panic_at_handle_error_placed ext hpanic
  have hstep : SepWP (lsProg_518 ext) (lsρ lsHandleErrorSym) s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.trace = s.trace) := by
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine bind_sepWP_lscro_frame_placed hcro hstep (emp_sepConj P).symm
    fun s1 hpc1 hrun1 _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hp) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

set_option maxHeartbeats 400000 in
theorem oom_tail_3774_placed_ok [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (ret v_d0 : BitVec 64) (F : SepProp) (Q : State → SepProp → Prop)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x3774#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_518 ext) ret s (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F) Q (P3P4.PanicOomProp s0) := by
  have hp := closure_panic_at_handle_error_placed ext hpanic
  have hstep : SepWP (lsProg_518 ext) (lsρ lsHandleErrorSym) s ((s.sp + 0xd0#64) ↦₆₄ v_d0)
      (fun s1 P_f => (P_f ⊢ (s.sp + 0xd0#64) ↦₆₄ v_d0) ∧ s1.trace = s.trace) := by
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine bind_sepWP_lscro_frame_placed hcro hstep rfl
    fun s1 hpc1 hrun1 _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hp) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

set_option maxHeartbeats 400000 in
theorem alloc_call_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (s0 s : State) (ret_off oom_off : BitVec 64) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hbl : SepWP (lsProg_518 ext) (lsρ lsAllocSym) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 sz ∧ s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧
        s1.readReg64 .x30 = (blkPl_518).base + ret_off))
    (hcbz : ∀ s2 : State,
      s2.pc = (blkPl_518).base + ret_off → s2.status = .Running → s2.readReg64 .x0 = 0#64 →
      SepWP (lsProg_518 ext) ((blkPl_518).base + oom_off) s2 emp
        (fun s3 P_f => (P_f ⊢ emp) ∧ s3.sp = s2.sp ∧ s3.trace = s2.trace))
    (hoom_tail : ∀ s3 : State,
      StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem →
      s3.pc = (blkPl_518).base + oom_off → s3.status = .Running →
      s3.sp = s.sp → s3.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + ret_off) s3
        ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
        (fun s2 P_f =>
          (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                  A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
          s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
          CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
        (P3P4.PanicOomProp s0)) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + ret_off) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      (P3P4.PanicOomProp s0) := by
  refine bind_sepWP_lscro_frame_placed hcro hbl (emp_sepConj _).symm
    fun s1 hpc1 hrun1 hcro1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hsz_nat : (BitVec.ofNat 64 sz).toNat = sz := Nat.mod_eq_of_lt (by omega)
  have hlay : LayoutOk sz 1 := ⟨hsz_pos, ⟨0, rfl⟩, by omega⟩
  have hφ : (s1.readReg64 .x0).toNat = sz ∧ (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk sz 1 :=
    ⟨by rw [hx0_1, hsz_nat], by rw [hx1_1]; rfl, hlay⟩
  refine call_raw_nopanic_placed (spec := rustAllocSpec A) (x := (sz, 1))
    (T := A.pool ∗ stackAt s.sp allocHookStack) (F := F)
    hcro1 halloc hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [rustAllocSpec]; rw [hsp1])
    hφ (emp_sepConj _) (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := hcs1.trans hcs2
  dsimp only [rustAllocSpec]; rw [hsp1]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · have hoom0 : (s2.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr2 => ?_
    refine bind_sepWP_lscro_frame_placed hcro2 (hcbz s2 hpc2 hrun2 hoom) (emp_sepConj _).symm
      fun s3 hpc3 hrun3 hcro3 ⟨hsp3, htr3⟩ => ?_
    rw [emp_sepConj, ← sepConj_assoc]
    exact hoom_tail s3 hcro3 hpc3 hrun3 (hsp3.trans hsp2) (by rw [htr3, htr2, htr1, htr])
  · have hoom0 : (s2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
    refine SepWPp.done hpc2 hrun2
      ⟨Entails.of_eq (by ac_rfl), hoom, hsp2, htr2.trans htr1, hcs, hcro2⟩

set_option maxHeartbeats 400000 in
theorem alloc_179c_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (v_d0 : BitVec 64) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x179c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x17a0#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F))
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F)) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      (P3P4.PanicOomProp s0) := by
  refine alloc_call_placed_ok ext halloc s0 s 0x17a0#64 0x3774#64 sz
    (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F) hsz_pos hsz_lt hcro hsp_align htr ?_ ?_ ?_
  · wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl, by simp_all [arm64_norm], by simp_all [arm64_norm],
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp_all [arm64_norm]⟩
  · intro s2 hpc2 hrun2 hx0_2
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hcro3 hpc3 hrun3 hsp3 htr3
    have halign3 : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
    rw [show (A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F) =
      ((s3.sp + 0xd0#64) ↦₆₄ v_d0) ∗ ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F) by
      rw [hsp3]; ac_rfl]
    exact oom_tail_3774_placed_ok ext hpanic s0 s3 _ v_d0 _ _ hcro3 hpc3 hrun3 halign3 htr3

set_option maxHeartbeats 400000 in
theorem alloc_18fc_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x18fc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1900#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      (P3P4.PanicOomProp s0) := by
  refine alloc_call_placed_ok ext halloc s0 s 0x1900#64 0x3768#64 sz
    F hsz_pos hsz_lt hcro hsp_align htr ?_ ?_ ?_
  · wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl, by simp_all [arm64_norm], by simp_all [arm64_norm],
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp_all [arm64_norm]⟩
  · intro s2 hpc2 hrun2 hx0_2
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hcro3 hpc3 hrun3 _ htr3
    exact oom_tail_3768_placed_ok ext hpanic s0 s3 _ _ _ hcro3 hpc3 hrun3 htr3

set_option maxHeartbeats 400000 in
theorem alloc_1938_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1938#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x193c#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      (P3P4.PanicOomProp s0) := by
  refine alloc_call_placed_ok ext halloc s0 s 0x193c#64 0x375c#64 sz
    F hsz_pos hsz_lt hcro hsp_align htr ?_ ?_ ?_
  · wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl, by simp_all [arm64_norm], by simp_all [arm64_norm],
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp_all [arm64_norm]⟩
  · intro s2 hpc2 hrun2 hx0_2
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hcro3 hpc3 hrun3 _ htr3
    exact oom_tail_375c_placed_ok ext hpanic s0 s3 _ _ _ hcro3 hpc3 hrun3 htr3

set_option maxHeartbeats 400000 in
theorem alloc_1b48_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1b48#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1b4c#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      (P3P4.PanicOomProp s0) := by
  refine alloc_call_placed_ok ext halloc s0 s 0x1b4c#64 0x3768#64 sz
    F hsz_pos hsz_lt hcro hsp_align htr ?_ ?_ ?_
  · wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl, by simp_all [arm64_norm], by simp_all [arm64_norm],
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp_all [arm64_norm]⟩
  · intro s2 hpc2 hrun2 hx0_2
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hcro3 hpc3 hrun3 _ htr3
    exact oom_tail_3768_placed_ok ext hpanic s0 s3 _ _ _ hcro3 hpc3 hrun3 htr3

set_option maxHeartbeats 400000 in
theorem alloc_1b84_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1b84#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1b88#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      (P3P4.PanicOomProp s0) := by
  refine alloc_call_placed_ok ext halloc s0 s 0x1b88#64 0x375c#64 sz
    F hsz_pos hsz_lt hcro hsp_align htr ?_ ?_ ?_
  · wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl, by simp_all [arm64_norm], by simp_all [arm64_norm],
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp_all [arm64_norm]⟩
  · intro s2 hpc2 hrun2 hx0_2
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hcro3 hpc3 hrun3 _ htr3
    exact oom_tail_375c_placed_ok ext hpanic s0 s3 _ _ _ hcro3 hpc3 hrun3 htr3

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
