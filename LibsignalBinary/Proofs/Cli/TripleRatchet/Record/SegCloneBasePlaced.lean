/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneAssemblePlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Base Combinators and Frame Helpers for CLI `SegClone`

Defines the `LibsignalCodeLoaded`-threading weakest precondition `SepWPpCl`, extern hook and panic
tail lemmas on CLI Block `463`, and relocatable frame-reassembly helpers.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record hiding LibsignalCodeRoLoaded ls_externAt?_226 ls_hook_ok_226 recEntryPlaced recVPCPlaced recMPCPlaced recFPCPlaced recJPCPlaced recExitPlaced recMetaPlaced recFramePlaced tryDecryptPlacedSpec recordDecryptPlacedSpec VStatePlaced MStatePlaced FStatePlaced JStatePlaced SegClonePlacedSpec SegDecryptPlacedSpec SegMismatchPlacedSpec SegTailPlacedSpec SegExitPlacedSpec rootStack_le_of_recordPlacedPre recordDecrypt_placed_region_ok_of_seams
open CryptoVerification.Cli.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps hiding clonePanicPostPlaced segClone_assemble_1_placed segClone_assemble_2_placed segClone_fields_10_to_11_placed
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.Cli.CoinsTape

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `SepWPpCl` Combinators -/

def SepWPpCl [LibsignalPlacement] (prog : Program) (ret : BitVec 64) (s : State) (P : SepProp)
    (Q Qp : State → SepProp → Prop) (oom : State → SepProp := fun _ => ⌜False⌝) : Prop :=
  LibsignalCodeLoaded lsmpl s.mem → SepWPp prog ret s P Q Qp oom

theorem SepWPpCl.of_sepWPp [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog ret s P Q Qp oom) :
    SepWPpCl prog ret s P Q Qp oom :=
  fun _ => h

theorem SepWPpCl.of_sepWP [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpCl prog ret sm Pm Q Qp oom) oom) :
    SepWPpCl prog ret s P Q Qp oom := by
  intro hcl R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hcl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

theorem SepWPpCl.weaken_pre [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hent : P ⊢ P') (h : SepWPpCl prog ret s P' Q Qp oom) :
    SepWPpCl prog ret s P Q Qp oom :=
  fun hcl => SepWPp.weaken_pre hent (h hcl)

theorem SepWPpCl.pure_elim [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPpCl prog ret s P Q Qp oom) :
    SepWPpCl prog ret s (⌜φ⌝ ∗ P) Q Qp oom :=
  fun hcl => SepWPp.pure_elim fun hφ => h hφ hcl

theorem SepWPpCl.exists_elim [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {α : Sort _} {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a, SepWPpCl prog ret s (P a) Q Qp oom) :
    SepWPpCl prog ret s (∃∗ a, P a) Q Qp oom :=
  fun hcl => SepWPp.exists_elim fun a => h a hcl

theorem sepWPpCl_pure_2nd [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpCl prog ret s (P1 ∗ P2) Q Qp) :
    SepWPpCl prog ret s (P1 ∗ ⌜φ⌝ ∗ P2) Q Qp :=
  fun hcl => sepWPp_pure_2nd fun hφ => h hφ hcl

theorem sepWPpCl_pure_3rd [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpCl prog ret s (P1 ∗ P2 ∗ P3) Q Qp) :
    SepWPpCl prog ret s (P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3) Q Qp :=
  fun hcl => sepWPp_pure_3rd fun hφ => h hφ hcl

theorem SepWPpCl.done [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = ret) (hrun : s.status = .Running) (hq : Q s P) :
    SepWPpCl prog ret s P Q Qp oom :=
  fun _ => SepWPp.done hpc hrun hq

theorem SepWPpCl.panic [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s.status = .Running) (hext : prog.externAt? s.pc = some Rust.panicked)
    (hqp : Qp (Rust.panicked s) P) :
    SepWPpCl prog ret s P Q Qp oom :=
  fun _ => SepWPp.panic hrun hext hqp

theorem SepWPpCl.call_frame [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpCl prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPpCl prog ret s P Q Qp oom := by
  intro hcl R hm hL
  have hpre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcl.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom sm R hoom_st hpost⟩)⟩

theorem SepWPpCl.call_frame_cl [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpCl prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPpCl prog ret s P Q Qp oom := by
  intro hcl R hm hL
  have hpre : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_st, hpost⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcl.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom sm R hoom_st hpost⟩)⟩

/-! ## Extern Hooks and Panic Tails on Block `463` -/

structure SegCloneHooks [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) : Prop where
  shim : HookSat H lsRustNoAllocShimSym sessionShimSpec
  alloc : HookSat H lsRustAllocSym (rustAllocSpec A)
  memcpy : HookSat H "memcpy" sessionMemcpyRegionSpec
  handle_error : H lsHandleErrorSym = some Rust.panicked

theorem SegCloneHooks.shim_ok [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hA : SegCloneHooks A H) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.ρ lsRustNoAllocShimSym) sessionShimSpec :=
  ls_hook_ok_226 (by decide) hA.shim

theorem SegCloneHooks.alloc_ok [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hA : SegCloneHooks A H) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.ρ lsRustAllocSym) (rustAllocSpec A) :=
  ls_hook_ok_226 (by decide) hA.alloc

theorem SegCloneHooks.memcpy_ok [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hA : SegCloneHooks A H) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.ρ "memcpy") sessionMemcpyRegionSpec :=
  ls_hook_ok_226 (by decide) hA.memcpy

theorem SegCloneHooks.panic_at_handle_error [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (hA : SegCloneHooks A H) :
    ((blkPC_463).rebase (blkPl_463).base H).externAt? (lsmpl.ρ lsHandleErrorSym) = some Rust.panicked :=
  (ls_externAt?_226 (by decide)).trans hA.handle_error

theorem onPanic_of_allocFailed_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {x : RecordDecryptGhost} {R P_f : SepProp} {s0 sf : State}
    (halloc : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P_f ∗ R) :
    sf.mem ⊨ (recordDecryptPlacedSpec C A ctl uuidTryParse S).onPanic x s0 sf ∗ R := by
  simpa only [recordDecryptPlacedSpec, sepConj_assoc] using
    allowPanic_panicked ⟨Or.inr (Or.inr halloc.1), halloc.2⟩ hm

theorem onPanic_of_callee_panic_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {x : RecordDecryptGhost} {F R : SepProp} {s0 s_call sf : State}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (recordDecryptPlacedSpec C A ctl uuidTryParse S).onPanic x s0 sf ∗ R := by
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨⟨haf, hpre⟩, hm'⟩ := hm
  unfold allocFailedIn at haf
  rw [htr] at haf hpre
  rw [← sepConj_assoc] at hm'
  exact onPanic_of_allocFailed_placed ⟨haf, hpre⟩ hm'

theorem segClone_panic_0x25f8_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_463).base + 0x25f8#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s P Q
      (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hpanic := hA.panic_at_handle_error
  apply SepWPpCl.of_sepWP (mid := lsmpl.ρ lsHandleErrorSym)
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPpCl.panic hrun hpanic fun hm => ?_
  exact onPanic_of_allocFailed_placed
    (SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem segClone_panic_0x2604_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_463).base + 0x2604#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s P Q
      (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hpanic := hA.panic_at_handle_error
  apply SepWPpCl.of_sepWP (mid := lsmpl.ρ lsHandleErrorSym)
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPpCl.panic hrun hpanic fun hm => ?_
  exact onPanic_of_allocFailed_placed
    (SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem segClone_panic_0x2610_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_463).base + 0x2610#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s P Q
      (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hpanic := hA.panic_at_handle_error
  apply SepWPpCl.of_sepWP (mid := lsmpl.ρ lsHandleErrorSym)
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPpCl.panic hrun hpanic fun hm => ?_
  exact onPanic_of_allocFailed_placed
    (SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem segClone_panic_0x261c_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_463).base + 0x261c#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s P Q
      (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hpanic := hA.panic_at_handle_error
  apply SepWPpCl.of_sepWP (mid := lsmpl.ρ lsHandleErrorSym)
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPpCl.panic hrun hpanic fun hm => ?_
  exact onPanic_of_allocFailed_placed
    (SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem segClone_panic_0x2628_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_463).base + 0x2628#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s P Q
      (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hpanic := hA.panic_at_handle_error
  apply SepWPpCl.of_sepWP (mid := lsmpl.ρ lsHandleErrorSym)
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPpCl.panic hrun hpanic fun hm => ?_
  exact onPanic_of_allocFailed_placed
    (SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem segClone_panic_0x2634_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_463).base + 0x2634#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s P Q
      (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hpanic := hA.panic_at_handle_error
  apply SepWPpCl.of_sepWP (mid := lsmpl.ρ lsHandleErrorSym)
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPpCl.panic hrun hpanic fun hm => ?_
  exact onPanic_of_allocFailed_placed
    (SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

/-! ## Frame Remainder and Postcondition -/

def segClone_fixedRestPlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : RecordDecryptGhost) (sp : BitVec 64) : SepProp :=
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
  memRegion (sp + 0x98#64) 4 ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x4b0#64) 48 ∗ memRegion (sp + 0x4e0#64) 0xd0 ∗
  ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
  ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
  errsAt A (sp + 0x5d8#64) [] ∗
  memRegion (sp + 0x658#64) 0x4e8 ∗ memRegion (sp + 0xba0#64) 0x100 ∗
  memRegion (sp + 0xdf8#64) 8 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗
  cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack)

theorem segClone_fixedRest_reassemble_placed [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : RecordDecryptGhost) (sp : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v00 v08 : BitVec 64) (v14 : BitVec 32) (v18 : BitVec 64)
    (v24 v28 v2c : BitVec 32) (v30 : BitVec 64) (v3c : BitVec 32)
    (v40 v48 : BitVec 64) (v54 : BitVec 32) (v58 v60 v68 v70 v78 : BitVec 64) :
    (spillSlotsAt sp v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78 ∗
      chunks96_6QAt (sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
      memRegion (sp + 0x5f0#64) 104 ∗
      ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
      memRegion (sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
      stackAt sp allocHookStack ∗ A.pool ∗
      segClone_fixedRestPlaced A ctl x sp) ⊢
      (recFramePlaced A x sp ∗ errsAt A (sp + 0x5d8#64) [] ∗
        memRegion (sp + 0x4b0#64) 48 ∗ cliTapeAt ctl x.cur x.rest) := by
  refine Entails.trans
    (sepConj_mono
      (spillSlotsAt_entails_memRegion_0x80 sp v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78)
      (sepConj_mono_left (chunks96_6QAt_entails_memRegion (sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5))) ?_
  unfold segClone_fixedRestPlaced recFramePlaced
  rw [memRegion_0x5f0_0x6b0_eq sp, stackAt_root_eq_chainClone sp, stackAt_chainClone_eq_alloc sp]
  exact Entails.of_eq (by ac_rfl)

def segClone_clonePostPlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : RecordDecryptGhost) (s0 sf : State) (P_f : SepProp) : Prop :=
  sf.sp = s0.sp ∧ sf.spAligned = true ∧
    sf.readReg64 .x29 = s0.readReg64 .x29 ∧
    (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
    sf.readReg64 .x9 = x.msg.messageVersion.setWidth 64 ∧
    (P_f ⊢ ∃∗ G₁ : SessionGhost,
      ⌜CloneRel x.G G₁⌝ ∗
      recFramePlaced A x s0.sp ∗
      sessionStateAt A (s0.sp + 0x138#64) x.G x.st ∗
      sessionStateAt A (s0.sp + 0xca0#64) G₁ x.st ∗
      errsAt A (s0.sp + 0x5d8#64) [] ∗
      memRegion (s0.sp + 0x4b0#64) 48 ∗
      cliTapeAt ctl x.cur x.rest)

end CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps
