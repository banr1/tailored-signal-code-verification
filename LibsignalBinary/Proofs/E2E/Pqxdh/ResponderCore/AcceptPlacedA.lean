/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlaced
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.SharedCodeSym
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Relocatable `Pqxdh::accept` (Block `79`), Part A: Frozen Helpers and `opk = none` Branch

Provides `LibsignalFrozen` stepping, `.rodata` introduction, and Block `207`
`PrivateKey::calculate_agreement` call helpers under `[LibsignalFullPlacement]`, and proves
`pqxdhAccept_opt_fields_opk_none_placed_ok` on `lsProg_79 H` for the `g.inp.opkBSk? = none` branch.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.Shared (pqxdhVecAppendElementsFastSpec)

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
attribute [-arm64_norm] List.append_assoc

structure AcceptCanonTrue (P : Primitives) (inp : AcceptKeysInput) : Prop where
  out : P.isCanonical inp.hdr.ekAPk = true

/-! ## 1. `LibsignalFrozen` Stepping, `.rodata`, & Block `79` Hook Helpers -/

/-- State-indexed wrapper for `LibsignalFrozen pl s.mem` (all `619` blocks of
`libsignalSessionLib` + `.rodata` loaded). -/
structure LsFullFrozenInv (pl : Obj.MultiPlacement) (s : State) : Prop where
  ro : LibsignalRoLoaded pl s.mem
  code : libsignalSessionLib.CodeLoaded pl s.mem

theorem LsFullFrozenInv.of_frozen {pl : Obj.MultiPlacement} {s : State}
    (h : LibsignalFrozen pl s.mem) : LsFullFrozenInv pl s :=
  ⟨h.1, h.2⟩

theorem LsFullFrozenInv.to_frozen {pl : Obj.MultiPlacement} {s : State}
    (h : LsFullFrozenInv pl s) : LibsignalFrozen pl s.mem :=
  ⟨h.ro, h.code⟩

theorem LsFullFrozenInv.to_lscro {pl : Obj.MultiPlacement} {s : State}
    (h : LsFullFrozenInv pl s) : Keys.LsFrozenInv pl s :=
  ⟨LibsignalCodeLoaded.of_codeLoaded h.code, h.ro⟩

theorem LsFullFrozenInv.of_keepsFrozen {pl : Obj.MultiPlacement} {s0 sf : State}
    (h0 : LsFullFrozenInv pl s0) (hk : s0.mem.KeepsFrozen sf.mem) : LsFullFrozenInv pl sf :=
  LsFullFrozenInv.of_frozen (libsignalFrozen_of_keepsFrozen h0.to_frozen hk)

theorem SepWPp.of_sepWP_lsfull {prog : Program} {ret mid : BitVec 64} {pl : Obj.MultiPlacement}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF0 : LsFullFrozenInv pl s)
    (hwp : SepWP prog mid s P
      (fun sm Pm => LsFullFrozenInv pl sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (Φ := LibsignalFrozen pl)
    (fun _ _ h hkf => libsignalFrozen_of_keepsFrozen h hkf)
    hF0.to_frozen
    (SepWP.mono hwp fun _ _ _ _ hnext hfr => hnext (LsFullFrozenInv.of_frozen hfr))

theorem SepWP.of_sepWP_lsfull {prog : Program} {target_pc mid : BitVec 64}
    {pl : Obj.MultiPlacement} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hF0 : LsFullFrozenInv pl s)
    (hwp : SepWP prog (Keys.frozenStop mid) s P
      (fun sm Pm => LsFullFrozenInv pl sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold Keys.frozenStop at hwp
  exact SepWP.seq_frozen (Φ := LibsignalFrozen pl)
    (fun _ _ h hkf => libsignalFrozen_of_keepsFrozen h hkf)
    hF0.to_frozen
    (SepWP.mono hwp fun _ _ _ _ hnext hfr => hnext (LsFullFrozenInv.of_frozen hfr))

theorem SepWP.checkpoint_lsfull {prog : Program} {mid mid' target_pc : BitVec 64}
    {pl : Obj.MultiPlacement} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hnext : LsFullFrozenInv pl s → SepWP prog (Keys.frozenStop mid') s P
        (fun sm Pm => LsFullFrozenInv pl sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog (Keys.frozenStop mid) s P
      (fun sm Pm => LsFullFrozenInv pl sm → SepWP prog target_pc sm Pm post) := by
  refine Keys.SepWP.done_frozen hpc hrun fun hF => ?_
  exact SepWP.of_sepWP_lsfull hF (hnext hF)

theorem subroutine_ok_withLsFrozen_of_withRoSlice {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {roSym : String} {roBytes : List (BitVec 8)} {spec : Spec α}
    (hchk : lsroCheck roSym roBytes = true)
    (h : subroutine_ok prog entry (withLsFrozen pl (withRoSlice (pl.ρ roSym) roBytes spec))) :
    subroutine_ok prog entry (withLsFrozen pl spec) := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun _ _ _ _ hq => ?_)
  · obtain ⟨hfr, hpre⟩ := extract_withLsFrozen hpre
    dsimp only [withLsFrozen, withRoSlice]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    rw [sepConj_assoc]
    exact lsro_intro_chk hfr.1 hchk hpre
  · dsimp only [withLsFrozen, withRoSlice] at hq
    rw [sepConj_assoc] at hq
    exact Satisfies.of_sep_right hq

/-- Lift a `withLsFrozen lsmpl` contract from any block `j < 619` (including mutated blocks
such as Block `79`) to any `callerProg` under `[LibsignalFullPlacement]`. -/
theorem ls_subroutine_ok_withLsFrozen_of_block [LibsignalFullPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsFrozen lsmpl spec))
    (hj : j < 619 := by decide) :
    subroutine_ok callerProg entry (withLsFrozen lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hfr0, _⟩ := extract_withLsFrozen hpre
  have hlt_blocks : j < libsignalSessionLib.blocks.length := by
    rw [libsignalSessionLib_blocks_length]; omega
  have hQL : calleeProg.CodeLoaded s0.mem := by
    rw [hcallee_prog.eq_blockProgram]
    have h := hfr0.2 j hlt_blocks
    rwa [Program.codeLoaded_iff] at h ⊢
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

/-- Convert `libsignalSessionLib.withCodeLoaded lsmpl spec` into `withMemEq m spec` for `wp_call`
using `hcl : libsignalSessionLib.CodeLoaded lsmpl m`. -/
theorem subroutine_ok_withMemEq_of_withCodeLoaded [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α} {m : Memory}
    (h : subroutine_ok prog entry (libsignalSessionLib.withCodeLoaded lsmpl spec))
    (hcl : libsignalSessionLib.CodeLoaded lsmpl m) :
    subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono h
    (fun _ _ s0 hp => by
      have ⟨hm, hpre⟩ := extract_withMemEq hp
      have hcl0 : libsignalSessionLib.CodeLoaded lsmpl s0.mem := hm ▸ hcl
      dsimp only [Obj.MultiPlacedLib.withCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl0, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-- Convert `withLsCodeRoLoaded lsmpl spec` into `withMemEq m spec` for `wp_call`
using `hcro : Keys.LsFrozenInv lsmpl s` (`m = s.mem`). -/
theorem subroutine_ok_withMemEq_of_withLsCodeRoLoaded [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α} {m : Memory}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcro : LibsignalCodeRoLoaded lsmpl m) :
    subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono h
    (fun _ _ s0 hp => by
      have ⟨hm, hpre⟩ := extract_withMemEq hp
      have hcro0 : LibsignalCodeRoLoaded lsmpl s0.mem := hm ▸ hcro
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcro0, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem externAt_79_of_mem [LibsignalFullPlacement] {H : LibsignalHooks}
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by decide) :
    (lsProg_79 H).externAt? (lsρ sym) = H sym := by
  have heq : (lsProg_79 H).externAt? (lsρ sym) = (lsProg_75 H).externAt? (lsρ sym) := by
    rw [(inferInstance : IsLsBlockProg (lsProg_79 H) 79 H).eq_blockProgram,
        (inferInstance : IsLsBlockProg (lsProg_75 H) 75 H).eq_blockProgram,
        ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
          (i := 79) (j := 75) rfl]
  exact heq.trans (keys_ls_externAt?_of_mem hmem (by decide) (by decide))

theorem hook_ok_79_of_mem [LibsignalFullPlacement] {α : Type} {H : LibsignalHooks}
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_79 H) (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((externAt_79_of_mem hmem).trans hf) hok

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

/-! ## 2. `SepWPp_call_hag_placed` for `PrivateKey::calculate_agreement` (Block `207`) -/

/-- Relocatable base specification for `PrivateKey::calculate_agreement` (Block `207`). -/
def acceptCalculateAgreementPlacedBaseSpec (P : Primitives) (A : RustAlloc) :
    Spec (BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64) where
  pre := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s =>
    ⌜s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧ s.readReg64 .x8 = ret ∧ s.sp = sp ∧
      ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗ (ourA ↦ₛ bytesToBv8 ourSk32) ∗
      (theirA ↦ₛ bytesToBv8 theirPk32) ∗ memRegion ret 24 ∗ A.pool ∗
      stackAt sp calculateAgreementStack
  post := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
      pqxdhCalculateAgreementResultAt P A ret ourSk32 theirPk32 ∗ A.pool ∗
      stackAt sp calculateAgreementStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem allowPanic_hag_placed {P : Primitives} {A : RustAlloc} {s0 s : State} {F R : SepProp}
    {x : BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64}
    (htr : s.trace = s0.trace) :
    ∀ sf, sf.status = .Panicked →
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))
      sf ((acceptCalculateAgreementPlacedBaseSpec P A).onPanic x s sf ∗ F) := by
  intro sf _ hm
  dsimp only [acceptCalculateAgreementPlacedBaseSpec] at hm
  exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm

theorem SepWPp.call_lsfull_of_lscro {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : LsFullFrozenInv pl s)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LsFullFrozenInv pl sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [withLsCodeRoLoaded]) :
    SepWPp prog ret s P Q Qp := by
  have hcall' : subroutine_ok prog entry
      { withLsFrozen pl spec with
        post := fun x' s0' sf => ⌜LsFullFrozenInv pl sf⌝ ∗ spec.post x' s0' sf } := by
    refine Arm64.subroutine_ok.of_codeLoaded fun x' R' s0' hpc0 hrun0 hpre0 hsp0 hL0 => ?_
    have ⟨hfr0, hpre_spec⟩ := extract_withLsFrozen hpre0
    have hpre_cro : s0'.mem ⊨ (withLsCodeRoLoaded pl spec).pre x' s0' ∗ R' := by
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨LibsignalCodeRoLoaded.of_libsignalFrozen hfr0, hpre_spec⟩
    obtain ⟨sf, hsteps, hout, -⟩ := hcall.no_fault_before_outcome x' R' s0' hpc0 hrun0 hpre_cro hsp0 hL0
    refine Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨(LsFullFrozenInv.of_frozen hfr0).of_keepsFrozen hsteps.keepsFrozen, hpost⟩
    · exact Or.inr hrest
  refine SepWPp.call_wpp (x := x) (F := F) hcall' hpc hrun hsp hlr
    (fun R hm => by
      dsimp only [withLsFrozen]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hF.to_frozen, ?_⟩
      rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hm⟩)
    (fun sm code R' hex hpost => by
      dsimp only [withLsFrozen] at hpost
      exact hexit sm code R' hex hpost)
    (fun sm hpan _ => hpanic sm hpan)
    (fun sm hpcm hrunm hspm hcsm => ?_)
    (fun sm R' _ hoom_post => by
      dsimp only [withLsFrozen] at hoom_post
      rw [hoom sm] at hoom_post
      exact (not_satisfies_false_sepConj hoom_post).elim)
  have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
  dsimp only
  exact SepWPp.congr_pre (sepConj_assoc _ _ _)
    (SepWPp.pure_left fun hFm => hnext sm hpcm hrunm hspm hsp_alm hcsm hFm)

theorem SepWPp_call_hag_placed [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P_pre : SepProp} {Q Qp : State → SepProp → Prop} {s0 : State} {F : SepProp}
    {ret_pc : BitVec 64} {P : Primitives} {A : RustAlloc}
    (hWF : StructuralPrims P)
    (hag : subroutine_ok prog (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec P A)))
    (hF : LsFullFrozenInv lsmpl s)
    (ourA : BitVec 64) (our : Bytes) (theirA : BitVec 64) (their : Bytes)
    (hpc : s.pc = lsmpl.base 207) (hrun : s.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = s0.sp - 4944#64) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx : s.readReg64 Reg.x0 = ourA ∧ s.readReg64 Reg.x1 = theirA ∧
      s.readReg64 Reg.x8 = s0.sp - 4912#64 ∧ s.sp = s0.sp - 4944#64 ∧
      our.length = 32 ∧ their.length = 32)
    (hP : P_pre = ((ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗
      memRegion (s0.sp - 4912#64) 24 ∗ A.pool ∗
      stackAt (s0.sp - 4944#64) calculateAgreementStack) ∗ F)
    (hpanic : ∀ sf, sf.status = .Panicked →
      Qp sf ((acceptCalculateAgreementPlacedBaseSpec P A).onPanic
        (ourA, our, theirA, their, s0.sp - 4912#64, s0.sp - 4944#64) s sf ∗ F))
    (herr : P.x25519 our their = List.replicate 32 0 →
      ∀ (sf : State) (hi : BitVec 56) (u2 : BitVec 64), sf.pc = ret_pc → sf.status = .Running →
        sf.sp = s0.sp - 4944#64 → CalleeSavedPreserved s sf → sf.trace = s0.trace →
        SepWPp prog ret sf (((s0.sp - 4912#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 4904#64) ↦₆₄ (hi ++ 3#8)) ∗ ((s0.sp - 4896#64) ↦₆₄ u2) ∗
          (ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗
          A.pool ∗ stackAt (s0.sp - 4944#64) calculateAgreementStack ∗ F) Q Qp)
    (hok : P.x25519 our their ≠ List.replicate 32 0 →
      ∀ (sf : State) (dh_ptr : BitVec 64), sf.pc = ret_pc → sf.status = .Running →
        sf.sp = s0.sp - 4944#64 → CalleeSavedPreserved s sf → sf.trace = s0.trace →
        LsFullFrozenInv lsmpl sf →
        SepWPp prog ret sf (((s0.sp - 4912#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 4904#64) ↦₆₄ dh_ptr) ∗ ((s0.sp - 4896#64) ↦₆₄ 32#64) ∗
          (dh_ptr ↦ₛ bytesToBv8 (P.x25519 our their)) ∗ A.live dh_ptr 32 1 ∗
          (ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗
          A.pool ∗ stackAt (s0.sp - 4944#64) calculateAgreementStack ∗ F) Q Qp) :
    SepWPp prog ret s P_pre Q Qp := by
  refine SepWPp.call_lsfull_of_lscro
    (spec := acceptCalculateAgreementPlacedBaseSpec P A)
    (x := (ourA, our, theirA, their, s0.sp - 4912#64, s0.sp - 4944#64))
    hF hag hpc hrun (spAligned_sub_4944 hsp_align hsp_eq) hlr rfl hx hP
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    hpanic
    (fun sf hpc_f hrun_f hsp_f _hsp_al_f hcs_f hF_f => ?_)
  dsimp only [acceptCalculateAgreementPlacedBaseSpec, pqxdhCalculateAgreementResultAt]
  rw [htr, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_sf => ?_
  by_cases hdh : P.x25519 our their = List.replicate 32 0
  · simp only [hdh, ↓reduceIte, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    refine SepWPp.fold (calcErr_entails_at_sub4912 s0.sp) (by sep_focus) ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun u2 => ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun hi => ?_
    simp only [sepConj_assoc]
    exact herr hdh sf hi u2 hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f htr_sf
  · have hdh_bv_len : (bytesToBv8 (P.x25519 our their)).length = 32 := by
      simp [bytesToBv8, hWF.x25519_len our their]
    simp only [hdh, ↓reduceIte, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    refine SepWPp.fold (boxSliceU8_32_entails_at_sub4912 A s0.sp hdh_bv_len) (by sep_focus) ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun dh_ptr => ?_
    simp only [sepConj_assoc]
    exact hok hdh sf dh_ptr hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f htr_sf hF_f

/-! ## 3. Full-Library Frozen Spec & `opk = none` Proof on Block `79` -/

/-- Full-library frozen (`withLsFrozen lsmpl`) contract for `Pqxdh::accept` (Block `79`). -/
def pqxdhAcceptOptFieldsFrozenPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec AcceptFieldsCallGhost :=
  withLsFrozen lsmpl (pqxdhAcceptOptFieldsInnerPlacedSpec P A)

/-- `pqxdhAcceptOptFieldsInnerPlacedSpec` restricted to `g.inp.opkBSk? = none`. -/
def pqxdhAcceptOptFieldsOpkNoneInnerPlacedSpec [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) : Spec AcceptFieldsCallGhost :=
  { pqxdhAcceptOptFieldsInnerPlacedSpec P A with
    pre := fun g s =>
      ⌜g.inp.opkBSk? = none⌝ ∗ (pqxdhAcceptOptFieldsInnerPlacedSpec P A).pre g s }

abbrev acceptHandleRawVecErrorSym : String := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"
abbrev acceptRustDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
abbrev acceptKyberDecapsSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate"

set_option maxHeartbeats 6000000 in
/-- Relocatable `Pqxdh::accept` (Block `79`) on the `g.inp.opkBSk? = none` branch under
`[LibsignalFullPlacement]`. -/
theorem pqxdhAccept_opt_fields_opk_none_placed_ok [LibsignalFullPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec P A)))
    (h_hkdf_extract : PqxdhHkdfExtractPlacedOk P (lsProg_79 H))
    (h_hkdf_expand : PqxdhHkdfExpandMultiInfoPlacedOk P (lsProg_79 H))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustDeallocSpec A))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_decaps : HookSat H acceptKyberDecapsSym (kyberDecapsStubSpec P))
    (h_pan_rawvec : H acceptHandleRawVecErrorSym = some Rust.panicked)
    (h_pan_alloc : H Keys.lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_79 H) (blkPl_79).base
      (withLsFrozen lsmpl (pqxdhAcceptOptFieldsOpkNoneInnerPlacedSpec P A)) := by
  refine subroutine_ok_withLsFrozen_of_withRoSlice
    (roSym := "libsignal_protocol:.rodata..Lanon.393")
    (roBytes := incomingBaseKeyInvalidBytes) (by decide) ?_
  refine subroutine_ok_withLsFrozen_of_withRoSlice
    (roSym := "libsignal_protocol:.rodata..Lanon.352")
    (roBytes := bytesToBv8 infoPqxdh) (by decide) ?_
  have hshim := hook_ok_79_of_mem h_shim (by decide)
  have halloc := hook_ok_79_of_mem h_alloc (by decide)
  have hdealloc := hook_ok_79_of_mem h_dealloc (by decide)
  have hmemcpy := hook_ok_79_of_mem h_memcpy (by decide)
  have hdecaps := hook_ok_79_of_mem h_decaps (by decide)
  have hpan_rawvec :
      (lsProg_79 H).externAt? (lsρ acceptHandleRawVecErrorSym) = some Rust.panicked :=
    (externAt_79_of_mem (by decide)).trans h_pan_rawvec
  have hpan_alloc : (lsProg_79 H).externAt? (lsρ Keys.lsHandleAllocErrorSym) = some Rust.panicked :=
    (externAt_79_of_mem (by decide)).trans h_pan_alloc
  have hext_none := h_hkdf_extract.1
  have hexp' := h_hkdf_expand 12
  simp only [pqxdhHkdfExpandCellsPlacedSpec, cells, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  clear h_shim h_alloc h_dealloc h_memcpy h_decaps h_pan_rawvec h_pan_alloc
    h_hkdf_extract h_hkdf_expand
  unfold withLsFrozen withRoSlice pqxdhAcceptOptFieldsOpkNoneInnerPlacedSpec
    pqxdhAcceptOptFieldsInnerPlacedSpec rustPanicOnOomPlaced
  wpp_init x s0
  rcases x with ⟨inp, argPtr, pqskPtr, ctSlicePtr, ctBufPtr, outPtr⟩
  dsimp only at *
  have hfr0 : LibsignalFrozen lsmpl s0.mem := ‹_›
  have hF0 : LsFullFrozenInv lsmpl s0 := LsFullFrozenInv.of_frozen hfr0
  have hopk_none_in : inp.opkBSk? = none := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = argPtr› ‹s0.readReg64 (.gpr 8#5) = outPtr›
  have hws : WellSizedAcceptKeysInput inp := ‹WellSizedAcceptKeysInput inp›
  rcases hws with ⟨hikBSk, _hikBPk, hspkBSk, _hspkBPk, _hopk_sz, hpqSk, _hpqPk, hikAPk, hekAPk,
    hkemCt⟩
  rw (occs := .pos [1]) [stackAt_pqxdh_accept_top s0.sp]
  refine SepWPp.fold (Entails.of_eq (pqsk_region_phaseA_split s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells4_sub4944_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells10_sub80_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'
  unfold pqxdhAcceptOptFieldsAt
  refine SepWPp.of_sepWP_lsfull hF0 (mid := lsmpl.base 202) ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF0_1; try simp only [arm64_norm] at hF0_1
  refine SepWPp.of_sepWP_lsfull hF0_1 (mid := (blkPl_79).base + 52#64) ?_
  wp_call (subroutine_ok_withMemEq_of_withCodeLoaded
    (spec := ecPubKeyIsCanonicalCallSpec P) h_canon hF0_1.code)
    ⟨s0.readReg64 (.gpr 0#5) + 160#64, inp.hdr.ekAPk⟩
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF1; try simp only [arm64_norm] at hF1
  cases hcanon_b : P.isCanonical inp.hdr.ekAPk
  · have hacc_none : Model.acceptKeys P inp = none :=
      acceptKeys_eq_none_of_not_canonical P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
        hikAPk hekAPk hcanon_b
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = false := hcanon_b
    simp only [hcanon_ec, Bool.false_eq_true, ↓reduceIte] at *
    rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP (mid := (blkPl_79).base + 216#64) ?_
    wp_steps; wp_call hshim (); wp_steps
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call halloc (28, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      (fun halloc0 htr0 => ?_) (fun halloc0 halign0 htr0 => ?_)
    · refine SepWPp.of_sepWP (mid := lsρ acceptHandleRawVecErrorSym) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_lhs) (by convert hpan_rawvec using 2; wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
        (by sep_focus) ?_; sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (incoming_alloc_split _)) (by sep_focus) ?_
      sep_elim_exists'
      refine SepWPp.fold
        (Entails.of_eq (rodata_incoming_split1 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")))
        (by sep_focus) ?_
      apply SepWPp.of_sepWP_ret
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      refine SepWP.fold
        (Entails.of_eq (rodata_incoming_1_to_2 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")))
        (by sep_focus) ?_
      wp_steps
      refine SepWP.fold
        (Entails.of_eq (rodata_incoming_split2 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")).symm)
        (by sep_focus) ?_
      refine SepWP.fold (incoming_overlap_prep _ _ _) (by sep_focus) ?_
      sep_elim_exists'; wp_steps
      refine SepWP.fold (err28_anyHeap_intro A _ _ _) (by sep_focus) ?_
      refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5)) 0x8000000000000018#64
        _ _ _ _ (by decide)) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (pqsk_region_phaseA_merge s0.sp _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
      rw [hacc_none]
      clear h_canon h_agree hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
        hpan_rawvec hpan_alloc
      simp only [sepConj_assoc, *]; wp_done
  · have hsp_align_eq : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_align
    have hsp_orr1 : (s0.sp - 4912#64) ||| 1#64 = s0.sp - 4911#64 := sp_sub4912_orr_one hsp_align_eq
    have hsp_orr2 : (s0.sp - 1744#64) ||| 1#64 = s0.sp - 1743#64 := sp_sub1744_orr_one hsp_align_eq
    obtain ⟨ss, hss, hss_len, hfit_ss⟩ := kyberDecaps_some_and_fitBv8_eq hWF hpqSk hkemCt
    have hdecaps_some : (P.kemDecaps inp.pqspkBSk inp.hdr.kemCt).isSome = true := by simp [hss]
    have hss_bv_len : (bytesToBv8 ss).length = 32 := by simp [bytesToBv8, hss_len]
    have hpqSk_drop_len : ((bytesToBv8 inp.pqspkBSk).drop 1).length = 3167 := by
      simp [bytesToBv8, hpqSk]
    have hkemCt_drop_len : ((bytesToBv8 inp.hdr.kemCt).drop 1).length = 1567 := by
      simp [bytesToBv8, hkemCt]
    obtain ⟨s0_w, s1_w, s2_w, s3_w, -, hss_cells⟩ := exists_unpack64_of_length_32 hss_bv_len
    have hro_dbf : infoPqxdh = INFO_PQXDH := by rfl_kernel
    have hinfo_len : BitVec.ofNat 64 INFO_PQXDH.length = 46#64 := by rfl_kernel
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = true := hcanon_b
    have hcanon_keep : AcceptCanonTrue P inp := ⟨hcanon_b⟩
    simp only [hcanon_ec, ↓reduceIte] at *
    clear hcanon_b hcanon_ec
    have hcanon_b : P.isCanonical inp.hdr.ekAPk = true := hcanon_keep.out
    clear hcanon_keep
    rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP_lsfull hF1 (mid := (blkPl_79).base + 72#64) ?_
    wp_steps; wp_call hshim ()
    wp_steps; have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call halloc (192, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2; try simp only [arm64_norm] at hF2
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      (fun halloc192 htr192 => ?_) (fun halloc192 halign192 htr192 => ?_)
    · refine SepWPp.of_sepWP (mid := lsρ acceptHandleRawVecErrorSym) ?_; wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_lhs) (by convert hpan_rawvec using 2; wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (memRegion_192_init_split _)) (by sep_focus) ?_
      sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (alloc_to_calc_stack s0.sp)) (by sep_focus) ?_
      refine SepWPp.of_sepWP_lsfull hF2 (mid := lsmpl.base 207) ?_; wp_steps
      refine SepWP.fold (Entails.of_eq (pointsTo64_4_allOnes_eq_F_X25519 _)) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF3; try simp only [arm64_norm] at hF3
      refine SepWPp_call_hag_placed hWF h_agree hF3 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
        (s0.readReg64 (.gpr 0#5) + 128#64) inp.hdr.ikAPk (by wp_norm_lhs) (by wp_norm_lhs) hsp_align
        (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 120#64) (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hikAPk⟩
        (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
        (fun hdh1 sf1 hi1 u2_1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
        (fun hdh1 sf1 dh1_ptr hpc1 hrun1 hsp1 hcs1 htr1 hF4 => ?_)
      · have hacc_none : Model.acceptKeys P inp = none :=
          acceptKeys_eq_none_of_dh1_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true› hikAPk
            hekAPk hcanon_b hdh1
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
          hcs29, hvregs1⟩
        simp only [arm64_norm]
          at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
        refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
          (by sep_focus) ?_; sep_elim_exists'
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.fold (vec_err_dh1_merge _) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
        wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
        refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
        refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
          0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
        refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
        rw [hacc_none]
        clear h_canon h_agree hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
          hpan_rawvec hpan_alloc
        simp only [sepConj_assoc, *]; wp_done
      · have hdh1_len : (P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 32 := hWF.x25519_len _ _
        have hdh1_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)).length = 32 := by
          simp [bytesToBv8, hdh1_len]
        have hpfx1_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 64 := by
          simp [F_X25519, hdh1_len]
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
          hcs29, hvregs1⟩
        simp only [arm64_norm]
          at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.of_sepWP_lsfull hF4 (mid := lsmpl.base 207) ?_; wp_steps
        wp_call hmemcpy ⟨_, dh1_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)⟩; wp_steps
        refine SepWP.fold (hdh1_bv_len ▸ pointsToBytes_entails_memRegion dh1_ptr _)
          (by sep_focus) ?_; wp_call hdealloc (dh1_ptr, 32, 1); wp_steps
        refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh1_ptr 32#64) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ F_X25519 (P.x25519 inp.spkBSk
          inp.hdr.ikAPk) 32 (by decide))) (by sep_focus) ?_
        refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF5; try simp only [arm64_norm] at hF5
        refine SepWPp_call_hag_placed hWF h_agree hF5 (s0.readReg64 (.gpr 0#5) + 32#64) inp.ikBSk
          (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
          (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
          (ret_pc := (blkPl_79).base + 304#64) (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hikBSk, hekAPk⟩
          (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
          (fun hdh2 sf2 hi2 u2_2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
          (fun hdh2 sf2 dh2_ptr hpc2 hrun2 hsp2 hcs2 htr2 hF6 => ?_)
        · have hacc_none : Model.acceptKeys P inp = none :=
            acceptKeys_eq_none_of_dh2_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
              hikAPk hekAPk hcanon_b hdh1 hdh2
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
               hcs2_29 hvregs2
          refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
            (by sep_focus) ?_; sep_elim_exists'
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.fold (vec_err_dh2_merge _ hpfx1_len) (by sep_focus) ?_
          apply SepWPp.of_sepWP_ret; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
          refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
          refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
            0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
          refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
          rw [hacc_none]
          clear h_canon h_agree hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
            hpan_rawvec hpan_alloc
          simp only [sepConj_assoc, *]; wp_done
        · have hdh2_len : (P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
          have hdh2_bv_len : (bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)).length = 32 := by
            simp [bytesToBv8, hdh2_len]
          have hpfx2_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
            P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 96 := by simp [F_X25519, hdh1_len, hdh2_len]
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
               hcs2_29 hvregs2
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.of_sepWP_lsfull hF6 (mid := lsmpl.base 207) ?_; wp_steps
          wp_call hmemcpy ⟨_, dh2_ptr, bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)⟩; wp_steps
          refine SepWP.fold (hdh2_bv_len ▸ pointsToBytes_entails_memRegion dh2_ptr _)
            (by sep_focus) ?_; wp_call hdealloc (dh2_ptr, 32, 1); wp_steps
          refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh2_ptr 32#64)
            (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
            P.x25519 inp.spkBSk inp.hdr.ikAPk) (P.x25519 inp.ikBSk inp.hdr.ekAPk) 64
            (by simp only [bytesToBv8, List.length_map, hpfx1_len]))) (by sep_focus) ?_
          refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hF7; try simp only [arm64_norm] at hF7
          refine SepWPp_call_hag_placed hWF h_agree hF7 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
            (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
            (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
            (ret_pc := (blkPl_79).base + 404#64) (by wp_norm_lhs) (by wp_norm_lhs)
            ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hekAPk⟩
            (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
            (fun hdh3 sf3 hi3 u2_3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
            (fun hdh3 sf3 dh3_ptr hpc3 hrun3 hsp3 hcs3 htr3 hF8 => ?_)
          · have hacc_none : Model.acceptKeys P inp = none :=
              acceptKeys_eq_none_of_dh3_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
                hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
            dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
                 hcs3_29 hvregs3
            refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
              (by sep_focus) ?_; sep_elim_exists'
            refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
            refine SepWPp.fold (vec_err_dh3_merge _ hpfx2_len) (by sep_focus) ?_
            apply SepWPp.of_sepWP_ret; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
            refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
            refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
              0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
            refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
              (by sep_focus) ?_; rw [hacc_none]
            clear h_canon h_agree hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
              hpan_rawvec hpan_alloc
            simp only [sepConj_assoc, *]; wp_done
          · have hdh3_len : (P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
            have hdh3_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)).length = 32 := by
              simp [bytesToBv8, hdh3_len]
            have hpfx3_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
              P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 128 :=
              by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len]
            dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
                 hcs3_29 hvregs3
            cases hopk_eq : inp.opkBSk? with
            | some _ => simp [hopk_eq] at hopk_none_in
            | none =>
              have hikm160_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                ss).length = 160 := by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, hss_len]
              have hikm160_bv : BitVec.ofNat 64 (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                ss).length = 160#64 := by rw [hikm160_len]
              have hacc_some : Model.acceptKeys P inp = some (Model.deriveDRKeys P (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss)) :=
                acceptKeys_eq_some_of_opk_none P inp ss ‹inp.trustedPeer = true›
                  ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                  ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hss
              have hprk160_len : (bytesToBv8 (hkdfExtractRef P none (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss))).length = 32 := by
                simp [bytesToBv8, hkdfExtractRef_length]
              have hprk160_len32 : (hkdfExtractRef P none (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss)).length = 32 :=
                hkdfExtractRef_length P none _
              obtain ⟨p0, p1, p2, p3, -, hprk160⟩ := exists_unpack64_of_length_32 hprk160_len
              obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm160, hout160⟩ :=
                exists_unpack64_hkdfDerive96 P hWF (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss)
              simp only [Bool.false_eq_true, ↓reduceIte, emp_sepConj]
              refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
              refine SepWPp.of_sepWP_lsfull hF8 (mid := (blkPl_79).base + 944#64) ?_; wp_steps
              wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩; wp_steps
              refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
                (by sep_focus) ?_; wp_call hdealloc (dh3_ptr, 32, 1)
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk) (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
                (by simp only [bytesToBv8, List.length_map, hpfx2_len]))) (by sep_focus) ?_
              refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp 0#64 dh3_ptr 32#64 0#64)
                (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (pqsk_region_phaseB_split s0.sp)) (by sep_focus) ?_
              sep_elim_exists'
              refine SepWP.fold (Entails.of_eq (kemct_region_phaseB_split s0.sp)) (by sep_focus) ?_
              sep_elim_exists'
              refine SepWP.fold (Entails.of_eq (sub176_split_32_64 s0.sp)) (by sep_focus) ?_
              sep_elim_exists'; wp_steps
              wp_call hmemcpy ⟨s0.sp - 4911#64, pqskPtr + 1#64, (bytesToBv8 inp.pqspkBSk).drop 1⟩
              wp_steps
              wp_call hmemcpy ⟨s0.sp - 1743#64, ctBufPtr + 2#64, (bytesToBv8 inp.hdr.kemCt).drop 1⟩
              refine SepWP.fold (pqsk_head_tail_merge s0.sp hpqSk) (by sep_focus) ?_
              refine SepWP.fold (kemct_head_tail_merge s0.sp hkemCt) (by sep_focus) ?_; wp_steps
              wp_call hdecaps ⟨s0.sp - 4912#64, inp.pqspkBSk, s0.sp - 1744#64, inp.hdr.kemCt,
                s0.sp - 176#64⟩
              wp_steps; wp_call hshim (); wp_steps; wp_call halloc (32, 1)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              intro hF9; try simp only [arm64_norm] at hF9
              refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
                (fun halloc32 htr32 => ?_) (fun halloc32 halign32 htr32 => ?_)
              · refine SepWPp.of_sepWP (mid := lsρ Keys.lsHandleAllocErrorSym) ?_; wp_steps
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                apply SepWPp.panic (by wp_norm_lhs) (by convert hpan_alloc using 2; wp_norm_lhs)
                exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
              · (conv => arg 4; rw [hfit_ss, ss_sub176_eq s0.sp hss_cells, hro_dbf])
                refine SepWPp.fold (pqsk_to_extract_region s0.sp hpqSk) (by sep_focus) ?_
                refine SepWPp.fold (kemct_to_hmac18_region s0.sp hkemCt) (by sep_focus) ?_
                sep_elim_exists'
                refine SepWPp.fold (Entails.of_eq (ss_and_vec128_split _ _)) (by sep_focus) ?_
                sep_elim_exists'; apply SepWPp.of_sepWP_ret; apply SepWP.of_sepWP_lsfull hF9
                wp_steps
                refine SepWP.fold (cells4_to_memRegion32 _ s0_w s1_w s2_w s3_w) (by sep_focus) ?_
                wp_call hdealloc (_, 32, 1)
                refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (ss_vec_add128_merge _ hss_cells) (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk) ss 128 (by simp only [bytesToBv8,
                  List.length_map, hpfx3_len]))) (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (stack_to_kdf s0.sp)) (by sep_focus) ?_; wp_steps
                apply SepWP.checkpoint_lsfull (by wp_norm_lhs) (by wp_norm_lhs)
                intro hF10; try simp only [arm64_norm] at hF10
                have hF10_cro := hF10.to_lscro
                wp_call hext_none (s0.sp - 4912#64, _, F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss, s0.sp - 4944#64)
                refine SepWP.fold (vec_ok_160_merge _ hikm160_len) (by sep_focus) ?_
                refine SepWP.fold (prk_sub4912_eq s0.sp hprk160) (by sep_focus) ?_
                refine SepWP.fold (hmacCore_split_sub4880 P s0.sp _) (by sep_focus) ?_
                sep_elim_exists'; refine SepWP.pure_left_elim fun hhmac160 => ?_; wp_steps
                apply Keys.SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
                intro hF11; try simp only [arm64_norm] at hF11
                have hF11_cro := hF11.to_lscro
                refine SepWP.fold (hmacState_merge_sub1744 P s0.sp _ hhmac160) (by sep_focus) ?_
                (conv => arg 4; simp only [arm64_norm, ← hinfo_len])
                wp_call hexp' (s0.sp - 1744#64, hkdfExtractRef P none (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss), s0.sp - 4912#64,
                  lsmpl.ρ "libsignal_protocol:.rodata..Lanon.352",
                  INFO_PQXDH, s0.sp - 176#64, s0.sp - 4944#64); sep_elim_exists'
                refine SepWP.fold (Entails.of_eq (stack_to_kdf s0.sp).symm) (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (outPtr_ok104_cells_split (s0.readReg64 (.gpr
                  8#5)))) (by sep_focus) ?_; sep_elim_exists'
                refine SepWP.fold (okm_sub176_eq s0.sp hokm160) (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (sub1680_split_32_48 s0.sp)) (by sep_focus) ?_
                sep_elim_exists'; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
                refine SepWP.fold (outPtr_ok104_cells_merge (s0.readReg64 (.gpr 8#5)) hout160)
                  (by sep_focus) ?_
                refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (sub4912_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (sub1744_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
                  (by sep_focus) ?_
                refine SepWP.fold (sub176_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
                  (by sep_focus) ?_
                refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
                  (by sep_focus) ?_; (conv => arg 4; rw [← hro_dbf]); rw [hacc_some]
                clear h_canon h_agree hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
                  hpan_rawvec hpan_alloc
                simp only [sepConj_assoc, *]; wp_done

end CryptoVerification.E2E.Pqxdh.ResponderCore
