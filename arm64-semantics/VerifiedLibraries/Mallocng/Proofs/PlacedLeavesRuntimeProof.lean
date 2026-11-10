/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedCode
public import VerifiedLibraries.Mallocng.Proofs.Internal
import VerifiedLibraries.Mallocng.Proofs.MemcpySym
import VerifiedLibraries.Mallocng.Proofs.MemsetSym

/-!
# Placed Runtime, Lock, and String Leaf Proofs

Cross-block `withCL mmpl` combinators, `CodeLoaded`-preserving store tactics, and contracts for the
non-VM `musl` leaf blocks of `VerifiedLibraries.mallocngLib` (`errno_location`, `syscall_ret`,
`vm_wait`, `memcpy`, `memset`, `lock`, and `unlock`), polymorphic over any hook-free caller
`{P : Program}` with `P.svc = msvc`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## `withCL` Entry Combinator and `CodeLoaded`-Preserving Stores -/

/-- Prove `subroutine_ok prog entry (withCL mpl spec)` from a `subroutine_ok` goal that receives
    `hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mpl m0` at entry without mentioning
    `CodeLoaded` in `post`. -/
theorem subroutine_ok_withCL_of_cl {α : Type} {prog : Program} {entry : BitVec 64}
    {mpl : MultiPlacement} {spec : Spec α}
    (h : ∀ m0 : Memory, VerifiedLibraries.mallocngLib.CodeLoaded mpl m0 →
      subroutine_ok prog entry
        { spec with pre := fun x s0 => ⌜s0.mem = m0⌝ ∗ spec.pre x s0 })
    (h_no_panic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_no_exit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry (withCL mpl spec) := by
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [withCL]
    rw [sepConj_comm (spec.pre x s0), sepConj_assoc]
    exact Entails.refl _
  rw [satisfies_pure_sepConj] at hpre'
  obtain ⟨hcl0, hpre0⟩ := hpre'
  have hpre_eq : s0.mem ⊨ (⌜s0.mem = s0.mem⌝ ∗ spec.pre x s0) ∗ R := by
    rw [sepConj_assoc]
    exact (satisfies_pure_sepConj _ _ _).mpr ⟨rfl, hpre0⟩
  refine ⟨⌜s0.mem = s0.mem⌝ ∗ spec.pre x s0, hpre_eq, ?_⟩
  refine sepWP_mono_cl
    (post := fun sf Pf =>
      (sf.mem ⊨ Pf ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    hcl0 ?_ (fun sf Pf _ _ hcl_f ⟨hq, hsp', hcs'⟩ => ⟨fun hm => ?_, hsp', hcs'⟩)
  · refine SepWP.call_subroutine_frame (F := emp) (h s0.mem hcl0) hpc hrun hsp rfl
      (fun R' hm => by simpa [emp_sepConj] using hm)
      (fun R' sf _ hp => by rw [h_no_panic x s0 sf] at hp; exact not_satisfies_false_sepConj hp)
      (fun R' code sf _ he => by rw [h_no_exit x code s0 sf] at he; exact not_satisfies_false_sepConj he)
      (fun sf hpc' hrun' hsp' hcs' =>
        SepWP.done hpc' hrun' ⟨fun hm => by simpa [sepConj_emp] using hm, hsp', hcs'⟩)
      (fun R' sf _ ho => by simpa [withCL, emp_sepConj] using ho)
  · refine Satisfies.mono ?_ (hq hm)
    dsimp only [withCL]
    rw [sepConj_assoc]
    exact sepConj_mono_right (Entails.pure_right hcl_f (Entails.refl R))

theorem hasWords_blk_of_checkSegment [MallocngMultiPlacement] {i : Nat} (hi : i < 24)
    {ws : List (BitVec 32)} {R : List RelocEntry}
    (hchk : VerifiedLibraries.mallocngLib.blocks[i].checkSegment 0 ws R = true) :
    (mallocngBlockProg mmpl i msvc).hasWords (mbase i)
        (patchRelocs R ws (mbase i) (VerifiedLibraries.mallocngLib.resolve mmpl)) ∧
      ∀ r ∈ R, CodeRelocInRange r.kind
        (mbase i + BitVec.ofNat 64 r.off)
        (addSignedAddr (VerifiedLibraries.mallocngLib.resolve mmpl r.sym) r.addend) := by
  have h := MultiPlacedLib.hasWords_of_checkSegment
    (lib := VerifiedLibraries.mallocngLib) (mpl := mmpl) (i := i)
    (by simpa using hi) (X := fun _ => none) (svc := msvc)
    MallocngMultiPlacement.placeable hchk
  simpa [mallocngBlockProg, mbase, BitVec.add_zero] using h

theorem hasWords_blk_relocFree [MallocngMultiPlacement] {i : Nat} (hi : i < 24)
    {ws : List (BitVec 32)}
    (hchk : VerifiedLibraries.mallocngLib.blocks[i].checkSegment 0 ws [] = true) :
    (mallocngBlockProg mmpl i msvc).hasWords (mbase i) ws := by
  have ⟨hw, _⟩ := hasWords_blk_of_checkSegment hi hchk
  simpa [patchRelocs] using hw

theorem step_str64_perm_kf {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m' := s.mem.write64 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 8 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m' (Memory.perm_write64 _ _ _) (Memory.keepsFrozen_write64 hcan val)) hm'

theorem step_stp64_perm_kf {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2_m1 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  have hcan2 : s.mem.canWrite ea2 8 = true := by
    rwa [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2_m1
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  have hkf : s.mem.KeepsFrozen m2 :=
    (Memory.keepsFrozen_write64 hcan1 v1).trans (Memory.keepsFrozen_write64 hcan2_m1 v2)
  exact SepWP.to_reaches_pc (hnext m2 (by simp [m2, m1]) hkf) hm2

theorem step_str32_perm_kf {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .W32 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg32 rt = val) (hstore : SepStore32 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m' := s.mem.write32 ea val
  have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 4 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .W32 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, htrunc, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m' (Memory.perm_write32 _ _ _) (Memory.keepsFrozen_write32 hcan val)) hm'

scoped elab "wp_close_fetch_cl" : tactic => ProofLib.closeFetchSubgoal none

scoped macro "wp_stp64_cl" m:ident hm:ident hcl_prev:ident hcl_new:ident : tactic => `(tactic| (
  apply step_stp64_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_sep_access); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf
  have $hcl_new:ident := ($hcl_prev:ident).of_keepsFrozen _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

scoped macro "wp_str64_cl" m:ident hm:ident hcl_prev:ident hcl_new:ident : tactic => `(tactic| (
  apply step_str64_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf
  have $hcl_new:ident := ($hcl_prev:ident).of_keepsFrozen _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

scoped macro "wp_str32_cl" m:ident hm:ident hcl_prev:ident hcl_new:ident : tactic => `(tactic| (
  apply step_str32_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf
  have $hcl_new:ident := ($hcl_prev:ident).of_keepsFrozen _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

/-! ## Pure Runtime and Lock Leaves -/

private theorem blk00_errno_perm [MallocngMultiPlacement] :
    subroutine_ok (mallocngBlockProg mmpl 0 msvc) (mbase 0) {
      pre := fun (_ : Unit) _ => emp
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm ∧
         sf.readReg64 .x0 = s0.tpidrEl0 - 0xa4#64⌝
    } := by
  have _hw := hasWords_blk_relocFree (i := 0) (by decide)
    (ws := errnoLocation3Words) (by decide +kernel)
  wp_init x s0; wp_steps; wp_done

theorem placed_errnoLocation_perm_ok [MallocngMultiPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 0) (withCL mmpl {
      pre := fun (_ : Unit) _ => emp
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm ∧
         sf.readReg64 .x0 = s0.tpidrEl0 - 0xa4#64⌝
    }) :=
  subroutine_ok_block_to_block_plain (j := 0) (by decide) blk00_errno_perm hext hsvc

private theorem blk00_errno [MallocngMultiPlacement] :
    subroutine_ok (mallocngBlockProg mmpl 0 msvc) (mbase 0) {
      pre := fun (_ : Unit) _ => emp
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
         sf.readReg64 .x0 = s0.tpidrEl0 - 0xa4#64⌝
    } := by
  have _hw := hasWords_blk_relocFree (i := 0) (by decide)
    (ws := errnoLocation3Words) (by decide +kernel)
  wp_init x s0; wp_steps; wp_done

theorem placed_errnoLocation_ok [MallocngMultiPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 0) (withCL mmpl {
      pre := fun (_ : Unit) _ => emp
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧
         sf.readReg64 .x0 = s0.tpidrEl0 - 0xa4#64⌝
    }) :=
  subroutine_ok_block_to_block_plain (j := 0) (by decide) blk00_errno hext hsvc

private theorem blk15_vmWait_perm [MallocngMultiPlacement] :
    subroutine_ok (mallocngBlockProg mmpl 15 msvc) (mbase 15) {
      pre := fun (_ : Unit) _ => emp
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm⌝
    } := by
  have _hw := hasWords_blk_relocFree (i := 15) (by decide)
    (ws := vmWaitWords) (by decide +kernel)
  wp_init x s0; wp_steps; wp_done

theorem placed_vmWait_perm_ok [MallocngMultiPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 15) (withCL mmpl {
      pre := fun (_ : Unit) _ => emp
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm⌝
    }) :=
  subroutine_ok_block_to_block_plain (j := 15) (by decide) blk15_vmWait_perm hext hsvc

private theorem blk23_unlockNoop [MallocngMultiPlacement] (lk : BitVec 64) :
    subroutine_ok (mallocngBlockProg mmpl 23 msvc) (mbase 23) {
      pre := fun (_ : Unit) s0 => ⌜s0.readReg64 .x0 = lk⌝ ∗ (lk ↦₃₂ 0#32)
      post := fun _ s0 sf => ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk⌝ ∗ (lk ↦₃₂ 0#32)
    } := by
  have _hw := hasWords_blk_relocFree (i := 23) (by decide)
    (ws := unlockFnWords) (by decide +kernel)
  wp_init x s0; subst lk; wp_steps; wp_done

theorem placed_unlockNoop_ok [MallocngMultiPlacement] {P : Program} (lk : BitVec 64)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 23) (withCL mmpl {
      pre := fun (_ : Unit) s0 => ⌜s0.readReg64 .x0 = lk⌝ ∗ (lk ↦₃₂ 0#32)
      post := fun _ s0 sf => ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk⌝ ∗ (lk ↦₃₂ 0#32)
    }) :=
  subroutine_ok_block_to_block_plain (j := 23) (by decide) (blk23_unlockNoop lk) hext hsvc

private theorem blk22_lockNoop [MallocngMultiPlacement] (lk : BitVec 64) :
    subroutine_ok (mallocngBlockProg mmpl 22 msvc) (mbase 22) {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.readReg64 .x0 = lk⌝ ∗ ((maddrs.libc + 3#64) ↦₈ 0#8)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk⌝ ∗ ((maddrs.libc + 3#64) ↦₈ 0#8)
    } := by
  have ⟨_hw, _hrange⟩ := hasWords_blk_of_checkSegment (i := 22) (by decide)
    (ws := lockFnWords) (R := VerifiedLibraries.mallocng_blk22_lock.relocs) (by decide +kernel)
  wp_init x s0; subst lk; wp_steps; wp_done

theorem placed_lockNoop_ok [MallocngMultiPlacement] {P : Program} (lk : BitVec 64)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 22) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.readReg64 .x0 = lk⌝ ∗ ((maddrs.libc + 3#64) ↦₈ 0#8)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk⌝ ∗ ((maddrs.libc + 3#64) ↦₈ 0#8)
    }) :=
  subroutine_ok_block_to_block_plain (j := 22) (by decide) (blk22_lockNoop lk) hext hsvc

private theorem condHolds_hi_eq (p : PState) :
    ConditionHolds .HI p = (ConditionHolds .CS p && ConditionHolds .NE p) := by
  cases p; rfl

private theorem cmn_4096_hi (x : BitVec 64) :
    ConditionHolds .HI (addsPState64 x 4096#64) = true ↔ ¬ (x.toNat ≤ 2 ^ 64 - 4096) := by
  rw [condHolds_hi_eq, conditionHolds_cs_addsPState64, conditionHolds_ne_addsPState64]
  have _hx := x.isLt
  have hne : ((x + 4096#64 != 0#64) = true) ↔ x.toNat + 4096 ≠ 2 ^ 64 := by
    rw [bne_iff_ne]
    constructor
    · intro h heq; apply h; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · intro h heq; apply h
      have ht := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht; omega
  rw [Bool.and_eq_true, BitVec.ult_iff_toNat_lt, BitVec.toNat_add, BitVec.toNat_ofNat, hne]
  omega

abbrev PlacedSyscallRetGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 32

set_option maxHeartbeats 400000 in
private theorem blk01_syscallRet_perm [MallocngMultiPlacement] :
    subroutine_ok (mallocngBlockProg mmpl 1 msvc) (mbase 1) (withCL mmpl {
      pre := fun (g : PlacedSyscallRetGhost) s0 =>
        ⌜s0.tpidrEl0 = g.1 ∧ s0.readReg64 .x0 = g.2.1⌝ ∗
        ((s0.sp - 32#64) ↦₆₄ g.2.2.1) ∗ ((s0.sp - 24#64) ↦₆₄ g.2.2.2.1) ∗
        ((s0.sp - 16#64) ↦₆₄ g.2.2.2.2.1) ∗ ((s0.sp - 8#64) ↦₆₄ g.2.2.2.2.2.1) ∗
        ((g.1 - 0xa4#64) ↦₃₂ g.2.2.2.2.2.2)
      post := fun g s0 sf =>
        ∃∗ (w0 : BitVec 64), ∃∗ (w1 : BitVec 64), ∃∗ (w2 : BitVec 64), ∃∗ (w3 : BitVec 64),
          ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm ∧
           sf.readReg64 .x0 = (if g.2.1.toNat ≤ 2 ^ 64 - 4096 then g.2.1 else BitVec.allOnes 64)⌝ ∗
          ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗
          ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3) ∗
          ((g.1 - 0xa4#64) ↦₃₂
            (if g.2.1.toNat ≤ 2 ^ 64 - 4096 then g.2.2.2.2.2.2 else 0#32 - g.2.1.truncate 32))
    }) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have ⟨_hw, _hrange⟩ := hasWords_blk_of_checkSegment (i := 1) (by decide)
    (ws := syscallRetWords) (R := VerifiedLibraries.mallocng_blk01_syscall_ret.relocs) (by decide +kernel)
  have herr := placed_errnoLocation_perm_ok (P := mallocngBlockProg mmpl 1 msvc)
    (by intro pc; simp) rfl
  wp_init g s0
  subst m0
  rcases g with ⟨tp, r, a, b, c, d, ev⟩
  dsimp only at *
  wp_stp64_cl m1 hm1 hcl0 hcl1
  wp_step; wp_step
  wp_str64_cl m2 hm2 hcl1 hcl2
  wp_step; wp_step
  wp_if hcond
  · have hgt : ¬ (r.toNat ≤ 2 ^ 64 - 4096) := (cmn_4096_hi r).mp hcond
    simp only [Reg.x0, hgt, ↓reduceIte]
    wp_step
    wp_call herr
    simp only [MallocngProcPreserved] at *
    have hcl_herr : VerifiedLibraries.mallocngLib.CodeLoaded mmpl _ := ‹_›
    wp_step; wp_step; wp_step
    wp_str32_cl m3 hm3 hcl_herr hcl3
    wp_steps
    have hneg : 0#32 - r.truncate 32 = (-r).truncate 32 := by bv_bits
    have _hperm : m3.perm = s0.mem.perm := Eq.trans hm3 (Eq.trans ‹_› (Eq.trans hm2 hm1))
    simp only [hneg]
    wp_done
  · have hle : r.toNat ≤ 2 ^ 64 - 4096 :=
      Classical.byContradiction fun hn => hcond ((cmn_4096_hi r).mpr hn)
    simp only [Reg.x0, hle, ↓reduceIte]
    wp_steps
    have _hperm : m2.perm = s0.mem.perm := Eq.trans hm2 hm1
    wp_done

theorem placed_syscallRet_perm_ok [MallocngMultiPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 1) (withCL mmpl {
      pre := fun (g : PlacedSyscallRetGhost) s0 =>
        ⌜s0.tpidrEl0 = g.1 ∧ s0.readReg64 .x0 = g.2.1⌝ ∗
        ((s0.sp - 32#64) ↦₆₄ g.2.2.1) ∗ ((s0.sp - 24#64) ↦₆₄ g.2.2.2.1) ∗
        ((s0.sp - 16#64) ↦₆₄ g.2.2.2.2.1) ∗ ((s0.sp - 8#64) ↦₆₄ g.2.2.2.2.2.1) ∗
        ((g.1 - 0xa4#64) ↦₃₂ g.2.2.2.2.2.2)
      post := fun g s0 sf =>
        ∃∗ (w0 : BitVec 64), ∃∗ (w1 : BitVec 64), ∃∗ (w2 : BitVec 64), ∃∗ (w3 : BitVec 64),
          ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm ∧
           sf.readReg64 .x0 = (if g.2.1.toNat ≤ 2 ^ 64 - 4096 then g.2.1 else BitVec.allOnes 64)⌝ ∗
          ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗
          ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3) ∗
          ((g.1 - 0xa4#64) ↦₃₂
            (if g.2.1.toNat ≤ 2 ^ 64 - 4096 then g.2.2.2.2.2.2 else 0#32 - g.2.1.truncate 32))
    }) :=
  subroutine_ok_block_to_block (j := 1) (by decide) blk01_syscallRet_perm hext hsvc

/-! ## String Leaves -/

private theorem disjoint_pts_ro {m : Memory} {dst src : BitVec 64}
    {dstBs srcBs : List (BitVec 8)} {R : SepProp}
    (hlen : srcBs.length ≤ 2 ^ 64) (heq : dstBs.length = srcBs.length)
    (h : m ⊨ (src ↦ᵣ srcBs) ∗ ((dst ↦ₛ dstBs) ∗ R)) :
    DisjointRegions dst srcBs.length src srcBs.length := by
  by_cases hpos : 0 < srcBs.length
  · have hmem : m ⊨ (src ↦ᵣ srcBs) ∗ (memRegion dst srcBs.length ∗ R) := by
      have hent := (IsBlock.pointsToBytes dst dstBs).entails_memRegion
      rw [heq] at hent
      exact Satisfies.mono (sepConj_mono_right (sepConj_mono_left hent)) h
    have hdisj : ∀ a, ¬(InRegion dst srcBs.length a ∧ InRegion src srcBs.length a) := by
      intro a ⟨hin1, hin2⟩
      exact not_satisfies_ownsRO_ownsRW
        (ownsRO_pointsToBytesRO_at hlen hin2)
        (ownsRW_sepConj_left (ownsRW_memRegion dst srcBs.length a hin1))
        hmem
    constructor
    · apply Classical.byContradiction; intro hlt
      exact hdisj src ⟨by simp only [InRegion]; omega,
        by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
    · apply Classical.byContradiction; intro hlt
      exact hdisj dst ⟨by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega,
        by simp only [InRegion]; omega⟩
  · have hzero : srcBs.length = 0 := by omega
    rw [hzero]; exact ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem placed_memcpy_ok [MallocngMultiPlacement] {P : Program}
    (dst src : BitVec 64) (dstBs srcBs : List (BitVec 8)) (n : Nat)
    (hdstLen : dstBs.length = n) (hsrcLen : srcBs.length = n)
    (_hdstFit : dst.toNat + n ≤ 2 ^ 64) (_hsrcFit : src.toNat + n ≤ 2 ^ 64)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 20) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = n⌝ ∗
        (dst ↦ₛ dstBs) ∗ (src ↦ₛ srcBs)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.readReg64 .x0 = dst⌝ ∗
        (dst ↦ₛ srcBs) ∗ (src ↦ₛ srcBs)
    }) := by
  refine subroutine_ok_block_to_block_plain (j := 20) (by decide) ?_ hext hsvc
  have hc : (mallocngBlockProg mmpl 20 msvc).hasCode (mbase 20) memcpySymWords :=
    hasWords_blk_relocFree (i := 20) (by decide) (ws := memcpySymWords) (by decide +kernel)
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre _hsp
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  have hro : s0.mem ⊨ (src ↦ᵣ srcBs) ∗ ((dst ↦ₛ dstBs) ∗ R) := by
    have h' : s0.mem ⊨ (src ↦ₛ srcBs) ∗ ((dst ↦ₛ dstBs) ∗ R) := by
      rw [← sepConj_assoc, sepConj_comm (src ↦ₛ srcBs), sepConj_assoc]; exact hmem
    exact Satisfies.pointsToBytes_to_ro h'
  have ⟨hd1, hd2⟩ := disjoint_pts_ro (by omega) (hdstLen.trans hsrcLen.symm) hro
  have hn63 : (s0.readReg64 .x2).toNat ≤ 2 ^ 63 := by rw [hx2, ← hsrcLen]; bv_omega
  refine ⟨(dst ↦ₛ dstBs) ∗ memcpySrc false src srcBs, by simpa [memcpySrc, sepConj_assoc] using hmem, ?_⟩
  refine SepWP.mono (memcpy_sepwp false (mallocngBlockProg mmpl 20 msvc) (mbase 20) hc s0
    dst src (s0.readReg64 .x2) dstBs srcBs hpc hrun hx0 hx1 rfl
    (by omega) (by omega) hn63) ?_
  intro sf _ _ _ ⟨⟨hx0f, hspf, hcsf, hfs, htr, htpidr, hbrks, horc, hsym, hsig, hbrk⟩, hent⟩
  refine ⟨fun hm => ?_, hspf, hcsf⟩
  have hm' := Satisfies.mono (sepConj_mono_left hent) hm
  simp only [memcpySrc, Bool.cond_false, sepConj_assoc, satisfies_pure_sepConj] at hm' ⊢
  exact ⟨⟨⟨hfs, htr, htpidr, hbrks, horc, hsym, hsig⟩, hbrk, hx0f⟩, hm'⟩

private theorem readBytes_of_prefixFilled {m₀ mf : Memory} {dst c : BitVec 64} {n : Nat}
    (hfc : PrefixFilled m₀ mf dst c n n) :
    mf.readBytes dst n = List.replicate n (c.truncate 8) := by
  have go : ∀ k off, off + k ≤ n →
      mf.readBytes (dst + BitVec.ofNat 64 off) k = List.replicate k (c.truncate 8) := by
    intro k
    induction k with
    | zero => intro _ _; rfl
    | succ k ih =>
      intro off hk
      simp only [Memory.readBytes, List.replicate_succ]
      have hhead : mf.read8 (dst + BitVec.ofNat 64 off) = c.truncate 8 := hfc.2 off (by omega)
      have h1 : dst + BitVec.ofNat 64 off + 1#64 = dst + BitVec.ofNat 64 (off + 1) := by bv_omega
      rw [hhead, h1, ih (off + 1) (by omega)]
  simpa using go n 0 (by omega)

private theorem codeLoaded_perm_rx_words {prog : Program} {m : Memory} {a : BitVec 64}
    {words : List (BitVec 32)} (hL : prog.CodeLoaded m) (hw : prog.hasWords a words)
    {j : Nat} (hj : j < 4 * words.length) :
    m.perm (a + BitVec.ofNat 64 j) = some Perm.rx := by
  have hget := Program.code_getElem?_of_hasWordsOff hw j hj
  have hflat : j < (words.flatMap Program.wordToBytesLE).length := by
    rw [Program.length_flatMap_wordToBytesLE]; exact hj
  rw [List.getElem?_eq_getElem hflat] at hget
  have hlt : (a - prog.base).toNat + j < prog.code.length :=
    Classical.byContradiction fun hge => by
      rw [List.getElem?_eq_none (by omega)] at hget; cases hget
  have hp := hL.perm_eq ((a - prog.base).toNat + j) hlt
  have haddr : prog.base + BitVec.ofNat 64 ((a - prog.base).toNat + j) = a + BitVec.ofNat 64 j := by
    bv_omega
  rwa [haddr] at hp

private theorem rw_len_add_words_le {prog : Program} {m : Memory} {a dst : BitVec 64}
    {words : List (BitVec 32)} {n : Nat}
    (hL : prog.CodeLoaded m) (hw : prog.hasWords a words) (hrw : m.RW dst n)
    (hn : n ≤ 2 ^ 64) :
    n + 4 * words.length ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · subst hn0; have := hw.1; omega
  · by_cases hw0 : words.length = 0
    · simp [hw0, hn]
    · have h1 : n ≤ (a - dst).toNat :=
        Classical.byContradiction fun hlt => by
          have hrw_a : m.perm a = some Perm.rw :=
            (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a (by unfold InRegion; omega))).1
          have hp_rx : m.perm (a + 0#64) = some Perm.rx :=
            codeLoaded_perm_rx_words hL hw (by omega)
          simp only [BitVec.add_zero, hrw_a] at hp_rx; cases hp_rx
      have h2 : 4 * words.length ≤ (dst - a).toNat :=
        Classical.byContradiction fun hlt => by
          have hp_rx : m.perm (a + BitVec.ofNat 64 (dst - a).toNat) = some Perm.rx :=
            codeLoaded_perm_rx_words hL hw (by omega)
          have haddr : a + BitVec.ofNat 64 (dst - a).toNat = dst := by bv_omega
          have hrw_d : m.perm dst = some Perm.rw :=
            (Memory.permNoLazy_eq_some_rw_iff.mp (hrw dst (by unfold InRegion; simp; omega))).1
          rw [haddr, hrw_d] at hp_rx; cases hp_rx
      bv_omega

theorem placed_memsetZero_ok [MallocngMultiPlacement] {P : Program}
    (dst : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (hbsLen : bs.length = n) (_hdstFit : dst.toNat + n ≤ 2 ^ 64)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 21) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.readReg64 .x0 = dst ∧ s0.readReg32 .x1 = 0#32 ∧ (s0.readReg64 .x2).toNat = n⌝ ∗
        (dst ↦ₛ bs)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.readReg64 .x0 = dst⌝ ∗
        (dst ↦ₛ List.replicate n 0#8)
    }) := by
  refine subroutine_ok_block_to_block_plain (j := 21) (by decide) ?_ hext hsvc
  have hw := hasWords_blk_relocFree (i := 21) (by decide) (ws := memsetWordsSym) (by decide +kernel)
  have hc : (mallocngBlockProg mmpl 21 msvc).hasCode (mbase 21) memsetWordsSym := hw
  apply subroutine_ok_outcome_intro
  intro _ R s0 hpc hrun hpre _hsp
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1_32, hx2⟩, hmem⟩ := hpre
  have htrunc : (s0.readReg64 .x1).truncate 8 = 0#8 := by
    have h32 : (s0.readReg64 .x1).truncate 32 = 0#32 := hx1_32
    revert h32; generalize s0.readReg64 .x1 = v; intro h32; bv_bits
  refine reaches_outcome_of_reaches_pc (oom := fun _ => False) ?_
  by_cases hn96 : n ≤ 96
  · refine reaches_pc_mono (SepWP.to_reaches_pc
      (memset_sepWP_le96 (mallocngBlockProg mmpl 21 msvc) (mbase 21) hc s0
        dst (s0.readReg64 .x1) (s0.readReg64 .x2) bs hpc hrun hx0 rfl rfl
        (by omega) (by omega)) hmem) ?_
      (fun _ _ h => not_satisfies_false_sepConj h)
    rintro sf _ _ ⟨P_f, hmf, ⟨hx0_f, hsp_f, hcs_f, hfs, htr, htpidr, hbrks, horc, hsym, hsig, hbrk⟩, hent⟩
    have hpost_mem : sf.mem ⊨ (dst ↦ₛ List.replicate n 0#8) ∗ R := by
      have hm' := Satisfies.mono (sepConj_mono_left hent) hmf
      rwa [htrunc, hx2] at hm'
    refine ⟨?_, hsp_f, hcs_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨⟨hfs, htr, htpidr, hbrks, horc, hsym, hsig⟩, hbrk, hx0_f⟩, hpost_mem⟩
  · have hreg : s0.mem ⊨ memRegion dst n ∗ R := by
      have hent := (IsBlock.pointsToBytes dst bs).entails_memRegion
      rw [hbsLen] at hent
      exact Satisfies.mono (sepConj_mono_left hent) hmem
    have hrw : s0.mem.RW dst (s0.readReg64 .x2).toNat := by
      rw [hx2]; exact (IsBlock.memRegion dst n).rw hreg
    intro hL
    have hn_code := rw_len_add_words_le hL hw hrw (by rw [hx2]; omega)
    have hn_le : (s0.readReg64 .x2).toNat + 260 ≤ 2 ^ 64 := by simpa [memsetWordsSym] using hn_code
    refine memset_sym_large (mallocngBlockProg mmpl 21 msvc) (mbase 21) hc s0 _
      dst (s0.readReg64 .x1) (s0.readReg64 .x2) hpc hrun hx0 rfl rfl hrw (by omega) hn_le ?_ hL
    rintro sf _ _ hx0_f ⟨hcc, _hlr, hfs, htr, htpidr, hbrks, horc, hsym, hsig, hbrk⟩ hfc
    let zbs := List.replicate n 0#8
    have hzlen : zbs.length = n := List.length_replicate
    have hdst_bytes : sf.mem.readBytes dst zbs.length = zbs := by
      rw [hzlen]
      have hrb := readBytes_of_prefixFilled hfc; rwa [htrunc, hx2] at hrb
    have hpost_mem : sf.mem ⊨ (dst ↦ₛ zbs) ∗ R :=
      (IsBlock.memRegion dst n).update (IsBlock.pointsToBytes dst zbs)
        (Nat.le_of_eq hzlen) hreg (by simpa [hx2] using hfc.1) ⟨by omega, hdst_bytes⟩
    refine ⟨?_, hcc⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨⟨hfs, htr, htpidr, hbrks, horc, hsym, hsig⟩, hbrk, hx0_f⟩, hpost_mem⟩

end VerifiedLibraries.Mallocng.Proofs
