/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.Wave1.TimeAdd
public import ProofLib.Placed.OpcodeExclusion
public import ProofLib.Hoare.MultiCodeROHook
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget -- proof-setup: allow-public-import
import ProofLib.MallocngBridge
import LibsignalBinary.Proofs.HookDischarge.RustStd.TimeAdd

/-!
# `<SystemTime as Add<Duration>>::add` `VmPreserved` Hook Discharge (`LibsignalBinary.Proofs.HookDischarge.RustStd.TimeAddVm`)

Proves that the real `rustc 1.98.1` `aarch64-unknown-linux-musl` `libstd` code (`timeMultiLib`
block `2`, `timeTree02`) satisfies `VmPreserved` and meets all three consumer contracts:
1. `CryptoVerification.LibsignalPublicApi.timeAddSpec` (`Specifications/LibsignalPublicApi.lean:294`),
2. `LibsignalBinary.Heap.SpecBudget.timeAddBudgetSpec` (`Heap/SpecBudget.lean:526`), and
3. `LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins.timeAddBudgetSpec`
   (`Proofs/PublicApi/MessageEncrypt/Seg/SegFromPlacedBudget.lean:127`, `rfl`-equal to (2)).

Also provides reusable `MultiPlacedLib` `withVmPreserved` lifting combinators shared with `FromUtf8Vm`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.TimeAddVm

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement MultiPlacedLib PlacedLib CodeBlock svc0Pat msrTpidrEl0Pat lookupBlockSym)
open VerifiedLibraries.RustStd (timeMultiLib timeAddSym rustTimeExpectFailedSym timeExterns)
open LibsignalBinary.Heap (VmPreserved FdsHiFrame)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt withRoData SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.RustStd.TimeAdd (timeAdd_placed_timeAddSpec_ok
  timeAdd_timeAddSpec_subroutineOk_of_panic timeAdd_timeAddSpec_subroutineOk)

/-! ## 1. Shared `MultiPlacedLib` `withVmPreserved` Lifting Infrastructure -/

/-- Combine `ProofLib.NonSyscallPreserved s0 sf` and `sf.tpidrEl0 = s0.tpidrEl0` into
    `VmPreserved s0 sf`. -/
theorem vmPreserved_of_nonSyscall_tpidr {s0 sf : State}
    (hnsp : ProofLib.NonSyscallPreserved s0 sf) (htp : sf.tpidrEl0 = s0.tpidrEl0) :
    VmPreserved s0 sf :=
  ⟨⟨hnsp.2.2.2.1, hnsp.2.2.1, htp⟩, hnsp.2.2.2.2.1,
    fun a => congrFun hnsp.2.1 a, FdsHiFrame.of_fs_eq hnsp.2.2.2.2.2.2⟩

/-- `withRoData` and `withVmPreserved` commute definitionally (`rfl`). -/
theorem withRoData_withVmPreserved {α : Type} (addr : BitVec 64) (bytes : List (BitVec 8))
    (spec : Spec α) :
    withRoData addr bytes (withVmPreserved spec) =
      withVmPreserved (withRoData addr bytes spec) := rfl

/-- `keepsFs` and `withVmPreserved` commute up to `SpecSimulates`. -/
theorem keepsFs_withVmPreserved_simulates {α : Type} (spec : Spec α) :
    SpecSimulates (withVmPreserved (keepsFs spec)) (keepsFs (withVmPreserved spec)) := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hout
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, keepsFs] at hpost ⊢
    rw [sepConj_left_comm ⌜VmPreserved s0 sf⌝ ⌜sf.fs = s0.fs⌝] at hpost
    exact hpost
  · exact Or.inr hout

/-- Stripping execute permissions outside `keep` preserves `RoDataAt` (`Perm.ro` has `.x = false`). -/
theorem roDataAt_stripExecOutside (keep : BitVec 64 → Bool) {m : Memory} {addr : BitVec 64}
    {bytes : List (BitVec 8)} (h : RoDataAt m addr bytes) :
    RoDataAt (ProofLib.stripExecOutside keep m) addr bytes := by
  obtain ⟨hro, hread⟩ := h
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨hp, hlf⟩ := hro a ha
    rw [ProofLib.strip_perm, ProofLib.strip_isLazyFree, hp]
    exact ⟨by cases keep a <;> rfl, hlf⟩
  · have hr : ∀ (a : BitVec 64) (n : Nat),
        (ProofLib.stripExecOutside keep m).readBytes a n = m.readBytes a n := by
      intro a n
      induction n generalizing a with
      | zero => rfl
      | succ n ih =>
        simp only [Memory.readBytes, ProofLib.strip_read8, ih]
    rw [hr]
    exact hread

/-- Keep predicate covering all blocks of `lib` under `mpl`. -/
@[expose] def multiLibKeep (lib : MultiPlacedLib) (mpl : MultiPlacement) (a : BitVec 64) : Bool :=
  (List.range lib.blocks.length).any fun k => ProofLib.progKeep (lib.blockProgram mpl k) a

private theorem strip_codeLoaded_multi {lib : MultiPlacedLib} {mpl : MultiPlacement} {m : Memory}
    (hcl : lib.CodeLoaded mpl m) :
    lib.CodeLoaded mpl (ProofLib.stripExecOutside (multiLibKeep lib mpl) m) := by
  intro k hk
  have hL := hcl k hk
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub :
      (lib.blockProgram mpl k).base + BitVec.ofNat 64 i - (lib.blockProgram mpl k).base =
        BitVec.ofNat 64 i := by bv_omega
  have hpk :
      ProofLib.progKeep (lib.blockProgram mpl k)
        ((lib.blockProgram mpl k).base + BitVec.ofNat 64 i) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  have hkeep :
      multiLibKeep lib mpl ((lib.blockProgram mpl k).base + BitVec.ofNat 64 i) = true :=
    List.any_eq_true.mpr ⟨k, List.mem_range.mpr hk, hpk⟩
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private def OutcomeStatus (st : ExecStatus) : Prop :=
  st = .Running ∨ st = .Panicked ∨ (∃ c, st = .Exited c) ∨ st = .OutOfMemory

private theorem step_not_halted_or_exc {Q : Program} {s2 sf : State}
    (hrest : Steps Q s2 sf) (hout : OutcomeStatus sf.status)
    (hbad : s2.status = .Halted ∨ ∃ msg, s2.status = .Exception msg) : False := by
  cases hrest with
  | refl =>
    rcases hbad with hh | ⟨_, hh⟩ <;> rcases hout with hr | hp | ⟨_, he⟩ | ho <;>
      simp_all
  | step hs _ =>
    have hrun := hs.status_running
    rcases hbad with hh | ⟨_, hh⟩ <;> simp_all

/-- Lift any `Steps` trace on `Q := lib.blockProgram mpl i X` across ALL blocks of `lib`
    from `stripS (multiLibKeep lib mpl) s0` to `Steps Q s0 sf`, establishing `VmPreserved s0 sf`,
    when every block of `lib` satisfies `patchSafe svc0Pat` and `patchSafe msrTpidrEl0Pat` and
    every active extern of `Q` is `Rust.panicked`. -/
private theorem steps_lift_multiBlocks_vm {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hpl : lib.Placeable mpl) {i : Nat} {X : String → Option (State → State)}
    (hall_svc : ∀ k (hk : k < lib.blocks.length), lib.blocks[k].patchSafe svc0Pat = true)
    (hall_msr : ∀ k (hk : k < lib.blocks.length), lib.blocks[k].patchSafe msrTpidrEl0Pat = true)
    (hext_pan : ∀ pc f, (lib.blockProgram mpl i X).externAt? pc = some f → f = Rust.panicked)
    {s1' sf' : State} (hsteps : Steps (lib.blockProgram mpl i X) s1' sf')
    (hout : OutcomeStatus sf'.status) :
    ∀ (s1 : State), s1' = ProofLib.stripS (multiLibKeep lib mpl) s1 →
      lib.CodeLoaded mpl s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (multiLibKeep lib mpl) sf ∧
        Steps (lib.blockProgram mpl i X) s1 sf ∧
        ProofLib.NonSyscallPreserved s1 sf ∧ sf.tpidrEl0 = s1.tpidrEl0 := by
  let Q := lib.blockProgram mpl i X
  let keep := multiLibKeep lib mpl
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1, rfl⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hcl1
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact False.elim (step_not_halted_or_exc hrest hout (Or.inl (by cases s1; rfl)))
    | extern_fault _ _ _ =>
      exact False.elim (step_not_halted_or_exc hrest hout (Or.inr ⟨_, by cases s1; rfl⟩))
    | @extern f hr1' he' _ _ =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hpc_eq : (ProofLib.stripS keep s1).pc = s1.pc := by cases s1; rfl
      rw [hpc_eq] at he'
      have hf_eq := hext_pan s1.pc f he'
      subst hf_eq
      have hstep_Q : Step Q s1 (Rust.panicked s1) :=
        Step.extern hr1 he' (Memory.KeepsFrozen.refl s1.mem) rfl
      have hcomm : Rust.panicked (ProofLib.stripS keep s1) =
          ProofLib.stripS keep (Rust.panicked s1) := by
        cases s1; rfl
      obtain ⟨sf, hsf_eq, hsteps_Q, hnsp_rest, htp_rest⟩ :=
        ih hout (Rust.panicked s1) hcomm hcl1
      have hnsp1 : ProofLib.NonSyscallPreserved s1 (Rust.panicked s1) := by
        cases s1; exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, fun _ h => h⟩, rfl⟩
      have htp1 : (Rust.panicked s1).tpidrEl0 = s1.tpidrEl0 := by cases s1; rfl
      exact ⟨sf, hsf_eq, .step hstep_Q hsteps_Q, hnsp1.trans hnsp_rest, htp_rest.trans htp1⟩
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hpc_eq : (ProofLib.stripS keep s1).pc = s1.pc := by cases s1; rfl
      have hmem_eq : (ProofLib.stripS keep s1).mem = ProofLib.stripExecOutside keep s1.mem := by
        cases s1; rfl
      change Q.fetchMem (ProofLib.stripS keep s1).mem (ProofLib.stripS keep s1).pc = some inst at hfe'
      rw [hpc_eq, hmem_eq] at hfe'
      have ⟨hal_pc, heQ, hce, hdec, hk0⟩ :
          s1.pc.toNat % 4 = 0 ∧ Q.externAt? s1.pc = none ∧
          s1.mem.canExec s1.pc 4 = true ∧ decode (s1.mem.read32 s1.pc) = some inst ∧
          keep s1.pc = true := by
        unfold Program.fetchMem at hfe'
        cases heQ : Q.externAt? s1.pc with
        | some _ => rw [heQ] at hfe'; nomatch hfe'
        | none =>
          rw [heQ] at hfe'
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
          by_cases hal_pc : s1.pc.toNat % 4 = 0
          · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
            split at hfe'
            · contradiction
            · rename_i hce'
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
              have hk0 : keep s1.pc = true := by
                have hce0 := hce'
                unfold Memory.canExec at hce0
                rw [Memory.allPerm_iff] at hce0
                simpa only [BitVec.add_zero] using
                  (ProofLib.strip_perm_x_imp (hce0 0 (by omega))).2
              have hce : s1.mem.canExec s1.pc 4 = true := by
                unfold Memory.canExec at hce' ⊢
                rw [Memory.allPerm_iff] at hce' ⊢
                intro k hk
                have hxk := hce' k hk
                rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
              have hr32 : (ProofLib.stripExecOutside keep s1.mem).read32 s1.pc =
                  s1.mem.read32 s1.pc := by
                simp [Memory.read32, ProofLib.strip_read8]
              rw [hr32] at hfe'
              exact ⟨hal_pc, rfl, hce, hfe', hk0⟩
          · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
            contradiction
      have hfe_Q : Q.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem
        simp [heQ, hal_pc, hce, hdec]
      obtain ⟨k, hk_mem, hpk⟩ := List.any_eq_true.mp hk0
      have hk : k < lib.blocks.length := List.mem_range.mp hk_mem
      let Rk := lib.blockProgram mpl k
      have hLk : Rk.CodeLoaded s1.mem := hcl1 k hk
      have hfe_Rk : Rk.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem
        rw [MultiPlacedLib.externAt?_blockProgram_none]
        simp [hal_pc, hce, hdec]
      have hlen_mod : Rk.code.length % 4 = 0 := by
        have hc : Rk.code = (lib.blockLib k).text.patched (lib.blockPlacement mpl k) := rfl
        rw [hc, lib.blockLib_text hk,
          CodeBlock.length_patched_of_aligned _ (hpl.blocks_ok k hk).len_aligned]
        exact (hpl.blocks_ok k hk).len_aligned
      have hin0 : (s1.pc - Rk.base).toNat < Rk.code.length := of_decide_eq_true hpk
      have hin4 : (s1.pc - Rk.base).toNat + 4 ≤ Rk.code.length := by
        have hal_b := hLk.aligned
        have hnw_b := hLk.no_wrap
        bv_omega
      have hp_svc : Rk.allInstrs (fun ins => !ins.isSvc0) = true := by
        unfold Rk MultiPlacedLib.blockProgram
        exact PlacedLib.program_noSvc0_of_patchSafe (by rw [lib.blockLib_text hk]; exact hall_svc k hk) _
      have hp_msr : Rk.allInstrs (fun ins => !ins.isMsrTpidrEl0) = true := by
        unfold Rk MultiPlacedLib.blockProgram
        exact PlacedLib.program_noMsrTpidrEl0_of_patchSafe
          (by rw [lib.blockLib_text hk]; exact hall_msr k hk) _
      have hHB : Obj.HoldsBytes s1.mem Rk.base Rk.code (fun _ => Perm.rx) :=
        fun idx hidx => ⟨hLk.byte_eq idx hidx, hLk.perm_eq idx hidx, hLk.isLazyFree_eq idx hidx⟩
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs_holdsBytes_in_code hp_svc hLk.aligned hLk.no_wrap
          hHB hin4 hfe_Rk
      have hnmsr : inst.isMsrTpidrEl0 = false := by
        simpa using Program.fetchMem_of_allInstrs_holdsBytes_in_code hp_msr hLk.aligned hLk.no_wrap
          hHB hin4 hfe_Rk
      have hev_Q : Q.evalInst inst (ProofLib.stripS keep s1) =
          ProofLib.stripS keep (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_Q : Step Q s1 (execInst inst s1) := by
        have := Step.exec (prog := Q) hr1 hfe_Q
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      have hcl2 : lib.CodeLoaded mpl (execInst inst s1).mem :=
        fun j hj => hstep_Q.codeLoaded (hcl1 j hj)
      obtain ⟨sf, hsf_eq, hsteps_Q, hnsp_rest, htp_rest⟩ :=
        ih hout (execInst inst s1) hev_Q hcl2
      have hnsp1 := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1
      have htp1 := execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1
      exact ⟨sf, hsf_eq, .step hstep_Q hsteps_Q, hnsp1.trans hnsp_rest, htp_rest.trans htp1⟩

private def otherBlockAddrs (lib : MultiPlacedLib) (mpl : MultiPlacement) (i : Nat) :
    List (BitVec 64) :=
  (List.range lib.blocks.length).flatMap fun k =>
    if k == i then []
    else (List.range (lib.blockProgram mpl k).code.length).map fun off =>
      mpl.base k + BitVec.ofNat 64 off

private def haltFn (s : State) : State := { s with status := .Halted }

private def guardBlockProg (lib : MultiPlacedLib) (mpl : MultiPlacement) (i : Nat)
    (panAddr? : Option (BitVec 64)) : Program :=
  let base := (lib.blockProgram mpl i).base
  let code := (lib.blockProgram mpl i).code
  let panStubs : List (String × Nat) :=
    match panAddr? with
    | some pa => [("__panic", (pa - base).toNat)]
    | none => []
  let haltStubs : List (String × Nat) :=
    (otherBlockAddrs lib mpl i).map fun a => ("__halt", (a - base).toNat)
  { base := base
    code := code
    symbols := []
    stubs := panStubs ++ haltStubs
    externs := fun name =>
      if name == "__panic" then some Rust.panicked
      else if name == "__halt" then some haltFn
      else none
    overrides := fun _ => none
    svc := Syscall.standard }

private theorem bv_eq_of_sub_toNat_eq {a b base : BitVec 64}
    (h : (a - base).toNat = (b - base).toNat) : a = b := by
  have hsub : a - base = b - base := BitVec.eq_of_toNat_eq h
  have := congrArg (· + base) hsub
  simpa [BitVec.sub_add_cancel] using this

private theorem findSome_guardStubs_isSome {stubs : List (String × Nat)} {ext : String → Option (State → State)}
    {name : String} {off : Nat} {f : State → State}
    (hmem : (name, off) ∈ stubs) (hext : ext name = some f) :
    (stubs.findSome? fun (n, o) => if o == off then ext n else none).isSome = true := by
  induction stubs with
  | nil => nomatch hmem
  | cons hd tl ih =>
    rcases List.mem_cons.mp hmem with rfl | htl
    · simp [hext]
    · simp only [List.findSome?_cons]
      cases h : (if hd.2 == off then ext hd.1 else none) with
      | some _ => rfl
      | none => exact ih htl

private theorem guardBlockProg_externAt_panic (lib : MultiPlacedLib) (mpl : MultiPlacement)
    (i : Nat) (pa : BitVec 64) :
    (guardBlockProg lib mpl i (some pa)).externAt? pa = some Rust.panicked := by
  unfold guardBlockProg Program.externAt? Program.hookAtOff?
  simp

private theorem guardBlockProg_externAt_block_none {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hpl : lib.Placeable mpl) {i : Nat} (hi : i < lib.blocks.length)
    {panAddr? : Option (BitVec 64)} {off : Nat}
    (hoff : off < lib.blocks[i].code.length)
    (hne_pan : ∀ pa, panAddr? = some pa → mpl.base i + BitVec.ofNat 64 off ≠ pa) :
    (guardBlockProg lib mpl i panAddr?).externAt? (mpl.base i + BitVec.ofNat 64 off) = none := by
  let pc := mpl.base i + BitVec.ofNat 64 off
  let base := (lib.blockProgram mpl i).base
  have hbase_eq : base = mpl.base i := rfl
  unfold guardBlockProg Program.externAt? Program.hookAtOff?
  dsimp only
  simp only [List.findSome?_nil, Option.or_none, List.findSome?_eq_none_iff]
  intro ⟨n, o⟩ hmem
  rw [List.mem_append] at hmem
  rcases hmem with hpan | hhalt
  · cases hpa : panAddr? with
    | none => simp [hpa] at hpan
    | some pa =>
      simp only [hpa, List.mem_singleton, Prod.mk.injEq] at hpan
      obtain ⟨rfl, rfl⟩ := hpan
      split
      · rename_i hbeq
        exact False.elim (hne_pan pa hpa (bv_eq_of_sub_toNat_eq (beq_iff_eq.mp hbeq).symm))
      · rfl
  · simp only [List.mem_map, Prod.mk.injEq] at hhalt
    obtain ⟨a, ha_mem, rfl, rfl⟩ := hhalt
    unfold otherBlockAddrs at ha_mem
    rw [List.mem_flatMap] at ha_mem
    obtain ⟨k, hk_range, ha_k⟩ := ha_mem
    have hk : k < lib.blocks.length := List.mem_range.mp hk_range
    by_cases hki : k = i
    · subst hki; simp at ha_k
    · have hkbeq : (k == i) = false := beq_eq_false_iff_ne.mpr hki
      rw [hkbeq] at ha_k
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_map] at ha_k
      obtain ⟨off', hoff'_range, rfl⟩ := ha_k
      have hoff' : off' < (lib.blockProgram mpl k).code.length := List.mem_range.mp hoff'_range
      have hlen_k : (lib.blockProgram mpl k).code.length = lib.blocks[k].code.length := by
        have hc : (lib.blockProgram mpl k).code =
            (lib.blockLib k).text.patched (lib.blockPlacement mpl k) := rfl
        rw [hc, lib.blockLib_text hk,
          CodeBlock.length_patched_of_aligned _ (hpl.blocks_ok k hk).len_aligned]
      rw [hlen_k] at hoff'
      have hnwi : (mpl.base i).toNat + lib.blocks[i].code.length ≤ 2 ^ 64 :=
        (hpl.blocks_ok i hi).no_wrap
      have hnwk : (mpl.base k).toNat + lib.blocks[k].code.length ≤ 2 ^ 64 :=
        (hpl.blocks_ok k hk).no_wrap
      have hpc_nat : pc.toNat = (mpl.base i).toNat + off := by
        dsimp only [pc]
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
      have ha_nat : (mpl.base k + BitVec.ofNat 64 off').toNat = (mpl.base k).toNat + off' := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
      have ha_ne_pc : mpl.base k + BitVec.ofNat 64 off' ≠ pc := by
        intro heq
        have hnat := congrArg BitVec.toNat heq
        rw [ha_nat, hpc_nat] at hnat
        rcases Nat.lt_trichotomy i k with hik | rfl | hki'
        · rcases hpl.blocks_disjoint i k hi hk hik with hd | hd <;> omega
        · exact hki rfl
        · rcases hpl.blocks_disjoint k i hk hi hki' with hd | hd <;> omega
      split
      · rename_i hbeq
        exact False.elim (ha_ne_pc (bv_eq_of_sub_toNat_eq (beq_iff_eq.mp hbeq)))
      · rfl

private theorem guardBlockProg_in_block_of_externAt_none {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {i : Nat} {panAddr? : Option (BitVec 64)} {pc : BitVec 64}
    (hext : (guardBlockProg lib mpl i panAddr?).externAt? pc = none)
    (hkeep : multiLibKeep lib mpl pc = true) :
    (pc - mpl.base i).toNat < (lib.blockProgram mpl i).code.length := by
  obtain ⟨k, hk_mem, hpk⟩ := List.any_eq_true.mp hkeep
  have hk : k < lib.blocks.length := List.mem_range.mp hk_mem
  by_cases hki : k = i
  · subst hki
    exact of_decide_eq_true hpk
  · exfalso
    have hoff' : (pc - mpl.base k).toNat < (lib.blockProgram mpl k).code.length :=
      of_decide_eq_true hpk
    have hpc_eq : mpl.base k + BitVec.ofNat 64 (pc - mpl.base k).toNat = pc := by
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      bv_lin
    have ha_mem : pc ∈ otherBlockAddrs lib mpl i := by
      unfold otherBlockAddrs
      rw [List.mem_flatMap]
      refine ⟨k, List.mem_range.mpr hk, ?_⟩
      have hkbeq : (k == i) = false := beq_eq_false_iff_ne.mpr hki
      rw [hkbeq]
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_map]
      exact ⟨(pc - mpl.base k).toNat, List.mem_range.mpr hoff', hpc_eq⟩
    let base := (lib.blockProgram mpl i).base
    have hstub_mem :
        ("__halt", (pc - base).toNat) ∈ (guardBlockProg lib mpl i panAddr?).stubs := by
      unfold guardBlockProg
      dsimp only
      exact List.mem_append_right _ (List.mem_map.mpr ⟨pc, ha_mem, rfl⟩)
    have hisSome := findSome_guardStubs_isSome
      (ext := (guardBlockProg lib mpl i panAddr?).externs) hstub_mem (f := haltFn) rfl
    unfold Program.externAt? Program.hookAtOff? at hext
    rw [Option.or_eq_none_iff] at hext
    have hext1 :
        ((guardBlockProg lib mpl i panAddr?).stubs.findSome? fun (n, o) =>
          if o == (pc - base).toNat then (guardBlockProg lib mpl i panAddr?).externs n
          else none) = none := hext.1
    rw [hext1] at hisSome
    nomatch hisSome

private theorem guardBlockProg_externAt_some {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {i : Nat} {panAddr? : Option (BitVec 64)} {pc : BitVec 64} {f : State → State}
    (hext : (guardBlockProg lib mpl i panAddr?).externAt? pc = some f) :
    (∃ pa, panAddr? = some pa ∧ pc = pa ∧ f = Rust.panicked) ∨ f = haltFn := by
  unfold guardBlockProg Program.externAt? Program.hookAtOff? at hext
  dsimp only at hext
  simp only [List.findSome?_nil, Option.or_none] at hext
  obtain ⟨⟨n, o⟩, hmem, hfn⟩ := List.exists_of_findSome?_eq_some hext
  rw [List.mem_append] at hmem
  rcases hmem with hpan | hhalt
  · cases hpa : panAddr? with
    | none => simp [hpa] at hpan
    | some pa =>
      simp only [hpa, List.mem_singleton, Prod.mk.injEq] at hpan
      obtain ⟨rfl, rfl⟩ := hpan
      split at hfn
      · rename_i ho
        have hfn' : some Rust.panicked = some f := hfn
        have hpc_eq := bv_eq_of_sub_toNat_eq (beq_iff_eq.mp ho)
        exact Or.inl ⟨pa, rfl, hpc_eq.symm, (Option.some.inj hfn').symm⟩
      · nomatch hfn
  · simp only [List.mem_map, Prod.mk.injEq] at hhalt
    obtain ⟨a, _, rfl, rfl⟩ := hhalt
    split at hfn
    · have hfn' : some haltFn = some f := hfn
      exact Or.inr (Option.some.inj hfn').symm
    · nomatch hfn

private theorem steps_lift_guardBlock_vm {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hpl : lib.Placeable mpl) {i : Nat} (hi : i < lib.blocks.length)
    {panAddr? : Option (BitVec 64)} {P : Program}
    (hall_svc : lib.blocks[i].patchSafe svc0Pat = true)
    (hall_msr : lib.blocks[i].patchSafe msrTpidrEl0Pat = true)
    (hext_blk : ∀ off : Nat, off < lib.blocks[i].code.length →
      P.externAt? (mpl.base i + BitVec.ofNat 64 off) = none)
    (hpan_P : ∀ pa, panAddr? = some pa → P.externAt? pa = some Rust.panicked)
    {s1' sf' : State}
    (hsteps : Steps (guardBlockProg lib mpl i panAddr?) s1' sf')
    (hout : OutcomeStatus sf'.status) :
    ∀ (s1 : State), s1' = ProofLib.stripS (multiLibKeep lib mpl) s1 →
      lib.CodeLoaded mpl s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (multiLibKeep lib mpl) sf ∧
        Steps P s1 sf ∧ ProofLib.NonSyscallPreserved s1 sf ∧ sf.tpidrEl0 = s1.tpidrEl0 := by
  let G := guardBlockProg lib mpl i panAddr?
  let keep := multiLibKeep lib mpl
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1, rfl⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hcl1
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact False.elim (step_not_halted_or_exc hrest hout (Or.inl (by cases s1; rfl)))
    | extern_fault _ _ _ =>
      exact False.elim (step_not_halted_or_exc hrest hout (Or.inr ⟨_, by cases s1; rfl⟩))
    | @extern f hr1' he' _ _ =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hpc_eq : (ProofLib.stripS keep s1).pc = s1.pc := by cases s1; rfl
      rw [hpc_eq] at he'
      rcases guardBlockProg_externAt_some he' with ⟨pa, hpa, hpc_pa, rfl⟩ | rfl
      · have heP : P.externAt? s1.pc = some Rust.panicked := hpc_pa ▸ hpan_P pa hpa
        have hstep_P : Step P s1 (Rust.panicked s1) :=
          Step.extern hr1 heP (Memory.KeepsFrozen.refl s1.mem) rfl
        have hcomm : Rust.panicked (ProofLib.stripS keep s1) =
            ProofLib.stripS keep (Rust.panicked s1) := by
          cases s1; rfl
        obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest, htp_rest⟩ :=
          ih hout (Rust.panicked s1) hcomm hcl1
        have hnsp1 : ProofLib.NonSyscallPreserved s1 (Rust.panicked s1) := by
          cases s1; exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, fun _ h => h⟩, rfl⟩
        have htp1 : (Rust.panicked s1).tpidrEl0 = s1.tpidrEl0 := by cases s1; rfl
        exact ⟨sf, hsf_eq, .step hstep_P hsteps_P, hnsp1.trans hnsp_rest, htp_rest.trans htp1⟩
      · exact False.elim (step_not_halted_or_exc hrest hout (Or.inl (by cases s1; rfl)))
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hpc_eq : (ProofLib.stripS keep s1).pc = s1.pc := by cases s1; rfl
      have hmem_eq : (ProofLib.stripS keep s1).mem = ProofLib.stripExecOutside keep s1.mem := by
        cases s1; rfl
      change G.fetchMem (ProofLib.stripS keep s1).mem (ProofLib.stripS keep s1).pc = some inst at hfe'
      rw [hpc_eq, hmem_eq] at hfe'
      have ⟨hal_pc, heG, hce, hdec, hk0⟩ :
          s1.pc.toNat % 4 = 0 ∧ G.externAt? s1.pc = none ∧
          s1.mem.canExec s1.pc 4 = true ∧ decode (s1.mem.read32 s1.pc) = some inst ∧
          keep s1.pc = true := by
        unfold Program.fetchMem at hfe'
        cases heG : G.externAt? s1.pc with
        | some _ => rw [heG] at hfe'; nomatch hfe'
        | none =>
          rw [heG] at hfe'
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
          by_cases hal_pc : s1.pc.toNat % 4 = 0
          · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
            split at hfe'
            · contradiction
            · rename_i hce'
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
              have hk0 : keep s1.pc = true := by
                have hce0 := hce'
                unfold Memory.canExec at hce0
                rw [Memory.allPerm_iff] at hce0
                simpa only [BitVec.add_zero] using
                  (ProofLib.strip_perm_x_imp (hce0 0 (by omega))).2
              have hce : s1.mem.canExec s1.pc 4 = true := by
                unfold Memory.canExec at hce' ⊢
                rw [Memory.allPerm_iff] at hce' ⊢
                intro k hk
                have hxk := hce' k hk
                rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
              have hr32 : (ProofLib.stripExecOutside keep s1.mem).read32 s1.pc =
                  s1.mem.read32 s1.pc := by
                simp [Memory.read32, ProofLib.strip_read8]
              rw [hr32] at hfe'
              exact ⟨hal_pc, rfl, hce, hfe', hk0⟩
          · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
            contradiction
      have hoff_i : (s1.pc - mpl.base i).toNat < (lib.blockProgram mpl i).code.length :=
        guardBlockProg_in_block_of_externAt_none heG hk0
      let Ri := lib.blockProgram mpl i
      have hLi : Ri.CodeLoaded s1.mem := hcl1 i hi
      have hlen_i : Ri.code.length = lib.blocks[i].code.length := by
        have hc : Ri.code = (lib.blockLib i).text.patched (lib.blockPlacement mpl i) := rfl
        rw [hc, lib.blockLib_text hi,
          CodeBlock.length_patched_of_aligned _ (hpl.blocks_ok i hi).len_aligned]
      have hpc_off : mpl.base i + BitVec.ofNat 64 (s1.pc - mpl.base i).toNat = s1.pc := by
        simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        bv_lin
      have heP : P.externAt? s1.pc = none :=
        hpc_off ▸ hext_blk (s1.pc - mpl.base i).toNat (hlen_i ▸ hoff_i)
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem
        simp [heP, hal_pc, hce, hdec]
      have hfe_Ri : Ri.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem
        rw [MultiPlacedLib.externAt?_blockProgram_none]
        simp [hal_pc, hce, hdec]
      have hlen_mod : Ri.code.length % 4 = 0 := by
        rw [hlen_i]
        exact (hpl.blocks_ok i hi).len_aligned
      have hin0 : (s1.pc - Ri.base).toNat < Ri.code.length := hoff_i
      have hin4 : (s1.pc - Ri.base).toNat + 4 ≤ Ri.code.length := by
        have hal_b := hLi.aligned
        have hnw_b := hLi.no_wrap
        bv_omega
      have hp_svc : Ri.allInstrs (fun ins => !ins.isSvc0) = true := by
        unfold Ri MultiPlacedLib.blockProgram
        exact PlacedLib.program_noSvc0_of_patchSafe
          (by rw [lib.blockLib_text hi]; exact hall_svc) _
      have hp_msr : Ri.allInstrs (fun ins => !ins.isMsrTpidrEl0) = true := by
        unfold Ri MultiPlacedLib.blockProgram
        exact PlacedLib.program_noMsrTpidrEl0_of_patchSafe
          (by rw [lib.blockLib_text hi]; exact hall_msr) _
      have hHB : Obj.HoldsBytes s1.mem Ri.base Ri.code (fun _ => Perm.rx) :=
        fun idx hidx => ⟨hLi.byte_eq idx hidx, hLi.perm_eq idx hidx, hLi.isLazyFree_eq idx hidx⟩
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs_holdsBytes_in_code hp_svc hLi.aligned hLi.no_wrap
          hHB hin4 hfe_Ri
      have hnmsr : inst.isMsrTpidrEl0 = false := by
        simpa using Program.fetchMem_of_allInstrs_holdsBytes_in_code hp_msr hLi.aligned hLi.no_wrap
          hHB hin4 hfe_Ri
      have hev_G : G.evalInst inst (ProofLib.stripS keep s1) =
          ProofLib.stripS keep (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      have hcl2 : lib.CodeLoaded mpl (execInst inst s1).mem :=
        fun j hj => hstep_P.codeLoaded (hcl1 j hj)
      obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest, htp_rest⟩ :=
        ih hout (execInst inst s1) hev_G hcl2
      have hnsp1 := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1
      have htp1 := execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P, hnsp1.trans hnsp_rest, htp_rest.trans htp1⟩

private theorem stripS_mem (keep : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS keep s).mem = ProofLib.stripExecOutside keep s.mem := by cases s; rfl
private theorem stripS_pc (keep : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS keep s).pc = s.pc := by cases s; rfl
private theorem stripS_sp (keep : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS keep s).sp = s.sp := by cases s; rfl
private theorem stripS_readReg64 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (ProofLib.stripS keep s).readReg64 r = s.readReg64 r := by cases s; rfl

private theorem outcomeStatus_of_subroutineOutcome {α : Type} {spec : Spec α} {x : α}
    {R : SepProp} {s0 sf : State} (hout : SubroutineOutcome spec x R s0 sf) :
    OutcomeStatus sf.status := by
  rcases hout with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, he, _⟩ | ⟨ho, _⟩
  · exact Or.inl hret.2.2
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he⟩))
  · exact Or.inr (Or.inr (Or.inr ho))

private theorem unstrip_outcome_keepsFs_withVmPreserved {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {spec : Spec α} {x : α} {R R_view : SepProp}
    {keep : BitVec 64 → Bool} {s0 sf sf' : State}
    (hsf_eq : sf' = ProofLib.stripS keep sf)
    (hnsp : ProofLib.NonSyscallPreserved s0 sf)
    (htp : sf.tpidrEl0 = s0.tpidrEl0)
    (hunstrip : ∀ {Q : SepProp} {mf : Memory},
      (∀ a, mf.perm a = s0.mem.perm a) →
      (ProofLib.stripExecOutside keep mf ⊨ Q ∗ R_view) →
      (mf ⊨ Q ∗ R))
    (hout' : SubroutineOutcome (lib.withCodeLoaded mpl spec) x
      R_view (ProofLib.stripS keep s0) sf')
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf)
    (h_panic_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.onPanic x (s0.setMem m0) (sf.setMem mf) = spec.onPanic x s0 sf)
    (h_exit_mem : ∀ x c (s0 sf : State) (m0 mf : Memory),
      spec.onExit x c (s0.setMem m0) (sf.setMem mf) = spec.onExit x c s0 sf)
    (h_oom_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.onOom x (s0.setMem m0) (sf.setMem mf) = spec.onOom x s0 sf) :
    SubroutineOutcome (lib.withCodeLoaded mpl (keepsFs (withVmPreserved spec))) x R s0 sf := by
  have hperm_eq : ∀ a, sf.mem.perm a = s0.mem.perm a := fun a => congrFun hnsp.2.1 a
  have hvm : VmPreserved s0 sf := vmPreserved_of_nonSyscall_tpidr hnsp htp
  subst hsf_eq
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨hp_st', hp'⟩ | ⟨c, he_st', he'⟩ | ⟨ho_st', ho'⟩
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · rcases hret' with ⟨hr_pc, hr_sp, hr_st⟩
      rw [stripS_pc] at hr_pc
      rw [stripS_sp] at hr_sp
      exact ⟨hr_pc.trans (stripS_readReg64 keep s0 Reg.lr),
        hr_sp.trans (stripS_sp keep s0), by cases sf; exact hr_st⟩
    · rcases hcc' with ⟨hsp_cc, hcs⟩
      rw [stripS_sp] at hsp_cc
      exact ⟨hsp_cc.trans (stripS_sp keep s0), by cases s0; cases sf; exact hcs⟩
    · dsimp only [MultiPlacedLib.withCodeLoaded, keepsFs, withVmPreserved] at hpost' ⊢
      dsimp only [ProofLib.stripS] at hpost'
      rw [h_post_mem, State.mem_setMem] at hpost'
      have hpost_sf : sf.mem ⊨ spec.post x s0 sf ∗ R := hunstrip hperm_eq hpost'
      simp only [sepConj_assoc]
      rw [satisfies_pure_sepConj]
      refine ⟨hnsp.2.2.2.2.2.2, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hvm, hpost_sf⟩
  · refine Or.inr (Or.inl ⟨by cases sf; exact hp_st', ?_⟩)
    dsimp only [MultiPlacedLib.withCodeLoaded, keepsFs, withVmPreserved] at hp' ⊢
    dsimp only [ProofLib.stripS] at hp'
    rw [h_panic_mem, State.mem_setMem] at hp'
    exact hunstrip hperm_eq hp'
  · refine Or.inr (Or.inr (Or.inl ⟨c, by cases sf; exact he_st', ?_⟩))
    dsimp only [MultiPlacedLib.withCodeLoaded, keepsFs, withVmPreserved] at he' ⊢
    dsimp only [ProofLib.stripS] at he'
    rw [h_exit_mem, State.mem_setMem] at he'
    exact hunstrip hperm_eq he'
  · refine Or.inr (Or.inr (Or.inr ⟨by cases sf; exact ho_st', ?_⟩))
    dsimp only [MultiPlacedLib.withCodeLoaded, keepsFs, withVmPreserved] at ho' ⊢
    dsimp only [ProofLib.stripS] at ho'
    rw [h_oom_mem, State.mem_setMem] at ho'
    exact hunstrip hperm_eq ho'

/-- Lift a program-polymorphic single-block `subroutine_ok` proof on block `i` of `lib` to
    `keepsFs (withVmPreserved spec)` on arbitrary `P : Program` (preserving `onPanic`, `onExit`,
    and `onOom`). -/
theorem subroutine_ok_placedBlock_withVmPreserved_keepsFs {α : Type}
    {lib : MultiPlacedLib} {mpl : MultiPlacement} (hpl : lib.Placeable mpl)
    {i : Nat} (hi : i < lib.blocks.length) {panAddr? : Option (BitVec 64)}
    {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h_sub : ∀ Q : Program,
      (∀ off : Nat, off < lib.blocks[i].code.length →
        Q.externAt? (mpl.base i + BitVec.ofNat 64 off) = none) →
      (∀ pa, panAddr? = some pa → Q.externAt? pa = some Rust.panicked) →
      subroutine_ok Q entry (lib.withCodeLoaded mpl spec))
    (h_svc0 : lib.blocks[i].patchSafe svc0Pat = true)
    (h_msr : lib.blocks[i].patchSafe msrTpidrEl0Pat = true)
    (h_ext_blk : ∀ off : Nat, off < lib.blocks[i].code.length →
      P.externAt? (mpl.base i + BitVec.ofNat 64 off) = none)
    (h_pan_P : ∀ pa, panAddr? = some pa → P.externAt? pa = some Rust.panicked)
    (h_pre_strip : ∀ x (s0 : State) (keep : BitVec 64 → Bool) (Rv : SepProp),
      (ProofLib.stripExecOutside keep s0.mem ⊨ spec.pre x s0 ∗ Rv) →
      (ProofLib.stripExecOutside keep s0.mem ⊨
        spec.pre x (ProofLib.stripS keep s0) ∗ Rv) := by
      intro _ s0 _ _ h; cases s0; exact h)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_panic_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.onPanic x (s0.setMem m0) (sf.setMem mf) = spec.onPanic x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_exit_mem : ∀ x c (s0 sf : State) (m0 mf : Memory),
      spec.onExit x c (s0.setMem m0) (sf.setMem mf) = spec.onExit x c s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_oom_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.onOom x (s0.setMem m0) (sf.setMem mf) = spec.onOom x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    subroutine_ok P entry (lib.withCodeLoaded mpl (keepsFs (withVmPreserved spec))) := by
  let G := guardBlockProg lib mpl i panAddr?
  let keep := multiLibKeep lib mpl
  have hG_sub : subroutine_ok G entry (lib.withCodeLoaded mpl spec) := by
    refine h_sub G (fun off hoff => ?_) (fun pa hpa => ?_)
    · refine guardBlockProg_externAt_block_none hpl hi hoff (fun pa hpa heq => ?_)
      have hnone := h_ext_blk off hoff
      have hsome := h_pan_P pa hpa
      rw [heq, hsome] at hnone
      nomatch hnone
    · subst hpa
      exact guardBlockProg_externAt_panic lib mpl i pa
  apply ProofLib.subroutine_ok_of_steps_outcome
  intro x R s0 hpc hrun hpre hsp _hLP
  have hpre_cl : s0.mem ⊨ ⌜lib.CodeLoaded mpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by
    dsimp only [MultiPlacedLib.withCodeLoaded, keepsFs, withVmPreserved] at hpre
    rw [sepConj_comm (spec.pre x s0) ⌜_⌝, sepConj_assoc] at hpre
    exact hpre
  rw [satisfies_pure_sepConj] at hpre_cl
  obtain ⟨hcl, hpre_x⟩ := hpre_cl
  obtain ⟨R_view, hpre_strip0, hunstrip⟩ := ProofLib.strip_frame keep hpre_x
  have hcl' : lib.CodeLoaded mpl (ProofLib.stripS keep s0).mem := by
    rw [stripS_mem]
    exact strip_codeLoaded_multi hcl
  have hLG' : G.CodeLoaded (ProofLib.stripS keep s0).mem :=
    (hcl' i hi).of_base_code rfl rfl
  have hpreG' :
      (ProofLib.stripS keep s0).mem ⊨
        (lib.withCodeLoaded mpl spec).pre x (ProofLib.stripS keep s0) ∗ R_view := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm (spec.pre x _) ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl', stripS_mem]
    exact h_pre_strip x s0 keep R_view hpre_strip0
  obtain ⟨sf', hsteps', hout'⟩ :=
    ProofLib.subroutine_ok_elim_steps_outcome hG_sub x R_view (ProofLib.stripS keep s0)
      ((stripS_pc keep s0).trans hpc) (by cases s0; exact hrun) hpreG'
      (by cases s0; exact hsp) hLG'
  obtain ⟨sf, hsf_eq, hstepsP, hnsp, htp⟩ :=
    steps_lift_guardBlock_vm hpl hi h_svc0 h_msr h_ext_blk h_pan_P hsteps'
      (outcomeStatus_of_subroutineOutcome hout') s0 rfl hcl
  exact ⟨sf, hstepsP, unstrip_outcome_keepsFs_withVmPreserved hsf_eq hnsp htp hunstrip hout'
    h_post_mem h_panic_mem h_exit_mem h_oom_mem⟩

/-- Lift a program-polymorphic single-block `subroutine_ok` proof on block `i` of `lib` to
    `withVmPreserved` on arbitrary `P : Program`. -/
theorem subroutine_ok_placedBlock_withVmPreserved {α : Type}
    {lib : MultiPlacedLib} {mpl : MultiPlacement} (hpl : lib.Placeable mpl)
    {i : Nat} (hi : i < lib.blocks.length) {panAddr? : Option (BitVec 64)}
    {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h_sub : ∀ Q : Program,
      (∀ off : Nat, off < lib.blocks[i].code.length →
        Q.externAt? (mpl.base i + BitVec.ofNat 64 off) = none) →
      (∀ pa, panAddr? = some pa → Q.externAt? pa = some Rust.panicked) →
      subroutine_ok Q entry (lib.withCodeLoaded mpl spec))
    (h_svc0 : lib.blocks[i].patchSafe svc0Pat = true)
    (h_msr : lib.blocks[i].patchSafe msrTpidrEl0Pat = true)
    (h_ext_blk : ∀ off : Nat, off < lib.blocks[i].code.length →
      P.externAt? (mpl.base i + BitVec.ofNat 64 off) = none)
    (h_pan_P : ∀ pa, panAddr? = some pa → P.externAt? pa = some Rust.panicked)
    (h_pre_strip : ∀ x (s0 : State) (keep : BitVec 64 → Bool) (Rv : SepProp),
      (ProofLib.stripExecOutside keep s0.mem ⊨ spec.pre x s0 ∗ Rv) →
      (ProofLib.stripExecOutside keep s0.mem ⊨
        spec.pre x (ProofLib.stripS keep s0) ∗ Rv) := by
      intro _ s0 _ _ h; cases s0; exact h)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_panic_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.onPanic x (s0.setMem m0) (sf.setMem mf) = spec.onPanic x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_exit_mem : ∀ x c (s0 sf : State) (m0 mf : Memory),
      spec.onExit x c (s0.setMem m0) (sf.setMem mf) = spec.onExit x c s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_oom_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.onOom x (s0.setMem m0) (sf.setMem mf) = spec.onOom x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    subroutine_ok P entry (lib.withCodeLoaded mpl (withVmPreserved spec)) :=
  (SpecSimulates.drop_keepsFs.withCodeLoaded lib mpl).subroutine_ok
    (subroutine_ok_placedBlock_withVmPreserved_keepsFs hpl hi h_sub h_svc0 h_msr h_ext_blk h_pan_P
      h_pre_strip h_post_mem h_panic_mem h_exit_mem h_oom_mem)

/-- Lift `lib.blockProgram mpl i X` `subroutine_ok` across all blocks of `lib` to
    `keepsFs (withVmPreserved spec)` when every block of `lib` avoids `SVC #0` and `MSR TPIDR_EL0`
    and every active extern of block `i` is `Rust.panicked`. -/
theorem subroutine_ok_blockProgram_withVmPreserved_keepsFs {α : Type}
    {lib : MultiPlacedLib} {mpl : MultiPlacement} (hpl : lib.Placeable mpl)
    {i : Nat} (hi : i < lib.blocks.length) {X : String → Option (State → State)}
    {entry : BitVec 64} {spec : Spec α}
    (h_sub : subroutine_ok (lib.blockProgram mpl i X) entry (lib.withCodeLoaded mpl spec))
    (h_svc0 : ∀ k (hk : k < lib.blocks.length), lib.blocks[k].patchSafe svc0Pat = true)
    (h_msr : ∀ k (hk : k < lib.blocks.length), lib.blocks[k].patchSafe msrTpidrEl0Pat = true)
    (h_ext_pan : ∀ pc f, (lib.blockProgram mpl i X).externAt? pc = some f → f = Rust.panicked)
    (h_pre_strip : ∀ x (s0 : State) (keep : BitVec 64 → Bool) (Rv : SepProp),
      (ProofLib.stripExecOutside keep s0.mem ⊨ spec.pre x s0 ∗ Rv) →
      (ProofLib.stripExecOutside keep s0.mem ⊨
        spec.pre x (ProofLib.stripS keep s0) ∗ Rv) := by
      intro _ s0 _ _ h; cases s0; exact h)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_panic_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.onPanic x (s0.setMem m0) (sf.setMem mf) = spec.onPanic x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_exit_mem : ∀ x c (s0 sf : State) (m0 mf : Memory),
      spec.onExit x c (s0.setMem m0) (sf.setMem mf) = spec.onExit x c s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_oom_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.onOom x (s0.setMem m0) (sf.setMem mf) = spec.onOom x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    subroutine_ok (lib.blockProgram mpl i X) entry
      (lib.withCodeLoaded mpl (keepsFs (withVmPreserved spec))) := by
  let Q := lib.blockProgram mpl i X
  let keep := multiLibKeep lib mpl
  apply ProofLib.subroutine_ok_of_steps_outcome
  intro x R s0 hpc hrun hpre hsp _hLQ
  have hpre_cl : s0.mem ⊨ ⌜lib.CodeLoaded mpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by
    dsimp only [MultiPlacedLib.withCodeLoaded, keepsFs, withVmPreserved] at hpre
    rw [sepConj_comm (spec.pre x s0) ⌜_⌝, sepConj_assoc] at hpre; exact hpre
  rw [satisfies_pure_sepConj] at hpre_cl
  obtain ⟨hcl, hpre_x⟩ := hpre_cl
  obtain ⟨R_view, hpre_strip0, hunstrip⟩ := ProofLib.strip_frame keep hpre_x
  have hcl' : lib.CodeLoaded mpl (ProofLib.stripS keep s0).mem := by
    rw [stripS_mem]; exact strip_codeLoaded_multi hcl
  have hLQ' : Q.CodeLoaded (ProofLib.stripS keep s0).mem := (hcl' i hi).of_base_code rfl rfl
  have hpreQ' : (ProofLib.stripS keep s0).mem ⊨
      (lib.withCodeLoaded mpl spec).pre x (ProofLib.stripS keep s0) ∗ R_view := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm (spec.pre x _) ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl', stripS_mem]
    exact h_pre_strip x s0 keep R_view hpre_strip0
  obtain ⟨sf', hsteps', hout'⟩ :=
    ProofLib.subroutine_ok_elim_steps_outcome h_sub x R_view (ProofLib.stripS keep s0)
      ((stripS_pc keep s0).trans hpc) (by cases s0; exact hrun) hpreQ'
      (by cases s0; exact hsp) hLQ'
  obtain ⟨sf, hsf_eq, hstepsQ, hnsp, htp⟩ :=
    steps_lift_multiBlocks_vm hpl h_svc0 h_msr h_ext_pan hsteps'
      (outcomeStatus_of_subroutineOutcome hout') s0 rfl hcl
  exact ⟨sf, hstepsQ, unstrip_outcome_keepsFs_withVmPreserved hsf_eq hnsp htp hunstrip hout'
    h_post_mem h_panic_mem h_exit_mem h_oom_mem⟩

/-- Lift `lib.blockProgram mpl i X` `subroutine_ok` across all blocks of `lib` to `withVmPreserved`. -/
theorem subroutine_ok_blockProgram_withVmPreserved {α : Type}
    {lib : MultiPlacedLib} {mpl : MultiPlacement} (hpl : lib.Placeable mpl)
    {i : Nat} (hi : i < lib.blocks.length) {X : String → Option (State → State)}
    {entry : BitVec 64} {spec : Spec α}
    (h_sub : subroutine_ok (lib.blockProgram mpl i X) entry (lib.withCodeLoaded mpl spec))
    (h_svc0 : ∀ k (hk : k < lib.blocks.length), lib.blocks[k].patchSafe svc0Pat = true)
    (h_msr : ∀ k (hk : k < lib.blocks.length), lib.blocks[k].patchSafe msrTpidrEl0Pat = true)
    (h_ext_pan : ∀ pc f, (lib.blockProgram mpl i X).externAt? pc = some f → f = Rust.panicked)
    (h_pre_strip : ∀ x (s0 : State) (keep : BitVec 64 → Bool) (Rv : SepProp),
      (ProofLib.stripExecOutside keep s0.mem ⊨ spec.pre x s0 ∗ Rv) →
      (ProofLib.stripExecOutside keep s0.mem ⊨
        spec.pre x (ProofLib.stripS keep s0) ∗ Rv) := by
      intro _ s0 _ _ h; cases s0; exact h)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_panic_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.onPanic x (s0.setMem m0) (sf.setMem mf) = spec.onPanic x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_exit_mem : ∀ x c (s0 sf : State) (m0 mf : Memory),
      spec.onExit x c (s0.setMem m0) (sf.setMem mf) = spec.onExit x c s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_oom_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.onOom x (s0.setMem m0) (sf.setMem mf) = spec.onOom x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    subroutine_ok (lib.blockProgram mpl i X) entry
      (lib.withCodeLoaded mpl (withVmPreserved spec)) :=
  (SpecSimulates.drop_keepsFs.withCodeLoaded lib mpl).subroutine_ok
    (subroutine_ok_blockProgram_withVmPreserved_keepsFs hpl hi h_sub h_svc0 h_msr h_ext_pan
      h_pre_strip h_post_mem h_panic_mem h_exit_mem h_oom_mem)

/-- Lift `MultiPlacedLib.subroutineOk` directly to `keepsFs (withVmPreserved ...)` when every
    block of `lib` avoids `SVC #0` and `MSR TPIDR_EL0` and every active extern of `fnName`'s
    defining block is `Rust.panicked`. -/
theorem multiSubroutineOk_withVmPreserved_keepsFs {α : Type} {lib : MultiPlacedLib}
    {fnName : String} {spec : MultiPlacement → Spec α}
    {externs : String → Option (State → State)} {i₀ off₀ : Nat}
    (h : lib.subroutineOk fnName spec externs)
    (hfn₀ : lookupBlockSym fnName lib.blocks = some (i₀, off₀) := by rfl)
    (hi₀ : i₀ < lib.blocks.length := by decide)
    (h_svc0 : ∀ k (hk : k < lib.blocks.length), lib.blocks[k].patchSafe svc0Pat = true)
    (h_msr : ∀ k (hk : k < lib.blocks.length), lib.blocks[k].patchSafe msrTpidrEl0Pat = true)
    (h_ext_pan : ∀ mpl pc f,
      (lib.blockProgram mpl i₀ externs).externAt? pc = some f → f = Rust.panicked)
    (h_pre_strip : ∀ mpl x (s0 : State) (keep : BitVec 64 → Bool) (Rv : SepProp),
      (ProofLib.stripExecOutside keep s0.mem ⊨ (spec mpl).pre x s0 ∗ Rv) →
      (ProofLib.stripExecOutside keep s0.mem ⊨
        (spec mpl).pre x (ProofLib.stripS keep s0) ∗ Rv) := by
      intro _ _ s0 _ _ h; cases s0; exact h)
    (h_post_mem : ∀ mpl x (s0 sf : State) (m0 mf : Memory),
      (spec mpl).post x (s0.setMem m0) (sf.setMem mf) = (spec mpl).post x s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_panic_mem : ∀ mpl x (s0 sf : State) (m0 mf : Memory),
      (spec mpl).onPanic x (s0.setMem m0) (sf.setMem mf) = (spec mpl).onPanic x s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_exit_mem : ∀ mpl x c (s0 sf : State) (m0 mf : Memory),
      (spec mpl).onExit x c (s0.setMem m0) (sf.setMem mf) = (spec mpl).onExit x c s0 sf := by
      intro _ _ _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_oom_mem : ∀ mpl x (s0 sf : State) (m0 mf : Memory),
      (spec mpl).onOom x (s0.setMem m0) (sf.setMem mf) = (spec mpl).onOom x s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl) :
    lib.subroutineOk fnName (fun mpl => keepsFs (withVmPreserved (spec mpl))) externs := by
  obtain ⟨hexp, i, off, hfn, hsub⟩ := h
  have hpair : (i, off) = (i₀, off₀) := Option.some.inj (hfn.symm.trans hfn₀)
  have hi_eq : i = i₀ := congrArg Prod.fst hpair
  exact ⟨hexp, i₀, off₀, hfn₀, fun mpl hpl =>
    subroutine_ok_blockProgram_withVmPreserved_keepsFs hpl hi₀ (hi_eq ▸ hsub mpl hpl)
      h_svc0 h_msr (h_ext_pan mpl)
      (h_pre_strip mpl) (h_post_mem mpl) (h_panic_mem mpl) (h_exit_mem mpl) (h_oom_mem mpl)⟩

/-- Lift `MultiPlacedLib.subroutineOk` directly to `withVmPreserved`. -/
theorem multiSubroutineOk_withVmPreserved {α : Type} {lib : MultiPlacedLib}
    {fnName : String} {spec : MultiPlacement → Spec α}
    {externs : String → Option (State → State)} {i₀ off₀ : Nat}
    (h : lib.subroutineOk fnName spec externs)
    (hfn₀ : lookupBlockSym fnName lib.blocks = some (i₀, off₀) := by rfl)
    (hi₀ : i₀ < lib.blocks.length := by decide)
    (h_svc0 : ∀ k (hk : k < lib.blocks.length), lib.blocks[k].patchSafe svc0Pat = true)
    (h_msr : ∀ k (hk : k < lib.blocks.length), lib.blocks[k].patchSafe msrTpidrEl0Pat = true)
    (h_ext_pan : ∀ mpl pc f,
      (lib.blockProgram mpl i₀ externs).externAt? pc = some f → f = Rust.panicked)
    (h_pre_strip : ∀ mpl x (s0 : State) (keep : BitVec 64 → Bool) (Rv : SepProp),
      (ProofLib.stripExecOutside keep s0.mem ⊨ (spec mpl).pre x s0 ∗ Rv) →
      (ProofLib.stripExecOutside keep s0.mem ⊨
        (spec mpl).pre x (ProofLib.stripS keep s0) ∗ Rv) := by
      intro _ _ s0 _ _ h; cases s0; exact h)
    (h_post_mem : ∀ mpl x (s0 sf : State) (m0 mf : Memory),
      (spec mpl).post x (s0.setMem m0) (sf.setMem mf) = (spec mpl).post x s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_panic_mem : ∀ mpl x (s0 sf : State) (m0 mf : Memory),
      (spec mpl).onPanic x (s0.setMem m0) (sf.setMem mf) = (spec mpl).onPanic x s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_exit_mem : ∀ mpl x c (s0 sf : State) (m0 mf : Memory),
      (spec mpl).onExit x c (s0.setMem m0) (sf.setMem mf) = (spec mpl).onExit x c s0 sf := by
      intro _ _ _ s0 sf _ _; cases s0; cases sf; rfl)
    (h_oom_mem : ∀ mpl x (s0 sf : State) (m0 mf : Memory),
      (spec mpl).onOom x (s0.setMem m0) (sf.setMem mf) = (spec mpl).onOom x s0 sf := by
      intro _ _ s0 sf _ _; cases s0; cases sf; rfl) :
    lib.subroutineOk fnName (fun mpl => withVmPreserved (spec mpl)) externs :=
  SpecSimulates.multiSubroutineOk (fun _ => SpecSimulates.drop_keepsFs)
    (multiSubroutineOk_withVmPreserved_keepsFs h hfn₀ hi₀ h_svc0 h_msr h_ext_pan
      h_pre_strip h_post_mem h_panic_mem h_exit_mem h_oom_mem)

/-- When block `i` of `lib` has no external call relocations (`(lib.blockLib i).text.externs = []`),
    `lib.blockProgram mpl i externs` has no extern hooks at any PC for any `externs` map. -/
theorem blockProgram_externAt_none_of_no_externs {lib : MultiPlacedLib}
    (mpl : MultiPlacement) (i : Nat)
    (hext_nil : (lib.blockLib i).text.externs = [] := by rfl)
    (externs : String → Option (State → State)) (pc : BitVec 64) :
    (lib.blockProgram mpl i externs).externAt? pc = none := by
  unfold MultiPlacedLib.blockProgram PlacedLib.program Program.externAt? Program.hookAtOff?
  dsimp only
  have hov :
      ((lib.blockLib i).text.symbols.findSome? fun (_n, o) =>
        if o == (pc - (lib.blockPlacement mpl i).base).toNat then
          (none : Option (State → State))
        else none) = none := by
    induction (lib.blockLib i).text.symbols <;> simp [*]
  rw [hov, Option.or_none, hext_nil]
  rfl

/-- Helper discharging `h_pre_strip` for `withRoData addr bytes spec` when `spec.pre` is
    memory-independent (`spec.pre x (s.setMem m) = spec.pre x s`). -/
theorem pre_strip_withRoData {α : Type} {addr : BitVec 64} {bytes : List (BitVec 8)}
    {spec : Spec α}
    (hpm : ∀ x (s : State) (m : Memory), spec.pre x (s.setMem m) = spec.pre x s := by
      intro _ s _; cases s; rfl) :
    ∀ x (s0 : State) (keep : BitVec 64 → Bool) (Rv : SepProp),
      (ProofLib.stripExecOutside keep s0.mem ⊨ (withRoData addr bytes spec).pre x s0 ∗ Rv) →
      (ProofLib.stripExecOutside keep s0.mem ⊨
        (withRoData addr bytes spec).pre x (ProofLib.stripS keep s0) ∗ Rv) := by
  intro x s0 keep Rv hpre
  dsimp only [withRoData] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hro, hpre_x⟩ := hpre
  have hro' : RoDataAt (ProofLib.stripS keep s0).mem addr bytes := by
    rw [stripS_mem]
    exact roDataAt_stripExecOutside keep hro
  have hp_eq : spec.pre x (ProofLib.stripS keep s0) = spec.pre x s0 :=
    hpm x s0 (ProofLib.stripExecOutside keep s0.mem)
  rw [hp_eq, sepConj_assoc, pure_sepConj_of_true hro']
  exact hpre_x

/-! ## 2. Opcode-Exclusion Checks on `timeMultiLib` -/

theorem timeMultiLib_patchSafe_svc0 :
    ∀ k (hk : k < timeMultiLib.blocks.length),
      timeMultiLib.blocks[k].patchSafe svc0Pat = true := by
  have hall : (timeMultiLib.blocks.all fun b => b.patchSafe svc0Pat) = true := by decide +kernel
  intro k hk
  exact List.all_eq_true.mp hall _ (List.getElem_mem hk)

theorem timeMultiLib_patchSafe_msrTpidrEl0 :
    ∀ k (hk : k < timeMultiLib.blocks.length),
      timeMultiLib.blocks[k].patchSafe msrTpidrEl0Pat = true := by
  have hall : (timeMultiLib.blocks.all fun b => b.patchSafe msrTpidrEl0Pat) = true := by
    decide +kernel
  intro k hk
  exact List.all_eq_true.mp hall _ (List.getElem_mem hk)

private theorem timeMultiLib_blk2_externAt_panicked (mpl : MultiPlacement)
    {externs : String → Option (State → State)}
    (hpanic : externs rustTimeExpectFailedSym = some Rust.panicked) :
    ∀ pc f, (timeMultiLib.blockProgram mpl 2 externs).externAt? pc = some f →
      f = Rust.panicked := by
  intro pc f hext
  unfold MultiPlacedLib.blockProgram PlacedLib.program Program.externAt? Program.hookAtOff? at hext
  dsimp only at hext
  have hov :
      ((timeMultiLib.blockLib 2).text.symbols.findSome? fun (_n, o) =>
        if o == (pc - (timeMultiLib.blockPlacement mpl 2).base).toNat then
          (none : Option (State → State))
        else none) =
        none := by
    induction (timeMultiLib.blockLib 2).text.symbols <;> simp [*]
  rw [hov, Option.or_none] at hext
  have hexts : (timeMultiLib.blockLib 2).text.externs = [rustTimeExpectFailedSym] := rfl
  rw [hexts] at hext
  simp only [List.map_cons, List.map_nil, List.findSome?_cons, List.findSome?_nil] at hext
  rw [hpanic] at hext
  split at hext
  · rename_i b hb
    split at hb
    · exact (Option.some.inj hext).symm.trans (Option.some.inj hb).symm
    · nomatch hb
  · nomatch hext

/-! ## 3. Consumer-Exact `<SystemTime as Add<Duration>>::add` Discharges -/

/-- `Heap.SpecBudget.timeAddBudgetSpec` and `SegFromPlacedBudget.TempTwins.timeAddBudgetSpec` are `rfl`-equal. -/
theorem timeAddBudgetSpec_eq_segFrom :
    LibsignalBinary.Heap.SpecBudget.timeAddBudgetSpec =
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins.timeAddBudgetSpec := rfl

/-- Program-generic real-code discharge for `CryptoVerification.LibsignalPublicApi.timeAddSpec`. -/
theorem timeAdd_placed_publicApi_timeAddSpec_ok {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 96 → P.externAt? (mpl.base 2 + BitVec.ofNat 64 off) = none)
    (hpanic : P.externAt? ((timeMultiLib.blockPlacement mpl 2).ρ rustTimeExpectFailedSym) =
      some Rust.panicked) :
    subroutine_ok P (timeMultiLib.fnAddr mpl timeAddSym)
      (timeMultiLib.withCodeLoaded mpl CryptoVerification.LibsignalPublicApi.timeAddSpec) :=
  timeAdd_placed_timeAddSpec_ok hpl hext hpanic

/-- `MultiPlacedLib.subroutineOk` for `LibsignalPublicApi.timeAddSpec` (`_of_panic`). -/
theorem timeAdd_publicApi_timeAddSpec_subroutineOk_of_panic
    {externs : String → Option (State → State)}
    (hpanic : externs rustTimeExpectFailedSym = some Rust.panicked) :
    timeMultiLib.subroutineOk timeAddSym
      (fun _ => CryptoVerification.LibsignalPublicApi.timeAddSpec) externs :=
  timeAdd_timeAddSpec_subroutineOk_of_panic hpanic

/-- Canonical `MultiPlacedLib.subroutineOk` for `LibsignalPublicApi.timeAddSpec`. -/
theorem timeAdd_publicApi_timeAddSpec_subroutineOk
    (hooks : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeAddSym
      (fun _ => CryptoVerification.LibsignalPublicApi.timeAddSpec) (timeExterns hooks) :=
  timeAdd_timeAddSpec_subroutineOk hooks

/-- Program-generic real-code discharge for `keepsFs Heap.SpecBudget.timeAddBudgetSpec`
    (`Heap/SpecBudget.lean:526`). -/
theorem timeAdd_placed_timeAddBudgetSpec_keepsFs_ok {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 96 → P.externAt? (mpl.base 2 + BitVec.ofNat 64 off) = none)
    (hpanic : P.externAt? ((timeMultiLib.blockPlacement mpl 2).ρ rustTimeExpectFailedSym) =
      some Rust.panicked) :
    subroutine_ok P (timeMultiLib.fnAddr mpl timeAddSym)
      (timeMultiLib.withCodeLoaded mpl
        (keepsFs LibsignalBinary.Heap.SpecBudget.timeAddBudgetSpec)) := by
  have hlen2 : timeMultiLib.blocks[2].code.length = 96 := by decide +kernel
  exact subroutine_ok_placedBlock_withVmPreserved_keepsFs (lib := timeMultiLib) (mpl := mpl)
    (i := 2) (panAddr? := some ((timeMultiLib.blockPlacement mpl 2).ρ rustTimeExpectFailedSym))
    (spec := CryptoVerification.LibsignalPublicApi.timeAddSpec)
    hpl (by decide)
    (fun Q heQ hpQ =>
      timeAdd_placed_timeAddSpec_ok hpl (fun off hoff => heQ off (hlen2.symm ▸ hoff)) (hpQ _ rfl))
    (timeMultiLib_patchSafe_svc0 2 (by decide))
    (timeMultiLib_patchSafe_msrTpidrEl0 2 (by decide))
    (fun off hoff => hext off (hlen2 ▸ hoff))
    (fun pa hpa => Option.some.inj hpa ▸ hpanic)

/-- Program-generic real-code discharge for `LibsignalBinary.Heap.SpecBudget.timeAddBudgetSpec`
    (`Heap/SpecBudget.lean:526`). -/
theorem timeAdd_placed_timeAddBudgetSpec_ok {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 96 → P.externAt? (mpl.base 2 + BitVec.ofNat 64 off) = none)
    (hpanic : P.externAt? ((timeMultiLib.blockPlacement mpl 2).ρ rustTimeExpectFailedSym) =
      some Rust.panicked) :
    subroutine_ok P (timeMultiLib.fnAddr mpl timeAddSym)
      (timeMultiLib.withCodeLoaded mpl LibsignalBinary.Heap.SpecBudget.timeAddBudgetSpec) :=
  (SpecSimulates.drop_keepsFs.withCodeLoaded timeMultiLib mpl).subroutine_ok
    (timeAdd_placed_timeAddBudgetSpec_keepsFs_ok hpl hext hpanic)

/-- `MultiPlacedLib.subroutineOk` for `keepsFs Heap.SpecBudget.timeAddBudgetSpec` under any extern
    table mapping `rustTimeExpectFailedSym` to `Rust.panicked`. -/
theorem timeAdd_timeAddBudgetSpec_keepsFs_subroutineOk_of_panic
    {externs : String → Option (State → State)}
    (hpanic : externs rustTimeExpectFailedSym = some Rust.panicked) :
    timeMultiLib.subroutineOk timeAddSym
      (fun _ => keepsFs LibsignalBinary.Heap.SpecBudget.timeAddBudgetSpec) externs :=
  multiSubroutineOk_withVmPreserved_keepsFs
    (spec := fun _ => CryptoVerification.LibsignalPublicApi.timeAddSpec)
    (timeAdd_timeAddSpec_subroutineOk_of_panic hpanic) rfl (by decide)
    timeMultiLib_patchSafe_svc0 timeMultiLib_patchSafe_msrTpidrEl0
    (fun mpl => timeMultiLib_blk2_externAt_panicked mpl hpanic)

/-- `MultiPlacedLib.subroutineOk` for `LibsignalBinary.Heap.SpecBudget.timeAddBudgetSpec`
    (`Heap/SpecBudget.lean:526`) under any extern table mapping `rustTimeExpectFailedSym` to
    `Rust.panicked`. -/
theorem timeAdd_timeAddBudgetSpec_subroutineOk_of_panic
    {externs : String → Option (State → State)}
    (hpanic : externs rustTimeExpectFailedSym = some Rust.panicked) :
    timeMultiLib.subroutineOk timeAddSym
      (fun _ => LibsignalBinary.Heap.SpecBudget.timeAddBudgetSpec) externs :=
  multiSubroutineOk_withVmPreserved
    (spec := fun _ => CryptoVerification.LibsignalPublicApi.timeAddSpec)
    (timeAdd_timeAddSpec_subroutineOk_of_panic hpanic) rfl (by decide)
    timeMultiLib_patchSafe_svc0 timeMultiLib_patchSafe_msrTpidrEl0
    (fun mpl => timeMultiLib_blk2_externAt_panicked mpl hpanic)

/-- Canonical `MultiPlacedLib.subroutineOk` for `keepsFs Heap.SpecBudget.timeAddBudgetSpec`. -/
theorem timeAdd_timeAddBudgetSpec_keepsFs_subroutineOk
    (hooks : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeAddSym
      (fun _ => keepsFs LibsignalBinary.Heap.SpecBudget.timeAddBudgetSpec) (timeExterns hooks) :=
  timeAdd_timeAddBudgetSpec_keepsFs_subroutineOk_of_panic
    (VerifiedLibraries.RustStd.timeExterns_expectFailed hooks)

/-- Canonical `MultiPlacedLib.subroutineOk` for `LibsignalBinary.Heap.SpecBudget.timeAddBudgetSpec`. -/
theorem timeAdd_timeAddBudgetSpec_subroutineOk
    (hooks : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeAddSym
      (fun _ => LibsignalBinary.Heap.SpecBudget.timeAddBudgetSpec) (timeExterns hooks) :=
  timeAdd_timeAddBudgetSpec_subroutineOk_of_panic
    (VerifiedLibraries.RustStd.timeExterns_expectFailed hooks)

/-- Program-generic real-code discharge for `SegFromPlacedBudget.TempTwins.timeAddBudgetSpec`. -/
theorem timeAdd_placed_segFrom_timeAddBudgetSpec_ok {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 96 → P.externAt? (mpl.base 2 + BitVec.ofNat 64 off) = none)
    (hpanic : P.externAt? ((timeMultiLib.blockPlacement mpl 2).ρ rustTimeExpectFailedSym) =
      some Rust.panicked) :
    subroutine_ok P (timeMultiLib.fnAddr mpl timeAddSym)
      (timeMultiLib.withCodeLoaded mpl
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins.timeAddBudgetSpec) :=
  timeAddBudgetSpec_eq_segFrom ▸ timeAdd_placed_timeAddBudgetSpec_ok hpl hext hpanic

/-- `MultiPlacedLib.subroutineOk` for `SegFromPlacedBudget.TempTwins.timeAddBudgetSpec` (`_of_panic`). -/
theorem timeAdd_segFrom_timeAddBudgetSpec_subroutineOk_of_panic
    {externs : String → Option (State → State)}
    (hpanic : externs rustTimeExpectFailedSym = some Rust.panicked) :
    timeMultiLib.subroutineOk timeAddSym
      (fun _ => LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins.timeAddBudgetSpec)
      externs :=
  timeAddBudgetSpec_eq_segFrom ▸ timeAdd_timeAddBudgetSpec_subroutineOk_of_panic hpanic

/-- Canonical `MultiPlacedLib.subroutineOk` for `SegFromPlacedBudget.TempTwins.timeAddBudgetSpec`. -/
theorem timeAdd_segFrom_timeAddBudgetSpec_subroutineOk
    (hooks : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeAddSym
      (fun _ => LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins.timeAddBudgetSpec)
      (timeExterns hooks) :=
  timeAddBudgetSpec_eq_segFrom ▸ timeAdd_timeAddBudgetSpec_subroutineOk hooks

end LibsignalBinary.Proofs.HookDischarge.RustStd.TimeAddVm
