/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.Wave1.TimeDurationSince
public import ProofLib.Placed.OpcodeExclusion
public import LibsignalBinary.Proofs.HookDischarge.RustStd.TimeDurationSince -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.SpecBudget
import ProofLib.Hoare.Model
import ProofLib.SepLogic.WP.StepsProcess

/-!
# `VmPreserved` & Epoch Zero-`.rodata` Bridges for `<std::time::SystemTime>::duration_since`

Lifts the `VerifiedLibraries.RustStd.timeMultiLib` real-code proofs (`rustc 1.98.1`
`aarch64-unknown-linux-musl` `libstd`, block `1` `<std::time::SystemTime>::duration_since` +
block `0` `Timespec::sub_timespec`) to `LibsignalBinary.Heap.SpecBudget.withVmPreserved`:

1. **Pure `MultiPlacedLib` `withVmPreserved` lifting:** All 3 blocks of `timeMultiLib` share the
   single extern `core::option::expect_failed` (the hooked panic tail of `sub_timespec` at `+236`,
   unreachable on valid `tv_nsec < 10 ^ 9` / epoch inputs, and placed outside every block's code
   range by `Placeable.externs_ok`), and satisfy `CodeBlock.patchSafe svc0Pat` and
   `CodeBlock.patchSafe msrTpidrEl0Pat`. Stripping executable permissions outside `timeMultiLib`'s
   placed blocks (`stripS`) lifts any normal-return `subroutine_ok` on `timeMultiLib` to
   `withVmPreserved` (`PoolPreserved`, `physMemAvail`, `mem.perm`, and `FdsHiFrame`).
2. **D1 — Epoch path with zero `.rodata` premise (`t2 ≤ t1`, `144` B stack):** When
   `timespecNs s2 n2 ≤ timespecNs s1 n1` (in particular on `UNIX_EPOCH` where `s1 = 0, n1 = 0,
   s2 = 0, n2 = 0`), `Timespec::sub_timespec` takes its `Ok` branch (`subTimespec_ge_block_ok`,
   `64` B stack) and never touches `.rodata.cst16`. Combining block `1`'s `80` B frame with
   `subTimespec_ge_block_ok` yields `timeDurationSinceGeSpec` (`144` B stack, zero `.rodata`) and
   discharges every epoch-path consumer contract (`durationSinceEpochAtSpec`,
   `CliExt.durationSinceEpochSpec`, `durationSinceEpochBudgetSpec`,
   `durationSinceEpochAllocSpec`, `durationSinceEpochAllocBudgetSpec`, and `keepsFs` / `inImage`
   variants) without any `.rodata` hypothesis.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceVm

open Arm64 ProofLib
open Arm64.Obj
  (CodeBlock MultiPlacedLib MultiPlacement Placement PlacedLib lookup lookupBlockSym
   msrTpidrEl0Pat svc0Pat)
open VerifiedLibraries.RustStd
  (TimePlacement memRegion20_eq_sret_slots subTimespecGeSpec
   subTimespec_ge_block_ok timeDurationSinceSpec timeDurationSinceSym timeDurationSince_block_ok
   timeDurationSince_subroutineOk timeFnAddr_eq_base timeMpl timeMultiLib timePC01 timePl00
   timePl01 timePl01_rho_subTimespec timePlacedData0 timeRodataCst16Sym timeSubTimespecLocalSym
   timespecNs)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (durationSinceEpochSpec)
open LibsignalBinary.Heap (FdsHiFrame PoolPreserved VmPreserved)
open LibsignalBinary.Heap.SpecBudget (durationSinceEpochBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs subroutine_ok_inImage)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common
  (RoDataAt SpecSimulates keepsFs_withRoData subroutine_ok_withRoData_of_sep withRoData
   withRoDataSep)
open LibsignalBinary.Proofs.HookDischarge.RustStd.TimeDurationSince
  (durationSinceBoundedAtSpec durationSinceBoundedSpec durationSinceEpochAtSpec)

/-! ## 1. Pure `MultiPlacedLib` `VmPreserved` Lifting -/

private def multiLibKeep (lib : MultiPlacedLib) (mpl : MultiPlacement) (a : BitVec 64) : Bool :=
  (List.range lib.blocks.length).any fun j => progKeep (lib.blockProgram mpl j) a

private theorem multiLibKeep_of_inBlock {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {j : Nat} (hj : j < lib.blocks.length) {a : BitVec 64}
    (hk : progKeep (lib.blockProgram mpl j) a = true) :
    multiLibKeep lib mpl a = true := by
  unfold multiLibKeep
  rw [List.any_eq_true]
  exact ⟨j, List.mem_range.mpr hj, hk⟩

private theorem strip_codeLoaded_multi {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {m : Memory} (hcl : lib.CodeLoaded mpl m) :
    lib.CodeLoaded mpl (stripExecOutside (multiLibKeep lib mpl) m) := by
  intro j hj
  have hL := hcl j hj
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  let Pj := lib.blockProgram mpl j
  have hsub : Pj.base + BitVec.ofNat 64 k - Pj.base = BitVec.ofNat 64 k := by bv_omega
  have hin : (Pj.base + BitVec.ofNat 64 k - Pj.base).toNat < Pj.code.length := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hk
  have hkp : progKeep Pj (Pj.base + BitVec.ofNat 64 k) = true := by
    unfold progKeep; exact decide_eq_true hin
  have hmk : multiLibKeep lib mpl (Pj.base + BitVec.ofNat 64 k) = true :=
    multiLibKeep_of_inBlock hj hkp
  have hp_eq : (stripExecOutside (multiLibKeep lib mpl) m).perm (Pj.base + BitVec.ofNat 64 k) =
      m.perm (Pj.base + BitVec.ofNat 64 k) := by
    rw [strip_perm, hmk]
    cases m.perm (Pj.base + BitVec.ofNat 64 k) with
    | none => rfl
    | some p => cases p; rfl
  rw [strip_read8, hp_eq, strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

private theorem externAt?_blockProgram_none_of_keep {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {i : Nat} {externs : String → Option (State → State)}
    (hpl : lib.Placeable mpl)
    (hext_sub : lib.blocks.all (fun blk =>
      (lib.blockLib i).text.externs.all (fun e => blk.externs.contains e)) = true)
    {pc : BitVec 64} (hk : multiLibKeep lib mpl pc = true) :
    (lib.blockProgram mpl i externs).externAt? pc = none := by
  unfold multiLibKeep at hk
  rw [List.any_eq_true] at hk
  obtain ⟨j, hj_mem, hkp⟩ := hk
  have hj : j < lib.blocks.length := List.mem_range.mp hj_mem
  have hin : (pc - mpl.base j).toNat < (lib.blockProgram mpl j).code.length := by
    unfold progKeep at hkp; exact of_decide_eq_true hkp
  have hbt := hpl.blocks_ok j hj
  have hplen_j : (lib.blockProgram mpl j).code.length = lib.blocks[j].code.length := by
    change ((lib.blockLib j).text.patched (lib.blockPlacement mpl j)).length = _
    rw [CodeBlock.length_patched_of_aligned _ (by rw [lib.blockLib_text hj]; exact hbt.len_aligned),
      lib.blockLib_text hj]
  rw [hplen_j] at hin
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program, MultiPlacedLib.blockPlacement,
    Program.externAt?, Program.hookAtOff?]
  simp only [ite_self, h0, Option.or_none]
  rw [List.findSome?_eq_none_iff]
  rintro ⟨e, off_e⟩ hmem
  rw [List.mem_map] at hmem
  obtain ⟨e', he_mem, heq⟩ := hmem
  have he_eq : e' = e := (Prod.mk.inj heq).1
  have hoff_eq : (lib.resolve mpl e' - mpl.base i).toNat = off_e := (Prod.mk.inj heq).2
  subst he_eq hoff_eq
  have he_in_j : e' ∈ lib.blocks[j].externs := by
    have hall_j := (List.all_eq_true.mp hext_sub) lib.blocks[j] (List.getElem_mem hj)
    have hc := (List.all_eq_true.mp hall_j) e' he_mem
    exact List.contains_iff_mem.mp hc
  have hex_ok := (hbt.externs_ok e' he_in_j).2
  dsimp only [MultiPlacedLib.blockPlacement] at hex_ok
  have hne : (lib.resolve mpl e' - mpl.base i).toNat ≠ (pc - mpl.base i).toNat := by
    intro heq_nat
    have hbv := BitVec.eq_of_toNat_eq heq_nat
    have hres_eq : lib.resolve mpl e' = pc := by
      have h1 : (lib.resolve mpl e' - mpl.base i) + mpl.base i =
          (pc - mpl.base i) + mpl.base i := congrArg (· + mpl.base i) hbv
      simpa [BitVec.sub_add_cancel] using h1
    rw [hres_eq] at hex_ok
    omega
  simp only [beq_iff_eq, hne, ↓reduceIte]

private theorem vmPreserved_of_nonSyscall_tpidr {s0 sf : State}
    (hnsp : ProofLib.NonSyscallPreserved s0 sf) (htp : sf.tpidrEl0 = s0.tpidrEl0) :
    VmPreserved s0 sf := by
  have hpool : PoolPreserved s0 sf := ⟨hnsp.2.2.2.1, hnsp.2.2.1, htp⟩
  have hfds : FdsHiFrame s0 sf := by
    intro fd _ _
    rw [hnsp.2.2.2.2.2.2]
  exact ⟨hpool, hnsp.2.2.2.2.1, fun a => congrFun hnsp.2.1 a, hfds⟩

private theorem fetch_in_multiLib_not_svc0_msr {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hpl : lib.Placeable mpl)
    (hsvc_all : lib.blocks.all (fun blk => blk.patchSafe svc0Pat) = true)
    (hmsr_all : lib.blocks.all (fun blk => blk.patchSafe msrTpidrEl0Pat) = true)
    {m0 m : Memory} (hcl0 : lib.CodeLoaded mpl m0) (hkf : m0.KeepsFrozen m)
    {pc : BitVec 64} {inst : Instr}
    (hk : multiLibKeep lib mpl pc = true)
    (hfm : Program.pureMem.fetchMem m pc = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  unfold multiLibKeep at hk
  rw [List.any_eq_true] at hk
  obtain ⟨j, hj_mem, hkp⟩ := hk
  have hj : j < lib.blocks.length := List.mem_range.mp hj_mem
  have hcl_m : (lib.blockProgram mpl j).CodeLoaded m := (hcl0 j hj).of_keepsFrozen hkf
  have hal_pc : pc.toNat % 4 = 0 := by
    unfold Program.fetchMem at hfm
    by_cases h4 : pc.toNat % 4 = 0
    · exact h4
    · simp [h4] at hfm
  let Pj := lib.blockProgram mpl j
  have hPj_al : Pj.base.toNat % 4 = 0 := hcl_m.aligned
  have hPj_nw : Pj.base.toNat + Pj.code.length ≤ 2 ^ 64 := hcl_m.no_wrap
  have hin : (pc - Pj.base).toNat < Pj.code.length := by
    unfold progKeep at hkp; exact of_decide_eq_true hkp
  have hPj_len4 : Pj.code.length % 4 = 0 := by
    have hbt := (hpl.blocks_ok j hj).len_aligned
    have hplen : ((lib.blockLib j).text.patched (lib.blockPlacement mpl j)).length =
        (lib.blockLib j).text.code.length :=
      CodeBlock.length_patched_of_aligned _ (by rw [lib.blockLib_text hj]; exact hbt)
    change ((lib.blockLib j).text.patched (lib.blockPlacement mpl j)).length % 4 = 0
    rw [hplen, lib.blockLib_text hj]
    exact hbt
  let off := (pc - Pj.base).toNat
  have hpc_eq : pc = Pj.base + BitVec.ofNat 64 off := by
    dsimp [off]; bv_omega
  have hpc_ge : Pj.base.toNat ≤ pc.toNat := by
    change (pc - Pj.base).toNat < Pj.code.length at hin
    bv_omega
  have hoff_nat : off = pc.toNat - Pj.base.toNat := by
    dsimp [off]; bv_omega
  have hoff_lt : off < Pj.code.length := hin
  have hoff4 : off % 4 = 0 := by omega
  have hoff_end : off + 4 ≤ Pj.code.length := by omega
  have hoff_end' : off + 4 ≤ (lib.blockProgram mpl j).code.length := hoff_end
  have hrw : Pj.readWordOff off = some (m.read32 pc) := by
    have hb0 := hcl_m.byte_eq off (by omega)
    have hb1 := hcl_m.byte_eq (off + 1) (by omega)
    have hb2 := hcl_m.byte_eq (off + 2) (by omega)
    have hb3 := hcl_m.byte_eq (off + 3) (by omega)
    have ha0 : pc + 0#64 = Pj.base + BitVec.ofNat 64 off := by rw [hpc_eq]; bv_omega
    have ha1 : pc + 1#64 = Pj.base + BitVec.ofNat 64 (off + 1) := by rw [hpc_eq]; bv_omega
    have ha2 : pc + 2#64 = Pj.base + BitVec.ofNat 64 (off + 2) := by rw [hpc_eq]; bv_omega
    have ha3 : pc + 3#64 = Pj.base + BitVec.ofNat 64 (off + 3) := by rw [hpc_eq]; bv_omega
    unfold Program.readWordOff
    simp only [hoff4, ne_eq, not_true_eq_false, ↓reduceIte]
    have hd0 : Pj.code.drop off =
        Pj.code[off]'(by omega) :: Pj.code[off + 1]'(by omega) ::
        Pj.code[off + 2]'(by omega) :: Pj.code[off + 3]'(by omega) :: Pj.code.drop (off + 4) := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
        List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
    rw [hd0]
    dsimp only [Memory.read32]
    rw [ha0, hb0, ha1, hb1, ha2, hb2, ha3, hb3]
  have hdec : decode (m.read32 pc) = some inst := by
    unfold Program.fetchMem at hfm
    split at hfm
    · simp at hfm
    · split at hfm
      · simp at hfm
      · split at hfm
        · simp at hfm
        · exact hfm
  have hfetch_Pj : Pj.fetch (Pj.base + BitVec.ofNat 64 off) = some inst := by
    have hf := Program.fetch_of_readWordOff (prog := Pj) (off := off) (by omega)
      (by simp [Pj, MultiPlacedLib.blockProgram, PlacedLib.program, Program.hookAtOff?]) hrw
    rwa [hdec] at hf
  have hps_svc : (lib.blockLib j).text.patchSafe svc0Pat = true := by
    rw [lib.blockLib_text hj]
    exact (List.all_eq_true.mp hsvc_all) lib.blocks[j] (List.getElem_mem hj)
  have hps_msr : (lib.blockLib j).text.patchSafe msrTpidrEl0Pat = true := by
    rw [lib.blockLib_text hj]
    exact (List.all_eq_true.mp hmsr_all) lib.blocks[j] (List.getElem_mem hj)
  have hall_svc := PlacedLib.program_noSvc0_of_patchSafe hps_svc (lib.blockPlacement mpl j)
  have hall_msr := PlacedLib.program_noMsrTpidrEl0_of_patchSafe hps_msr (lib.blockPlacement mpl j)
  exact ⟨by
      have hi := Program.fetch_of_allInstrs hall_svc _ _ hfetch_Pj
      simpa using hi,
    by
      have hi := Program.fetch_of_allInstrs hall_msr _ _ hfetch_Pj
      simpa using hi⟩

private theorem steps_pureMem_lift_stripS_vm (keep : BitVec 64 → Bool) {P : Program}
    {m0 : Memory}
    (hsvc_P : P.svc = Syscall.standard)
    (hext_P : ∀ pc : BitVec 64, keep pc = true → P.externAt? pc = none)
    (h_pure : ∀ (m : Memory) (pc : BitVec 64) (inst : Instr),
      m0.KeepsFrozen m →
      keep pc = true →
      Program.pureMem.fetchMem m pc = some inst →
      inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false) :
    ∀ {s0 s' sf' : State},
      s' = stripS keep s0 →
      m0.KeepsFrozen s0.mem →
      Steps Program.pureMem s' sf' →
      sf'.status = .Running →
      ∃ sf : State,
        sf' = stripS keep sf ∧
        Steps P s0 sf ∧
        ProofLib.NonSyscallPreserved s0 sf ∧
        sf.tpidrEl0 = s0.tpidrEl0 := by
  intro s0 s' sf' hs' hkf hsteps hrun_f
  induction hsteps generalizing s0 with
  | refl _ =>
    subst hs'
    exact ⟨s0, rfl, Steps.refl s0, ProofLib.NonSyscallPreserved.refl s0, rfl⟩
  | @step s1' s2' sf' hstep hrest ih =>
    subst hs'
    have hrun2' : s2'.status = .Running := by
      cases hrest with
      | refl _ => exact hrun_f
      | step hs _ => exact hs.status_running
    cases hstep with
    | halt_unmapped _ _ _ => simp at hrun2'
    | extern _ h_ext _ _ => nomatch h_ext
    | extern_fault _ h_ext _ => nomatch h_ext
    | exec hrun1' hfetch' =>
      rename_i inst
      have hrun1 : s0.status = .Running := by cases s0; exact hrun1'
      have hpc_eq : (stripS keep s0).pc = s0.pc := by cases s0; rfl
      have hmem_eq : (stripS keep s0).mem = stripExecOutside keep s0.mem := by cases s0; rfl
      rw [hpc_eq, hmem_eq] at hfetch'
      unfold Program.fetchMem at hfetch'
      by_cases hce' : (stripExecOutside keep s0.mem).canExec s0.pc 4 = true
      · have hr32 : (stripExecOutside keep s0.mem).read32 s0.pc = s0.mem.read32 s0.pc := by
          simp [Memory.read32, strip_read8]
        simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr32] at hfetch'
        have hx4 :
            ((stripExecOutside keep s0.mem).perm s0.pc).x = true ∧
            ((stripExecOutside keep s0.mem).perm (s0.pc + 1#64)).x = true ∧
            ((stripExecOutside keep s0.mem).perm (s0.pc + 2#64)).x = true ∧
            ((stripExecOutside keep s0.mem).perm (s0.pc + 3#64)).x = true := by
          simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
        obtain ⟨hx0, hk0⟩ := strip_perm_x_imp hx4.1
        obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
        obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
        obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
        have hce : s0.mem.canExec s0.pc 4 = true := by
          simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
        have hpure_ext : Program.pureMem.externAt? s0.pc = none := rfl
        have hfetch_pm : Program.pureMem.fetchMem s0.mem s0.pc = some inst := by
          unfold Program.fetchMem
          rw [hpure_ext] at hfetch' ⊢
          simpa [hce] using hfetch'
        have hfetch_P : P.fetchMem s0.mem s0.pc = some inst := by
          unfold Program.fetchMem
          rw [hext_P s0.pc hk0]
          unfold Program.fetchMem at hfetch_pm
          rw [hpure_ext] at hfetch_pm
          exact hfetch_pm
        obtain ⟨hns, hmsr⟩ := h_pure s0.mem s0.pc inst hkf hk0 hfetch_pm
        rw [evalInst_pureMem] at hrest hrun2' ih
        have heval_P : P.evalInst inst s0 = execInst inst s0 :=
          evalInst_eq_execInst_of_not_isSvc0 hns s0
        have hstep_s0 : Step P s0 (execInst inst s0) :=
          heval_P ▸ Step.exec hrun1 hfetch_P
        have hstep_pm : Step Program.pureMem s0 (execInst inst s0) :=
          evalInst_pureMem inst s0 ▸ Step.exec hrun1 hfetch_pm
        have _ := hsvc_P
        have hcomm : execInst inst (stripS keep s0) = stripS keep (execInst inst s0) :=
          execInst_stripS hns keep s0
        have hnsp1 : ProofLib.NonSyscallPreserved s0 (execInst inst s0) :=
          ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hns s0
        have htp1 : (execInst inst s0).tpidrEl0 = s0.tpidrEl0 :=
          execInst_tpidrEl0_of_not_isMsrTpidrEl0 hmsr s0
        have hkf2 : m0.KeepsFrozen (execInst inst s0).mem := hkf.trans hstep_pm.keepsFrozen
        obtain ⟨sf, hsf_eq, hsteps_rest, hnsp_rest, htp_rest⟩ := ih hcomm hkf2 hrun_f
        exact ⟨sf, hsf_eq, Steps.step hstep_s0 hsteps_rest, hnsp1.trans hnsp_rest,
          htp_rest.trans htp1⟩
      · simp [hce'] at hfetch'

/-- Lift `subroutine_ok` proved on hook-free `lib.blockProgram mpl i` to `withVmPreserved` on
    `lib.blockProgram mpl i externs` for any external hook table `externs`, whenever all blocks of
    `lib` exclude `SVC #0` and `MSR TPIDR_EL0` (`patchSafe`) and declare block `i`'s externs. -/
theorem multiBlock_subroutine_ok_withVmPreserved {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {i : Nat} {entry : BitVec 64} {spec : Spec α}
    {externs : String → Option (State → State)}
    (hi : i < lib.blocks.length)
    (hpl : lib.Placeable mpl)
    (hext_sub : lib.blocks.all (fun blk =>
      (lib.blockLib i).text.externs.all (fun e => blk.externs.contains e)) = true)
    (hsvc_all : lib.blocks.all (fun blk => blk.patchSafe svc0Pat) = true)
    (hmsr_all : lib.blocks.all (fun blk => blk.patchSafe msrTpidrEl0Pat) = true)
    (hsub : subroutine_ok (lib.blockProgram mpl i) entry (lib.withCodeLoaded mpl spec))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; simp [State.setMem])
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; simp [State.setMem]) :
    subroutine_ok (lib.blockProgram mpl i externs) entry
      (lib.withCodeLoaded mpl (withVmPreserved spec)) := by
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro x R s0 hpc hrun hpre hsp _hLi
  dsimp only [MultiPlacedLib.withCodeLoaded, withVmPreserved] at hpre
  rw [sepConj_comm (spec.pre x s0) ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_spec⟩ := hpre
  let keep := multiLibKeep lib mpl
  obtain ⟨R_view, hpre_strip, hunstrip⟩ := strip_frame keep hpre_spec
  let s0' := stripS keep s0
  have hcl_strip : lib.CodeLoaded mpl s0'.mem := by
    have hm : s0'.mem = stripExecOutside keep s0.mem := by cases s0; rfl
    rw [hm]; exact strip_codeLoaded_multi hcl0
  have hpre' : s0'.mem ⊨ (lib.withCodeLoaded mpl spec).pre x s0' ∗ R_view := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl_strip]
    have hs0_eq : s0' = s0.setMem (stripExecOutside keep s0.mem) := by cases s0; rfl
    rw [hs0_eq, h_pre_mem]
    simpa [State.setMem] using hpre_strip
  have hLi_strip : (lib.blockProgram mpl i).CodeLoaded s0'.mem :=
    hcl_strip i hi
  obtain ⟨sf', hsteps_blk, hout'⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hsub x R_view s0' (by cases s0; exact hpc) (by cases s0; exact hrun)
      hpre' (by cases s0; exact hsp))
    hLi_strip
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · have h0 : ∀ L : List (String × Nat),
        L.findSome? (fun _ => (none : Option (State → State))) = none := by
      intro L; induction L <;> simp [*]
    have hsteps_pm' : Steps Program.pureMem s0' sf' :=
      Steps.of_sameHooks (P := Program.pureMem) (Q := lib.blockProgram mpl i)
        (by
          intro pc
          have hpure_ext : Program.pureMem.externAt? pc = none := rfl
          rw [hpure_ext]
          dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program,
            Program.externAt?, Program.hookAtOff?]
          simp only [ite_self, h0, Option.or_none]) rfl hsteps_blk
    obtain ⟨sf, hsf_eq, hsteps_P, hnsp, htp⟩ :=
      steps_pureMem_lift_stripS_vm keep (P := lib.blockProgram mpl i externs) rfl
        (fun pc hk => externAt?_blockProgram_none_of_keep hpl hext_sub hk)
        (fun m pc inst hkf hk hfm =>
          fetch_in_multiLib_not_svc0_msr hpl hsvc_all hmsr_all hcl0 hkf hk hfm)
        rfl (Memory.KeepsFrozen.refl s0.mem) hsteps_pm' hret'.2.2
    have hvm : VmPreserved s0 sf := vmPreserved_of_nonSyscall_tpidr hnsp htp
    refine ⟨sf, hsteps_P, Or.inl ⟨?_, ?_, ?_⟩⟩
    · rcases hret' with ⟨hr_pc, hr_sp, hr_st⟩
      rw [hsf_eq] at hr_pc hr_sp hr_st
      exact ⟨by cases s0; cases sf; exact hr_pc,
        by cases s0; cases sf; exact hr_sp,
        by cases sf; exact hr_st⟩
    · rw [hsf_eq] at hcc'
      rcases hcc' with ⟨hsp_cc, hcs⟩
      exact ⟨by cases s0; cases sf; exact hsp_cc, by cases s0; cases sf; exact hcs⟩
    · rw [hsf_eq] at hpost'
      dsimp only [MultiPlacedLib.withCodeLoaded] at hpost'
      have hs0_set : s0' = s0.setMem (stripExecOutside keep s0.mem) := by cases s0; rfl
      have hsf_set : stripS keep sf = sf.setMem (stripExecOutside keep sf.mem) := by cases sf; rfl
      rw [hs0_set, hsf_set, h_post_mem] at hpost'
      have hpost_sf : sf.mem ⊨ spec.post x s0 sf ∗ R :=
        hunstrip (fun a => congrFun hnsp.2.1 a) (by simpa [State.setMem] using hpost')
      dsimp only [MultiPlacedLib.withCodeLoaded, withVmPreserved]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hvm, hpost_sf⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded] at hp
    rw [hpan] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [MultiPlacedLib.withCodeLoaded] at he
    rw [hex] at he; exact False.elim (not_satisfies_false_sepConj he)
  · dsimp only [MultiPlacedLib.withCodeLoaded] at ho
    rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

private theorem timeMultiLib_patchSafe_svc0 :
    timeMultiLib.blocks.all (fun blk => blk.patchSafe svc0Pat) = true := by decide

private theorem timeMultiLib_patchSafe_msrTpidrEl0 :
    timeMultiLib.blocks.all (fun blk => blk.patchSafe msrTpidrEl0Pat) = true := by decide

private theorem timeMultiLib_block1_externs_shared :
    timeMultiLib.blocks.all (fun blk =>
      (timeMultiLib.blockLib 1).text.externs.all (fun e => blk.externs.contains e)) = true := by
  decide

/-- Lift `SpecSimulates spec₁ spec₂` to `withVmPreserved` when both specs have `False` abnormal exits. -/
theorem specSimulates_lift_withVmPreserved {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂)
    (hpan₁ : spec₁.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex₁ : spec₁.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom₁ : spec₁.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (hpan₂ : spec₂.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex₂ : spec₂.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom₂ : spec₂.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    SpecSimulates (withVmPreserved spec₁) (withVmPreserved spec₂) := by
  intro y R s0 hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  refine ⟨x, R₁, hpre₁, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · dsimp only [withVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hvm, hpost₁⟩ := hpost
    rcases hm sf (Or.inl ⟨hret, hcc, hpost₁⟩) with ⟨_, _, hpost₂⟩ | ⟨_, hp⟩ | ⟨c, _, he⟩ | ⟨_, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withVmPreserved]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hvm, hpost₂⟩
    · rw [hpan₂] at hp; exact False.elim (not_satisfies_false_sepConj hp)
    · rw [hex₂] at he; exact False.elim (not_satisfies_false_sepConj he)
    · rw [hoom₂] at ho; exact False.elim (not_satisfies_false_sepConj ho)
  · dsimp only [withVmPreserved] at hp
    rw [hpan₁] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [withVmPreserved] at he
    rw [hex₁] at he; exact False.elim (not_satisfies_false_sepConj he)
  · dsimp only [withVmPreserved] at ho
    rw [hoom₁] at ho; exact False.elim (not_satisfies_false_sepConj ho)

/-- Commute `withVmPreserved (keepsFs spec)` to `keepsFs (withVmPreserved spec)`. -/
theorem specSimulates_keepsFs_withVmPreserved {α : Type} {spec : Spec α} :
    SpecSimulates (withVmPreserved (keepsFs spec)) (keepsFs (withVmPreserved spec)) := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hout_abn
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, keepsFs] at hpost ⊢
    rw [sepConj_left_comm ⌜VmPreserved s0 sf⌝ ⌜sf.fs = s0.fs⌝] at hpost
    exact hpost
  · exact Or.inr hout_abn

/-- Drop `withVmPreserved` along `SpecSimulates`. -/
theorem specSimulates_drop_withVmPreserved {α : Type} {spec : Spec α} :
    SpecSimulates (withVmPreserved spec) spec := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hout_abn
  · dsimp only [withVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inl ⟨hret, hcc, hpost.2⟩
  · exact Or.inr hout_abn

/-! ## 2. D1 — Epoch Path (`t2 ≤ t1`, Zero `.rodata`, `144` B Stack, `withVmPreserved`) -/

/-- Contract for `<std::time::SystemTime>::duration_since` on the `t2 ≤ t1` (`Ok`) path (`144` B
    stack = `80` B in `duration_since` + `64` B in `Timespec::sub_timespec`, zero `.rodata` reads). -/
@[expose] def timeDurationSinceGeSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 32 × BitVec 64 × BitVec 64 ×
          BitVec 64 × BitVec 32 × BitVec 32) where
  pre := fun (p, s2, n2, ret, sp, s1, n1, b20) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = s2 ∧ s0.readReg32 .x2 = n2 ∧
      s0.readReg64 .x8 = ret ∧ s0.sp = sp ∧
      n1.toNat < 10 ^ 9 ∧ n2.toNat < 10 ^ 9 ∧
      timespecNs s2 n2 ≤ timespecNs s1 n1⌝ ∗
    (p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗
    memRegion ret 20 ∗ ((ret + 20#64) ↦₃₂ b20) ∗
    stackFrameAt sp 144
  post := fun (p, s2, n2, ret, sp, s1, n1, b20) s0 sf =>
    let d : Nat := (timespecNs s1 n1 - timespecNs s2 n2).natAbs
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
    (p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗
    (ret ↦₆₄ 0#64) ∗
    ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
    ((ret + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)) ∗
    ((ret + 20#64) ↦₃₂ b20) ∗
    stackFrameAt sp 144
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem frame144_entails (sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    (stackAt (sp - 80#64) 64 ∗
      (((sp - 80#64) ↦₆₄ w0) ∗ ((sp - 72#64) ↦₆₄ w1) ∗ ((sp - 64#64) ↦₆₄ w2) ∗
        ((sp - 56#64) ↦₆₄ w3) ∗ ((sp - 48#64) ↦₆₄ w4) ∗ ((sp - 40#64) ↦₆₄ w5) ∗
        ((sp - 32#64) ↦₆₄ w6) ∗ ((sp - 24#64) ↦₆₄ w7) ∗ ((sp - 16#64) ↦₆₄ w8) ∗
        ((sp - 8#64) ↦₆₄ w9))) ⊢ stackFrameAt sp 144 := by
  rw [← stackAt_eq_stackFrameAt sp 144, stackAt_frame sp 144 10 (by decide)]
  refine sepConj_mono_right <|
    cells_sub_succ_entails 80 10 <|
    cells_sub_succ_entails 72 9 <|
    cells_sub_succ_entails 64 8 <|
    cells_sub_succ_entails 56 7 <|
    cells_sub_succ_entails 48 6 <|
    cells_sub_succ_entails 40 5 <|
    cells_sub_succ_entails 32 4 <|
    cells_sub_succ_entails 24 3 <|
    cells_sub_succ_entails 16 2 ?_
  simpa [cells_zero, sepConj_emp] using
    cells_sub_succ_entails (sp := sp) 8 1 (v := w9) (Entails.refl emp)

private theorem entails_subst_frame_local {A B : SepProp} (F : SepProp) {P Q : SepProp}
    (hab : A ⊢ B) (h1 : P ⊢ A ∗ F) (h2 : B ∗ F ⊢ Q) : P ⊢ Q :=
  Arm64.Entails.trans h1 (Arm64.Entails.trans (sepConj_mono_left hab) h2)

private theorem subroutine_ok_intro_withCodeLoaded {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (lib : MultiPlacedLib) (mpl : MultiPlacement)
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (lib.withCodeLoaded mpl spec) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _hL
  dsimp only [MultiPlacedLib.withCodeLoaded] at hpre
  rw [sepConj_comm (spec.pre x s0) ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp (fun _ hout => hout)

section
arm64_proof_prelude

set_option maxHeartbeats 1600000 in
/-- Block-1 proof of `<std::time::SystemTime>::duration_since` on the `t2 ≤ t1` path (`144` B stack,
    zero `.rodata`). -/
theorem timeDurationSince_ge_block_ok [TimePlacement]
    (externs : String → Option (State → State) := fun _ => none) :
    subroutine_ok (timeMultiLib.blockProgram timeMpl 1 externs)
      (timeMultiLib.fnAddr timeMpl timeDurationSinceSym)
      (timeMultiLib.withCodeLoaded timeMpl timeDurationSinceGeSpec) := by
  rw [timeFnAddr_eq_base 1 timeDurationSinceSym (by decide) (by decide)]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, s2, n2, ret, sp, s1, n1, b20⟩ R s0 hpc hrun hpre hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, timeDurationSinceGeSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜timeMultiLib.CodeLoaded timeMpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx8, hsp_eq, hn1, hn2, hle⟩, hmem⟩
  subst hsp_eq
  refine ⟨_, hmem, ?_⟩
  apply VerifiedLibraries.RustStd.seqCodeLoaded hcl (mid := timePl00.base)
  change SepWP (timePC01.rebase timePl01.base externs) timePl00.base s0 _ _ _
  have hpc0 : s0.pc = timePl01.base := hpc; clear hpc; rename_i hpc
  have hx2_tr : BitVec.truncate 32 (s0.readReg64 (.gpr 2#5)) = n2 := hx2
  wp_conv_pre =>
    rw [← stackAt_eq_stackFrameAt s0.sp 144, stackAt_frame s0.sp 144 10 (by decide)]
    simp (disch := decide) only [Nat.reduceMul, Nat.reduceSub, ProofLib.cells_sub_succ,
      ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 =>
    SepWP.exists_elim fun st4 => SepWP.exists_elim fun st5 =>
    SepWP.exists_elim fun st6 => SepWP.exists_elim fun st7 =>
    SepWP.exists_elim fun st8 => SepWP.exists_elim fun st9 => ?_
  wp_conv_pre =>
    rw [memRegion20_eq_sret_slots ret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun ow2 => SepWP.exists_elim fun ow1 =>
    SepWP.exists_elim fun ow0 => ?_
  wp_conv_pre =>
    rw [pointsTo64_split32 (s0.sp - 72#64) st1,
      show s0.sp - 72#64 + 4#64 = s0.sp - 68#64 by bv_arith,
      pointsTo64_split32 (s0.sp - 48#64) st4,
      show s0.sp - 48#64 + 4#64 = s0.sp - 44#64 by bv_arith]
  wp_sym_steps
  refine SepWP.done
    (by
      dsimp only [State.setMem, State.setPC]
      rw [timePl01_rho_subTimespec]
      bv_omega)
    (by simpa [arm64_norm] using hrun)
    fun hcl_call => ?_
  have hsub0 := subroutine_ok_intro_withCodeLoaded timeMultiLib timeMpl
    (subTimespec_ge_block_ok (externs := externs))
  have hsub := MultiPlacedLib.subroutine_ok_of_block_hooks
    (P := timeMultiLib.blockProgram timeMpl 1 externs) (j := 0) (by decide)
    hsub0
    (timeMultiLib.externAt?_blockProgram_eq_of_externs_eq rfl) rfl
  rw [timeFnAddr_eq_base 0 timeSubTimespecLocalSym (by decide) (by decide)] at hsub
  change subroutine_ok (timePC01.rebase timePl01.base externs) timePl00.base _ at hsub
  change SepWP (timePC01.rebase timePl01.base externs) (s0.readReg64 .lr) _ _ _ _
  refine SepWP.call_subroutine_frame hsub
    (x := (s0.sp - 64#64, p, s0.sp - 80#64, s1, n1, s2, n2, st2, st3, st4.extractLsb' 0 32))
    (F := ((ret + 20#64) ↦₃₂ b20) ∗
          ((s0.sp - 68#64) ↦₃₂ st1.extractLsb' 32 32) ∗
          ((s0.sp - 44#64) ↦₃₂ st4.extractLsb' 32 32) ∗
          ((s0.sp - 40#64) ↦₆₄ st5) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ st9) ∗
          (ret ↦₆₄ ow0) ∗ ((ret + 8#64) ↦₆₄ ow1) ∗ ((ret + 16#64) ↦₃₂ ow2))
    (by
      dsimp only [State.setMem, State.setPC]
      rw [timePl01_rho_subTimespec]
      bv_omega)
    (by simpa [arm64_norm] using hrun)
    (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp)
    (by simp only [wp_norm, arm64_norm]; rfl)
    (fun R' hm' => ?_)
    (by
      rintro R' sf - hp
      dsimp only [MultiPlacedLib.withCodeLoaded, subTimespecGeSpec] at hp
      rw [satisfies_pure_sepConj] at hp
      exact hp.1)
    (by
      rintro R' code sf - he
      dsimp only [MultiPlacedLib.withCodeLoaded, subTimespecGeSpec] at he
      rw [satisfies_pure_sepConj] at he
      exact he.1)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
  · refine Satisfies.mono ?_ hm'
    dsimp only [MultiPlacedLib.withCodeLoaded, subTimespecGeSpec]
    rw [sepConj_comm _ ⌜timeMultiLib.CodeLoaded timeMpl _⌝,
      pure_sepConj_of_true hcl_call,
      pure_sepConj_of_true ⟨by simp [wp_norm, arm64_norm],
        by simp [wp_norm, arm64_norm],
        by simp [wp_norm, arm64_norm],
        hn1, hn2, hle⟩]
    simp only [wp_norm, arm64_norm]
    sep_entail
  · dsimp only [MultiPlacedLib.withCodeLoaded, subTimespecGeSpec]
    wp_conv_pre =>
      simp only [sepConj_assoc]
    refine SepWP.pure_elim ?_
    rintro ⟨⟨htr1, _hsig1⟩, hfs1⟩
    replace htr1 : sf1.trace = s0.trace := by simpa [wp_norm, arm64_norm] using htr1
    replace hfs1 : sf1.fs = s0.fs := by simpa [wp_norm, arm64_norm] using hfs1
    have hsp1_eq : sf1.sp = s0.sp - 80#64 := by simpa [wp_norm, arm64_norm] using hsp1
    have hsp1_al : sf1.spAligned = true := by
      simpa only [State.spAligned, hsp1_eq, wp_norm, arm64_norm] using hsp
    rw [CalleeSavedPreserved.iff_regs] at hcs1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, _hfp_1, hvregs_1⟩
    have hx19_ret : sf1.readReg64 (.gpr 19#5) = ret := by
      simpa [wp_norm, arm64_norm, hx8] using hx19_1
    wp_conv_pre =>
      simp only [State.setMem, State.setPC, wp_norm, arm64_norm]
    wp_sym_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) ?_
    refine ⟨?_,
      by simp only [wp_norm, arm64_norm],
      by
        rw [CalleeSavedPreserved.iff_regs]
        refine ⟨by simp [wp_norm, arm64_norm],
          by simpa [wp_norm, arm64_norm] using hx20_1,
          by simpa [wp_norm, arm64_norm] using hx21_1,
          by simpa [wp_norm, arm64_norm] using hx22_1,
          by simpa [wp_norm, arm64_norm] using hx23_1,
          by simpa [wp_norm, arm64_norm] using hx24_1,
          by simpa [wp_norm, arm64_norm] using hx25_1,
          by simpa [wp_norm, arm64_norm] using hx26_1,
          by simpa [wp_norm, arm64_norm] using hx27_1,
          by simpa [wp_norm, arm64_norm] using hx28_1,
          by simp [wp_norm, arm64_norm],
          by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hvregs_1⟩⟩
    intro hm_f
    refine Satisfies.mono ?_ hm_f
    let d := (timespecNs s1 n1 - timespecNs s2 n2).natAbs
    rw [pure_sepConj_of_true ⟨by simpa [wp_norm, arm64_norm] using htr1,
      by simpa [wp_norm, arm64_norm] using hfs1⟩]
    have hpair1 := pointsTo32_pair (s0.sp - 72#64) n2 (st1.extractLsb' 32 32)
    rw [show s0.sp - 72#64 + 4#64 = s0.sp - 68#64 by bv_arith] at hpair1
    have hpair4 := pointsTo32_pair (s0.sp - 48#64) (BitVec.ofNat 32 (d % 10 ^ 9))
      (st4.extractLsb' 32 32)
    rw [show s0.sp - 48#64 + 4#64 = s0.sp - 44#64 by bv_arith] at hpair4
    have hstk := frame144_entails s0.sp s2 (st1.extractLsb' 32 32 ++ n2)
      0#64 (BitVec.ofNat 64 (d / 10 ^ 9))
      (st4.extractLsb' 32 32 ++ BitVec.ofNat 32 (d % 10 ^ 9)) st5
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 19#5)) st9
    rw [← hpair1, ← hpair4] at hstk
    exact entails_subst_frame_local
      ((p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗ ((ret + 20#64) ↦₃₂ b20) ∗
        (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
        ((ret + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)) ∗ R)
      hstk (by sep_entail) (by sep_entail)

end

/-- Layout-generic `MultiPlacedLib.subroutineOk` for `<std::time::SystemTime>::duration_since` on
    the `t2 ≤ t1` path (`144` B stack, zero `.rodata`). -/
theorem timeDurationSince_ge_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym (fun _ => timeDurationSinceGeSpec) externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    @timeDurationSince_ge_block_ok ⟨mpl, hpl⟩ externs⟩

/-- `withVmPreserved` lift of `timeDurationSince_ge_subroutineOk` (`144` B stack, zero `.rodata`). -/
theorem timeDurationSince_ge_vm_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => withVmPreserved timeDurationSinceGeSpec) externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    multiBlock_subroutine_ok_withVmPreserved (lib := timeMultiLib) (mpl := mpl) (i := 1)
      (by decide) hpl timeMultiLib_block1_externs_shared
      timeMultiLib_patchSafe_svc0 timeMultiLib_patchSafe_msrTpidrEl0
      (@timeDurationSince_ge_block_ok ⟨mpl, hpl⟩ (fun _ => none))
      (h_pre_mem := by rintro ⟨_, _, _, _, _, _, _, _⟩ s _; cases s; rfl)
      (h_post_mem := by rintro ⟨_, _, _, _, _, _, _, _⟩ s0 sf _ _; cases s0; cases sf; rfl)⟩

/-- `withVmPreserved` lift of `timeDurationSince_subroutineOk` (`208` B stack, bounded path). -/
theorem timeDurationSince_vm_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withVmPreserved (timeDurationSinceSpec (mpl.ρ timeRodataCst16Sym))) externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    multiBlock_subroutine_ok_withVmPreserved (lib := timeMultiLib) (mpl := mpl) (i := 1)
      (by decide) hpl timeMultiLib_block1_externs_shared
      timeMultiLib_patchSafe_svc0 timeMultiLib_patchSafe_msrTpidrEl0
      (@timeDurationSince_block_ok ⟨mpl, hpl⟩ (fun _ => none))
      (h_pre_mem := by rintro ⟨_, _, _, _, _, _, _, _⟩ s _; cases s; rfl)
      (h_post_mem := by rintro ⟨_, _, _, _, _, _, _, _⟩ s0 sf _ _; cases s0; cases sf; rfl)⟩

/-! ## 3. D1 — Epoch Consumer Spec Bridges (`0` `.rodata` Premises) -/

/-- Mirror of `CryptoVerification.SignalSession.Cli.Slots.durationSinceEpochAllocSpec`
    (`rfl`-identical at `allocHookStack = 4096`). -/
@[expose] def durationSinceEpochAllocSpec : Spec (BitVec 64 × BitVec 64) :=
  durationSinceEpochAtSpec allocHookStack

/-- Mirror of `SetUnackEpochPlacedBudget.durationSinceEpochAllocBudgetSpec`
    (`rfl`-identical: `withVmPreserved durationSinceEpochAllocSpec`). -/
@[expose] def durationSinceEpochAllocBudgetSpec : Spec (BitVec 64 × BitVec 64) :=
  withVmPreserved durationSinceEpochAllocSpec

private theorem systemTime_entails_memRegion16_local (p s1 : BitVec 64) (n1 : BitVec 32) :
    ((p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗ memRegion (p + 12#64) 4) ⊢ memRegion p 16 := by
  rw [memRegion_split3_ord p 16 8 4 (by decide) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion p s1)
    (sepConj_mono (pointsTo32_entails_memRegion (p + 8#64) n1) (Entails.refl _))

private theorem pair32_at16_entails_exists64_local (ret : BitVec 64) (r16 b20 : BitVec 32) :
    (((ret + 16#64) ↦₃₂ r16) ∗ ((ret + 20#64) ↦₃₂ b20)) ⊢
      ∃∗ w2 : BitVec 64, (ret + 16#64) ↦₆₄ w2 := by
  rw [← memRegion_eight (ret + 16#64), memRegion_split (ret + 16#64) 4 4 (by decide)]
  have hoff : (ret + 16#64) + 4#64 = ret + 20#64 := by rw [BitVec.add_assoc]; rfl
  rw [hoff]
  exact sepConj_mono (pointsTo32_entails_memRegion (ret + 16#64) r16)
    (pointsTo32_entails_memRegion (ret + 20#64) b20)

/-- Zero-`.rodata` forward simulation from `timeDurationSinceGeSpec` (`144` B stack) to
    `keepsFs (durationSinceEpochAtSpec hookStack)` whenever `144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64`. -/
theorem timeDurationSinceGe_simulates_epoch_keepsFs {hookStack : Nat}
    (hstk : 144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    SpecSimulates timeDurationSinceGeSpec (keepsFs (durationSinceEpochAtSpec hookStack)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨p, ret⟩ R s0 hpre
  dsimp only [keepsFs, durationSinceEpochAtSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hx1, hx2⟩, hpre⟩ := hpre
  rw [memRegion_split ret 20 4 (by decide), memRegion_four (ret + 20#64),
    stackAt_shrink s0.sp hookStack 144 hstk.1 hstk.2,
    stackAt_eq_stackFrameAt s0.sp 144 (by decide)] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨b20, hpre⟩ := hpre
  have hx2_32 : s0.readReg32 .x2 = 0#32 := by
    have hsw : s0.readReg32 .x2 = (s0.readReg64 .x2).setWidth 32 := by
      simp [State.readReg32, State.readReg64]
    exact hsw.trans hx2
  refine ⟨(p, 0#64, 0#32, ret, s0.sp, 0#64, 0#32, b20),
    memRegion (p + 12#64) 4 ∗ memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 144) ∗ R,
    ?_, ?_⟩
  · dsimp only [timeDurationSinceGeSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_32, hx8, rfl, by decide, by decide, by decide⟩,
      Satisfies.mono (by sep_entail) hpre⟩
  · intro sf _hret _hcc hpost
    dsimp only [timeDurationSinceGeSpec] at hpost
    have hdiv :
        BitVec.ofNat 64
          (((timespecNs 0#64 0#32 - timespecNs 0#64 0#32).natAbs) / 10 ^ 9) = 0#64 := by decide
    have hmod :
        BitVec.ofNat 32
          (((timespecNs 0#64 0#32 - timespecNs 0#64 0#32).natAbs) % 10 ^ 9) = 0#32 := by decide
    rw [hdiv, hmod, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨htr, hfs⟩, hpost⟩ := hpost
    have hp16 := systemTime_entails_memRegion16_local p 0#64 0#32
    have hw2 := pair32_at16_entails_exists64_local ret 0#32 b20
    have hreord :
        sf.mem ⊨ ((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₃₂ 0#32) ∗ memRegion (p + 12#64) 4) ∗
          (((ret + 16#64) ↦₃₂ 0#32) ∗ ((ret + 20#64) ↦₃₂ b20)) ∗
          (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 144) ∗
          stackFrameAt s0.sp 144 ∗ R :=
      Satisfies.mono (by sep_entail) hpost
    have hstep := Satisfies.mono
      (sepConj_mono hp16 (sepConj_mono hw2 (Entails.refl _))) hreord
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hstep
    obtain ⟨w2, hpost1⟩ := hstep
    dsimp only [keepsFs, durationSinceEpochAtSpec]
    rw [stackAt_shrink s0.sp hookStack 144 hstk.1 hstk.2,
      stackAt_eq_stackFrameAt s0.sp 144 (by decide)]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨w2, 0#64, Satisfies.mono (by sep_entail) hpost1⟩

/-- `SpecSimulates` from `withVmPreserved timeDurationSinceGeSpec` to
    `keepsFs (withVmPreserved (durationSinceEpochAtSpec hookStack))` (`144 ≤ hookStack`). -/
theorem timeDurationSinceGe_simulates_epoch_vm_keepsFs {hookStack : Nat}
    (hstk : 144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    SpecSimulates (withVmPreserved timeDurationSinceGeSpec)
      (keepsFs (withVmPreserved (durationSinceEpochAtSpec hookStack))) :=
  SpecSimulates.trans
    (specSimulates_lift_withVmPreserved (timeDurationSinceGe_simulates_epoch_keepsFs hstk))
    specSimulates_keepsFs_withVmPreserved

/-- Spec-level `subroutine_ok` bridge to `keepsFs (withVmPreserved (durationSinceEpochAtSpec hookStack))`
    with zero `.rodata` hypotheses. -/
theorem timeDurationSinceGe_epochAtSpec_vm_keepsFs_ok {prog : Program} {entry : BitVec 64}
    {hookStack : Nat} (hstk : 144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (withVmPreserved timeDurationSinceGeSpec)) :
    subroutine_ok prog entry
      (keepsFs (withVmPreserved (durationSinceEpochAtSpec hookStack))) :=
  (timeDurationSinceGe_simulates_epoch_vm_keepsFs hstk).subroutine_ok h

/-- Spec-level `subroutine_ok` bridge to `withVmPreserved (durationSinceEpochAtSpec hookStack)`. -/
theorem timeDurationSinceGe_epochAtSpec_vm_ok {prog : Program} {entry : BitVec 64}
    {hookStack : Nat} (hstk : 144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (withVmPreserved timeDurationSinceGeSpec)) :
    subroutine_ok prog entry (withVmPreserved (durationSinceEpochAtSpec hookStack)) :=
  ((timeDurationSinceGe_simulates_epoch_vm_keepsFs hstk).trans SpecSimulates.drop_keepsFs).subroutine_ok h

/-- Real-code `MultiPlacedLib.subroutineOk` for `keepsFs (withVmPreserved (durationSinceEpochAtSpec hookStack))`
    (`144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64`, zero `.rodata` hypotheses). -/
theorem timeDurationSince_epochAtSpec_vm_keepsFs_subroutineOk {hookStack : Nat}
    (hstk : 144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => keepsFs (withVmPreserved (durationSinceEpochAtSpec hookStack))) externs :=
  SpecSimulates.multiSubroutineOk
    (fun _ => timeDurationSinceGe_simulates_epoch_vm_keepsFs hstk)
    (timeDurationSince_ge_vm_subroutineOk externs)

/-- Real-code `MultiPlacedLib.subroutineOk` for `withVmPreserved (durationSinceEpochAtSpec hookStack)`
    (`144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64`, zero `.rodata` hypotheses). -/
theorem timeDurationSince_epochAtSpec_vm_subroutineOk {hookStack : Nat}
    (hstk : 144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => withVmPreserved (durationSinceEpochAtSpec hookStack)) externs :=
  SpecSimulates.multiSubroutineOk
    (fun _ => (timeDurationSinceGe_simulates_epoch_vm_keepsFs hstk).trans SpecSimulates.drop_keepsFs)
    (timeDurationSince_ge_vm_subroutineOk externs)

/-- Real-code `MultiPlacedLib.subroutineOk` for `keepsFs (durationSinceEpochAtSpec hookStack)`
    (`144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64`, zero `.rodata` hypotheses). -/
theorem timeDurationSince_epochAtSpec_keepsFs_subroutineOk {hookStack : Nat}
    (hstk : 144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => keepsFs (durationSinceEpochAtSpec hookStack)) externs :=
  SpecSimulates.multiSubroutineOk
    (fun _ => timeDurationSinceGe_simulates_epoch_keepsFs hstk)
    (timeDurationSince_ge_subroutineOk externs)

/-- Real-code `MultiPlacedLib.subroutineOk` for `durationSinceEpochAtSpec hookStack`
    (`144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64`, zero `.rodata` hypotheses). -/
theorem timeDurationSince_epochAtSpec_subroutineOk {hookStack : Nat}
    (hstk : 144 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => durationSinceEpochAtSpec hookStack) externs :=
  SpecSimulates.multiSubroutineOk
    (fun _ => (timeDurationSinceGe_simulates_epoch_keepsFs hstk).trans SpecSimulates.drop_keepsFs)
    (timeDurationSince_ge_subroutineOk externs)

/-- Real-code `MultiPlacedLib.subroutineOk` for `SpecBudget.durationSinceEpochBudgetSpec`
    (`= withVmPreserved CliExt.durationSinceEpochSpec`, `16384` B stack, zero `.rodata`). -/
theorem timeDurationSince_epochBudgetSpec_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => durationSinceEpochBudgetSpec) externs :=
  timeDurationSince_epochAtSpec_vm_subroutineOk (by decide) externs

/-- Real-code `MultiPlacedLib.subroutineOk` for `keepsFs durationSinceEpochBudgetSpec`
    (zero `.rodata`). -/
theorem timeDurationSince_epochBudgetSpec_keepsFs_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => keepsFs durationSinceEpochBudgetSpec) externs :=
  timeDurationSince_epochAtSpec_vm_keepsFs_subroutineOk (by decide) externs

/-- Real-code `MultiPlacedLib.subroutineOk` for `CliExt.durationSinceEpochSpec` with zero `.rodata`
    premises (`rfl`-identical to `Slots.durationSinceEpochSpec` and
    `WithStoresVT.ExtDefs.durationSinceEpochSpecExt`). -/
theorem timeDurationSince_epochSpec_zeroRo_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => durationSinceEpochSpec) externs :=
  timeDurationSince_epochAtSpec_subroutineOk (by decide) externs

/-- Real-code `MultiPlacedLib.subroutineOk` for `keepsFs CliExt.durationSinceEpochSpec` with zero
    `.rodata` premises. -/
theorem timeDurationSince_epochSpec_keepsFs_zeroRo_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => keepsFs durationSinceEpochSpec) externs :=
  timeDurationSince_epochAtSpec_keepsFs_subroutineOk (by decide) externs

/-- Real-code `MultiPlacedLib.subroutineOk` for `durationSinceEpochAllocBudgetSpec`
    (`= withVmPreserved (durationSinceEpochAtSpec allocHookStack)`, `4096` B stack, zero `.rodata`). -/
theorem timeDurationSince_epochAllocBudgetSpec_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => durationSinceEpochAllocBudgetSpec) externs :=
  timeDurationSince_epochAtSpec_vm_subroutineOk (by decide) externs

/-- Real-code `MultiPlacedLib.subroutineOk` for `keepsFs durationSinceEpochAllocBudgetSpec`
    (`SetUnackEpochPlacedBudgetFd`'s exact `duration_since` contract, zero `.rodata`). -/
theorem timeDurationSince_epochAllocBudgetSpec_keepsFs_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => keepsFs durationSinceEpochAllocBudgetSpec) externs :=
  timeDurationSince_epochAtSpec_vm_keepsFs_subroutineOk (by decide) externs

/-- Real-code `MultiPlacedLib.subroutineOk` for `durationSinceEpochAllocSpec` (`4096` B stack,
    zero `.rodata`). -/
theorem timeDurationSince_epochAllocSpec_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => durationSinceEpochAllocSpec) externs :=
  timeDurationSince_epochAtSpec_subroutineOk (by decide) externs

/-- Real-code `MultiPlacedLib.subroutineOk` for `durationSinceEpochBudgetSpec.inImage img`
    (fixed-`Obj.Image` `.inImage` companion to `timeDurationSince_epochBudgetSpec_subroutineOk`,
    zero `.rodata`). -/
theorem timeDurationSince_epochBudgetSpec_inImage_subroutineOk (img : Obj.Image)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => durationSinceEpochBudgetSpec.inImage img) externs := by
  obtain ⟨hexp, i, off, hfn, hsub⟩ := timeDurationSince_epochBudgetSpec_subroutineOk externs
  refine ⟨hexp, i, off, hfn, fun mpl hpl => ?_⟩
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _hL
  dsimp only [MultiPlacedLib.withCodeLoaded, Spec.inImage] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨_himg, hpre⟩ := hpre
  have hpre_cl : s0.mem ⊨ (timeMultiLib.withCodeLoaded mpl durationSinceEpochBudgetSpec).pre x s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl]
    exact hpre
  exact (hsub mpl hpl).mono_outcome x R s0 hpc hrun hpre_cl hsp (fun _ hout => hout)

/-- Real-code `MultiPlacedLib.subroutineOk` for `CliExt.durationSinceEpochSpec.inImage img`
    (`Stage2ContractsExt.duration_since`, zero `.rodata`). -/
theorem timeDurationSince_epochSpec_inImage_subroutineOk (img : Obj.Image)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun _ => durationSinceEpochSpec.inImage img) externs := by
  obtain ⟨hexp, i, off, hfn, hsub⟩ := timeDurationSince_epochSpec_zeroRo_subroutineOk externs
  refine ⟨hexp, i, off, hfn, fun mpl hpl => ?_⟩
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _hL
  dsimp only [MultiPlacedLib.withCodeLoaded, Spec.inImage] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨_himg, hpre⟩ := hpre
  have hpre_cl : s0.mem ⊨ (timeMultiLib.withCodeLoaded mpl durationSinceEpochSpec).pre x s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl]
    exact hpre
  exact (hsub mpl hpl).mono_outcome x R s0 hpc hrun hpre_cl hsp (fun _ hout => hout)

end LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceVm
