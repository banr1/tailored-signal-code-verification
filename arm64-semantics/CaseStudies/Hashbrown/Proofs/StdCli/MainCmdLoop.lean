/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.MainCmdStep
public import CaseStudies.Hashbrown.Proofs.StdCli.StdinAndVec
public meta import ProofLib.SepLogic.Stack
public meta import ProofLib.LiteralFetchLint
import ProofLib.BV

/-!
# Command Loop Induction and Table Drop for `hashbrown_cli`

Placement-generic `SepWP` proof for `hashbrown_cli::main` over `C : HbCliLayout`, covering table
initialization (`u + 0x13c`), line-by-line command execution, and table drop (`u + 0x310`).
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

local macro "unpack_loop_code " h:term : tactic => `(tactic| (
  have _hc := stdoutToStepFacts $h
  simp only [hbRustMainLoopChunks, stdoutStepFacts, stdoutStepAcc, fetchAtAcc',
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

local macro "norm_jmp" : tactic =>
  `(tactic| try conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel])
local macro "close_cs" : tactic =>
  `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])
local macro "close_cpu_step " s:term : term =>
  `(⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [CpuAuxPreserved.refl $s], by close_cs⟩)
local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)

attribute [local simp] cpuAux_writeReg64 cpuAux_writeReg32 cpuAux_writeReg
  cpuAux_setPState cpuAux_advancePC cpuAux_setPC cpuAux_setMem
@[local simp] private theorem cpuAux_writeVReg128 (s0 s : State) (r : BitVec 5) (v : BitVec 128) :
    CpuAuxPreserved s0 (s.writeVReg128 r v) ↔ CpuAuxPreserved s0 s := Iff.rfl

private theorem splitOnByte_getD_eq_sep (sep : BitVec 8) :
    ∀ (k : Nat) (rem : List (BitVec 8)),
      k < rem.length →
      splitOnByte sep rem = rem.take k :: splitOnByte sep (rem.drop (k + 1)) →
      rem.getD k 0#8 = sep
  | 0, b :: rs, _, hsp => by
    conv at hsp => lhs; unfold splitOnByte
    by_cases hb : (b == sep) = true
    · simpa [List.getD] using beq_iff_eq.mp hb
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hsp
      rcases hsub : splitOnByte sep rs with _ | ⟨hd, tl⟩ <;> simp [hsub] at hsp
  | k + 1, b :: rs, hk, hsp => by
    conv at hsp => lhs; unfold splitOnByte
    by_cases hb : (b == sep) = true
    · simp [hb] at hsp
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, List.take_succ_cons, List.drop_succ_cons] at hsp
      rcases hsub : splitOnByte sep rs with _ | ⟨hd, tl⟩
      · exact False.elim (splitOnByte_ne_nil sep rs hsub)
      · simp only [hsub, List.cons.injEq] at hsp
        obtain ⟨⟨_, hhd⟩, htl⟩ := hsp
        simpa [List.getD] using splitOnByte_getD_eq_sep sep k rs
          (Nat.lt_of_succ_lt_succ hk) (by rw [hsub, hhd, htl])

private theorem evalLinesStep_foldl_prefix (lines : List (List (BitVec 8))) (m : CliMap)
    (o0 e0 o e : List (BitVec 8)) :
    lines.foldl evalLinesStep (m, o0 ++ o, e0 ++ e) =
      let r := lines.foldl evalLinesStep (m, o, e); (r.1, o0 ++ r.2.1, e0 ++ r.2.2) := by
  induction lines generalizing m o e with
  | nil => rfl
  | cons line rest ih =>
    dsimp only [List.foldl_cons, evalLinesStep]
    cases parseCommand line with
    | none => simpa only [List.append_assoc] using ih m o (e ++ bytesOfString "error: invalid command\n")
    | some c => cases c with
      | insert k v     => exact ih (cliMapInsert k v m) o e
      | remove k       => exact ih (cliMapErase k m) o e
      | get k          => simpa only [List.append_assoc] using ih m (o ++ formatGetResult (cliMapLookup k m)) e
      | contains k     => simpa only [List.append_assoc] using ih m (o ++ formatBoolResult (cliMapLookup k m).isSome) e
      | withCapacity _ => exact ih [] o e
      | len            => simpa only [List.append_assoc] using ih m (o ++ formatDecimalNat m.length ++ bytesOfString "\n") e
      | isEmpty        => simpa only [List.append_assoc] using ih m (o ++ formatBoolResult m.isEmpty) e
      | clear          => exact ih [] o e

private theorem formatGetResult_len_eq {L k_ins : Nat} (m : Map64) (o : List (BitVec 8))
    (hL : L ≤ HashbrownCliMaxStdin) (hins : 11 * k_ins ≤ L + 1) (hlen : m.length ≤ k_ins) :
    o ++ formatGetResult (some (BitVec.ofNat 64 m.length)) = o ++ formatDecimalNat m.length ++ bytesOfString "\n" := by
  have hlt : m.length < 2 ^ 64 := by unfold HashbrownCliMaxStdin at hL; omega
  simp [formatGetResult_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, List.append_assoc]

private theorem loop_print_budget {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {bm : BitVec 64} {baseLc baseBlk vecCap k_ins : Nat} (hL : L ≤ HashbrownCliMaxStdin)
    (hbaseLc : baseLc ≤ mallocngBlockCost 8192 + hbByteVecCost vecCap) (hbaseBlk : baseBlk ≤ 2)
    (hcap : vecCap ≤ 2 * L + 32) (hins0 : 11 * k_ins ≤ L + 1) (hbm_wf : bm = 0#64 ∨ ValidBucketMask bm)
    (hbm_bound : bm ≠ 0#64 → bm.toNat + 1 ≤ max 8192 (3 * k_ins)) :
    1024 ≤ (hbStdLimits L).maxReq ∧
    (baseLc + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm) + mallocngBlockCost 1024 ≤ (hbStdLimits L).maxPeakCost ∧
    (baseBlk + tableAllocBlocks bm) + 1 ≤ (hbStdLimits L).maxPeakBlocks :=
  hbCli_print_budget M γ CodeInv hCodeInv hL hins0 hbm_wf hbm_bound hcap
    (Nat.add_le_add_right (by simpa [hbByteVecCost] using hbaseLc) _) (by unfold tableAllocBlocks; split <;> omega)

private theorem loop_reserve_budget {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {m : Map64} {bm : BitVec 64} {init : Bool} {baseLc baseBlk vecCap k_ins : Nat} (hL : L ≤ HashbrownCliMaxStdin)
    (hbaseLc : baseLc ≤ mallocngBlockCost 8192 + hbByteVecCost vecCap) (hbaseBlk : baseBlk ≤ 2)
    (hcap : vecCap ≤ 2 * L + 32) (hins1 : 11 * (k_ins + 1) ≤ L + 1) (hm_len : m.length ≤ k_ins)
    (hbm_wf : bm = 0#64 ∨ ValidBucketMask bm) (hbm_bound : bm ≠ 0#64 → bm.toNat + 1 ≤ max 8192 (3 * k_ins)) :
    HbCanInsertOne (HbAlloc.ofMallocng M γ CodeInv hCodeInv) m bm k_ins
      ((baseLc + hbStdoutCost init) + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm)
      ((baseBlk + hbStdoutBlocks init) + tableAllocBlocks bm) :=
  hbCli_canInsertOne M γ CodeInv hCodeInv hL hins1 hm_len hbm_wf hbm_bound hcap
    (Nat.add_le_add_right (by
      unfold hbByteVecCost at hbaseLc; cases init <;> simp only [hbStdoutCost, ↓reduceIte, Bool.false_eq_true] <;> omega) _)
    (by unfold tableAllocBlocks; cases init <;> split <;> simp only [hbStdoutBlocks, ↓reduceIte, Bool.false_eq_true] <;> omega)

private theorem loop_withCap_budget {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {cap : BitVec 64} {init : Bool} {baseLc baseBlk vecCap : Nat} (hcap_le : cap.toNat ≤ MaxWithCapacity)
    (hbaseLc : baseLc ≤ mallocngBlockCost 8192 + hbByteVecCost vecCap) (hbaseBlk : baseBlk ≤ 2) (hcap : vecCap ≤ 2 * L + 32) :
    HbCanWithCapacity (HbAlloc.ofMallocng M γ CodeInv hCodeInv) cap (baseLc + hbStdoutCost init) (baseBlk + hbStdoutBlocks init) :=
  hbCli_canWithCapacity M γ CodeInv hCodeInv hcap_le hcap
    (by unfold hbByteVecCost at hbaseLc; cases init <;> simp only [hbStdoutCost, ↓reduceIte, Bool.false_eq_true] <;> omega)
    (by cases init <;> simp only [hbStdoutBlocks, ↓reduceIte, Bool.false_eq_true] <;> omega)

private theorem init_pre_new_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hpc : s.pc = C.std.userMainAddr + 0x13c#64) (hrun : s.status = .Running) (hci : CodeInv s.mem)
    (hNext : ∀ s1 : State, s1.pc = hashbrownLib.fnAddr C.hbMpl "hashbrown_new" → s1.status = .Running →
      s1.sp = s.sp → s1.spAligned = s.spAligned → s1.fs = s.fs → s1.trace = s.trace →
      s1.tpidrEl0 = s.tpidrEl0 → s1.sigActions = s.sigActions → calleeSavedVRegs s1 = calleeSavedVRegs s →
      VmFieldsPreserved s s1 → CodeInv s1.mem → s1.readReg64 Reg.lr = C.std.userMainAddr + 0x148#64 →
      s1.readReg64 .x8 = s.sp + 0x20#64 → s1.readReg64 .x19 = s.readReg64 .x9 →
      s1.readReg64 .x22 = s.readReg64 .x22 → s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP P target s1 Pre post) :
    SepWP P target s Pre post := by
  refine sepWP_cpu_cut (mid := hashbrownLib.fnAddr C.hbMpl "hashbrown_new") hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'; wp_steps 2; wp_steps 1; norm_jmp
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 =>
    hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
      (by simp [State.spAligned, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      hvm1 hci1 wp_a wp_a wp_a wp_a wp_a wp_a

private theorem init_post_new_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target sp_m vecPtr : BitVec 64} {s_ref s : State} {Pre : State → SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hPre : ∀ {s1 s2 : State}, s2.tpidrEl0 = s1.tpidrEl0 → VmFieldsPreserved s1 s2 → Pre s1 ⊢ Pre s2)
    (hpc : s.pc = C.std.userMainAddr + 0x148#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_m) (hsp_al : s.spAligned = true) (hfs : s.fs = s_ref.fs) (htp : s.tpidrEl0 = s_ref.tpidrEl0)
    (hsig : s.sigActions = s_ref.sigActions) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_ref)
    (hx19 : s.readReg64 .x19 = vecPtr) (hx28 : s.readReg64 .x28 = s_ref.readReg64 .x28)
    (hx29 : s.readReg64 .x29 = sp_m + 0x80#64) (hci : CodeInv s.mem)
    (hNext : ∀ sf : State, sf.pc = C.std.userMainAddr + 0x184#64 → sf.status = .Running →
      CmdLoopState C sp_m s_ref sf → CodeInv sf.mem → sf.trace = s.trace →
      sf.readReg64 .x0 = vecPtr → sf.readReg64 .x22 = s.readReg64 .x22 → SepWP P target sf (Pre sf) post) :
    SepWP P target s (Pre s) post := by
  refine sepWP_cpu_cut (mid := C.std.userMainAddr + 0x184#64) hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'
  dsimp only [Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x28, Reg.x29, Reg.x0] at *
  wp_steps 2; wp_steps 1; wp_steps 2; wp_steps 1; wp_steps 2; wp_steps 1; wp_steps 1
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 => ?_
  refine SepWP.weaken_pre (hPre (by simp [wp_norm, arm64_norm]) hvm1)
    (hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) ?_ hci1 (by simp [wp_norm, arm64_norm]) wp_a wp_a)
  exact ⟨by simp [wp_norm, arm64_norm, hsp], by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al,
    by simp [wp_norm, arm64_norm, hfs], by simp [wp_norm, arm64_norm, htp],
    by simp [wp_norm, arm64_norm, hsig], by simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregs],
    wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a⟩

private theorem parse_prep_wp {Q : Program} {C : HbCliLayout}
    {target sp_m : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hc : HbMainCmdCode Q C) (hpc : s.pc = C.std.userMainAddr + 0x1d4#64) (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp_m + 0x80#64)
    (hNext : ∀ s1 : State, s1.pc = C.parseCommandAddr → s1.status = .Running → PureCpuStep s s1 →
      s1.readReg64 Reg.lr = C.std.userMainAddr + 0x1dc#64 → s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.readReg64 .x1 = s.readReg64 .x1 → s1.readReg64 .x8 = sp_m + 0x48#64 → SepWP Q target s1 Pre post) :
    SepWP Q target s Pre post := by
  have hc' := hc.rustMainLoop; unpack_loop_code hc'
  dsimp only [Reg.x29, Reg.x8, Reg.x0, Reg.x1, Reg.lr] at *; wp_steps 1; wp_steps 1; norm_jmp
  exact hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) wp_a wp_a wp_a wp_a

private theorem jumpToTail_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target sp_m nextPtr off : BitVec 64} {hasMore : Bool} {s_ref s : State} {Pre : State → SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hPre : ∀ {s1 s2 : State}, s2.tpidrEl0 = s1.tpidrEl0 → VmFieldsPreserved s1 s2 → Pre s1 ⊢ Pre s2)
    (hoff : off = 0x20c#64 ∨ off = 0x29c#64 ∨ off = 0x2a8#64 ∨ off = 0x2b8#64 ∨ off = 0x2c0#64 ∨ off = 0x2fc#64)
    (hpc : s.pc = C.std.userMainAddr + off) (hrun : s.status = .Running)
    (hst : CmdLoopState C sp_m s_ref s) (hci : CodeInv s.mem)
    (hx27 : s.readReg64 .x27 = nextPtr) (hx26 : s.readReg64 .x26 = if hasMore then 0#64 else 1#64)
    (hNext : ∀ sf : State, sf.pc = (if hasMore then C.std.userMainAddr + 0x184#64 else C.std.userMainAddr + 0x300#64) →
      sf.status = .Running → CmdLoopState C sp_m s_ref sf → CodeInv sf.mem →
      sf.trace = s.trace → sf.readReg64 .x0 = nextPtr → sf.readReg64 .x22 = s.readReg64 .x22 → SepWP P target sf (Pre sf) post) :
    SepWP P target s (Pre s) post := by
  refine sepWP_cpu_cut (mid := C.std.userMainAddr + 0x17c#64) hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'
  rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (wp_steps 1; refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 => ?_
     refine sepWP_let_cpu (s0 := s) (close_cpu_step s) fun s1 hs1_eq hcpu1 => ?_
     rw [← hs1_eq] at hvm1 hci1; refine SepWP.weaken_pre (hPre hcpu1.2.2.2.1.1 hvm1) ?_
     exact tailAt0x17c_wp hCodeInv hcCmd hext hsvc hPre
       (by rw [hs1_eq]; exact wp_a) (by rw [hs1_eq]; simp [wp_norm, arm64_norm, hrun])
       (hst.of_cpu hcpu1) hci1 (hcpu1.2.2.2.2.readReg64_x27.trans hx27) (hcpu1.2.2.2.2.readReg64_x26.trans hx26)
       fun sf hpc_f hrun_f hst_f hci_f htr_f hx0_f hx22_f =>
         hNext sf hpc_f hrun_f hst_f hci_f (htr_f.trans hcpu1.2.2.1) hx0_f (hx22_f.trans hcpu1.2.2.2.2.readReg64_x22))

private theorem bl_print_step_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target off callee : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hbl : (off = 0x208#64 ∧ callee = C.printBoolAddr) ∨ (off = 0x298#64 ∧ callee = C.printBoolAddr) ∨
           (off = 0x2a4#64 ∧ callee = C.printU64Addr))
    (hpc : s.pc = C.std.userMainAddr + off) (hrun : s.status = .Running) (hci : CodeInv s.mem)
    (hNext : ∀ s1 : State, s1.pc = callee → s1.status = .Running →
      PureCpuStep s s1 → VmFieldsPreserved s s1 → CodeInv s1.mem →
      s1.readReg64 Reg.lr = C.std.userMainAddr + (off + 4#64) → s1.readReg64 .x0 = s.readReg64 .x0 →
      SepWP P target s1 Pre post) :
    SepWP P target s Pre post := by
  refine sepWP_cpu_cut (mid := callee) hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'
  rcases hbl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (wp_steps 1; norm_jmp
     exact SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 =>
       hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) hvm1 hci1 wp_a wp_a)

private theorem post_get_none_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hpc : s.pc = C.std.userMainAddr + 0x278#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64) (hci : CodeInv s.mem)
    (hNext : ∀ s1 : State, s1.pc = C.stdioPrintAddr → s1.status = .Running →
      PureCpuStep s s1 → VmFieldsPreserved s s1 → CodeInv s1.mem →
      s1.readReg64 Reg.lr = C.std.userMainAddr + 0x2fc#64 →
      s1.readReg64 .x0 = s.readReg64 .x20 → s1.readReg64 .x1 = 0x0b#64 → SepWP P target s1 Pre post) :
    SepWP P target s Pre post := by
  refine sepWP_cpu_cut (mid := C.stdioPrintAddr) hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'
  have hx0' : s.readReg64 (.gpr 0#5) = 0#64 := hx0
  dsimp only [Reg.x20, Reg.x0, Reg.x1, Reg.lr] at *; wp_steps 3; wp_steps 1; norm_jmp
  exact SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 =>
    hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) hvm1 hci1 wp_a wp_a wp_a

private theorem post_get_some_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target v : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hpc : s.pc = C.std.userMainAddr + 0x278#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 1#64) (hx1 : s.readReg64 .x1 = v) (hci : CodeInv s.mem)
    (hNext : ∀ s1 : State, s1.pc = C.printU64Addr → s1.status = .Running →
      PureCpuStep s s1 → VmFieldsPreserved s s1 → CodeInv s1.mem →
      s1.readReg64 Reg.lr = C.std.userMainAddr + 0x2a8#64 → s1.readReg64 .x0 = v → SepWP P target s1 Pre post) :
    SepWP P target s Pre post := by
  refine sepWP_cpu_cut (mid := C.printU64Addr) hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'
  have hx0' : s.readReg64 (.gpr 0#5) = 1#64 := hx0
  dsimp only [Reg.x0, Reg.x1, Reg.lr] at *; wp_steps 3; wp_steps 1; norm_jmp
  exact SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 =>
    hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) hvm1 hci1 wp_a wp_a

private theorem fp_off_48 (sp_m : BitVec 64) : sp_m + 0x48#64 = (sp_m + 0x80#64) + (-0x38#64) := by bv_lin
private theorem fp_off_50 (sp_m : BitVec 64) : sp_m + 0x50#64 = (sp_m + 0x80#64) + (-0x30#64) := by bv_lin
private theorem fp_off_58 (sp_m : BitVec 64) : sp_m + 0x58#64 = ((sp_m + 0x80#64) + (-0x30#64)) + 8#64 := by bv_lin
private theorem fp_off_60 (sp_m : BitVec 64) : sp_m + 0x60#64 = (sp_m + 0x80#64) + (-0x20#64) := by bv_lin

private theorem withCap_moveTo60_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target sp_m cap : BitVec 64} {q0 q1 d0 d1 : BitVec 128} {s_ref s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hpc : s.pc = C.std.userMainAddr + 0x2c4#64) (hrun : s.status = .Running)
    (hst : CmdLoopState C sp_m s_ref s) (hci : CodeInv s.mem)
    (hNext : ∀ s1 : State, s1.pc = hashbrownLib.fnAddr C.hbMpl "hashbrown_drop" → s1.status = .Running →
      CmdLoopState C sp_m s_ref s1 → VmFieldsPreserved s s1 → CodeInv s1.mem → s1.trace = s.trace →
      s1.readReg64 Reg.lr = C.std.userMainAddr + 0x2d8#64 → s1.readReg64 .x0 = sp_m + 0x60#64 → s1.readReg64 .x21 = cap →
      s1.readReg64 .x22 = s.readReg64 .x22 → s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = s.readReg64 .x27 →
      SepWP P target s1 (((sp_m + 0x20#64) ↦₁₂₈ q0) ∗ (((sp_m + 0x20#64) + 16#64) ↦₁₂₈ q1) ∗
        ((sp_m + 0x50#64) ↦₆₄ cap) ∗ ((sp_m + 0x60#64) ↦₁₂₈ q0) ∗ (((sp_m + 0x60#64) + 16#64) ↦₁₂₈ q1) ∗ Rest) post) :
    SepWP P target s (((sp_m + 0x20#64) ↦₁₂₈ q0) ∗ (((sp_m + 0x20#64) + 16#64) ↦₁₂₈ q1) ∗
      ((sp_m + 0x50#64) ↦₆₄ cap) ∗ ((sp_m + 0x60#64) ↦₁₂₈ d0) ∗ (((sp_m + 0x60#64) + 16#64) ↦₁₂₈ d1) ∗ Rest) post := by
  conv => arg 4; simp only [fp_off_50 sp_m, fp_off_60 sp_m, pointsTo128_split64, BitVec.reduceNeg]
  refine sepWP_cpu_cut (mid := hashbrownLib.fnAddr C.hbMpl "hashbrown_drop") hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'
  rcases hst with ⟨hsp, hsp_al, hfs, htp, hsig, hvregs, r19, r20, r23, r24, r25, r28, r29⟩
  dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x0, Reg.lr] at *
  wp_steps 4; wp_steps 1; norm_jmp
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 =>
    SepWP.weaken_pre (by simp only [fp_off_50 sp_m, fp_off_60 sp_m, pointsTo128_split64, BitVec.reduceNeg]; sep_entail)
      (hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) ?_ hvm1 hci1 (by simp [wp_norm, arm64_norm]) wp_a wp_a wp_a wp_a wp_a wp_a)
  exact ⟨by simp [wp_norm, arm64_norm, hsp], by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al,
    by simp [wp_norm, arm64_norm, hfs], by simp [wp_norm, arm64_norm, htp],
    by simp [wp_norm, arm64_norm, hsig], by simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregs],
    wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a⟩

private theorem withCap_prep_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target sp_m : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hpc : s.pc = C.std.userMainAddr + 0x2d8#64) (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp_m + 0x80#64) (hci : CodeInv s.mem)
    (hNext : ∀ s1 : State, s1.pc = hashbrownLib.fnAddr C.hbMpl "hashbrown_with_capacity" → s1.status = .Running →
      PureCpuStep s s1 → VmFieldsPreserved s s1 → CodeInv s1.mem → s1.readReg64 Reg.lr = C.std.userMainAddr + 0x2e4#64 →
      s1.readReg64 .x0 = s.readReg64 .x21 → s1.readReg64 .x8 = sp_m + 0x60#64 → SepWP P target s1 Pre post) :
    SepWP P target s Pre post := by
  refine sepWP_cpu_cut (mid := hashbrownLib.fnAddr C.hbMpl "hashbrown_with_capacity") hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'
  dsimp only [Reg.x29, Reg.x21, Reg.x8, Reg.x0, Reg.lr] at *; wp_steps 2; wp_steps 1; norm_jmp
  exact SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 =>
    hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) hvm1 hci1 wp_a wp_a wp_a

private theorem withCap_moveTo20_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target sp_m : BitVec 64} {q0 q1 d0 d1 : BitVec 128} {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hpc : s.pc = C.std.userMainAddr + 0x2e4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_m) (hsp_al : s.spAligned = true) (hx29 : s.readReg64 .x29 = sp_m + 0x80#64) (hci : CodeInv s.mem)
    (hNext : ∀ s1 : State, s1.pc = C.std.userMainAddr + 0x17c#64 → s1.status = .Running →
      PureCpuStep s s1 → VmFieldsPreserved s s1 → CodeInv s1.mem →
      SepWP P target s1 (((sp_m + 0x20#64) ↦₁₂₈ q0) ∗ (((sp_m + 0x20#64) + 16#64) ↦₁₂₈ q1) ∗
        ((sp_m + 0x60#64) ↦₁₂₈ q0) ∗ (((sp_m + 0x60#64) + 16#64) ↦₁₂₈ q1) ∗ Rest) post) :
    SepWP P target s (((sp_m + 0x20#64) ↦₁₂₈ d0) ∗ (((sp_m + 0x20#64) + 16#64) ↦₁₂₈ d1) ∗
      ((sp_m + 0x60#64) ↦₁₂₈ q0) ∗ (((sp_m + 0x60#64) + 16#64) ↦₁₂₈ q1) ∗ Rest) post := by
  conv => arg 4; simp only [fp_off_60 sp_m, pointsTo128_split64, BitVec.reduceNeg]
  refine sepWP_cpu_cut (mid := C.std.userMainAddr + 0x17c#64) hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'
  dsimp only [Reg.x29] at *; wp_steps 3
  exact SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 =>
    SepWP.weaken_pre (by simp only [fp_off_60 sp_m, pointsTo128_split64, BitVec.reduceNeg]; sep_entail)
      (hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) hvm1 hci1)

private theorem tableDrop_moveTo60_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target sp_m : BitVec 64} {q0 q1 d0 d1 : BitVec 128} {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hpc : s.pc = C.std.userMainAddr + 0x300#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_m) (hsp_al : s.spAligned = true) (hx29 : s.readReg64 .x29 = sp_m + 0x80#64) (hci : CodeInv s.mem)
    (hNext : ∀ s1 : State, s1.pc = hashbrownLib.fnAddr C.hbMpl "hashbrown_drop" → s1.status = .Running →
      PureCpuStep s s1 → VmFieldsPreserved s s1 → CodeInv s1.mem →
      s1.readReg64 Reg.lr = C.std.userMainAddr + 0x310#64 → s1.readReg64 .x0 = sp_m + 0x60#64 →
      SepWP P target s1 (((sp_m + 0x20#64) ↦₁₂₈ q0) ∗ (((sp_m + 0x20#64) + 16#64) ↦₁₂₈ q1) ∗
        ((sp_m + 0x60#64) ↦₁₂₈ q0) ∗ (((sp_m + 0x60#64) + 16#64) ↦₁₂₈ q1) ∗ Rest) post) :
    SepWP P target s (((sp_m + 0x20#64) ↦₁₂₈ q0) ∗ (((sp_m + 0x20#64) + 16#64) ↦₁₂₈ q1) ∗
      ((sp_m + 0x60#64) ↦₁₂₈ d0) ∗ (((sp_m + 0x60#64) + 16#64) ↦₁₂₈ d1) ∗ Rest) post := by
  conv => arg 4; simp only [fp_off_60 sp_m, pointsTo128_split64, BitVec.reduceNeg]
  refine sepWP_cpu_cut (mid := hashbrownLib.fnAddr C.hbMpl "hashbrown_drop") hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'
  dsimp only [Reg.x29, Reg.x0, Reg.lr] at *; wp_steps 3; wp_steps 1; norm_jmp
  exact SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 =>
    SepWP.weaken_pre (by simp only [fp_off_60 sp_m, pointsTo128_split64, BitVec.reduceNeg]; sep_entail)
      (hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) hvm1 hci1 wp_a wp_a)

private def dispatchTargetPc (C : HbCliLayout) : Option CliCmd → BitVec 64
  | none                   => C.std.userMainAddr + 0x220#64
  | some (.insert _ _)     => hashbrownLib.fnAddr C.hbMpl "hashbrown_insert"
  | some (.get _)          => hashbrownLib.fnAddr C.hbMpl "hashbrown_get"
  | some (.remove _)       => hashbrownLib.fnAddr C.hbMpl "hashbrown_remove"
  | some (.contains _)     => hashbrownLib.fnAddr C.hbMpl "hashbrown_contains_key"
  | some (.withCapacity _) => C.std.userMainAddr + 0x2c4#64
  | some .len              => hashbrownLib.fnAddr C.hbMpl "hashbrown_len"
  | some .isEmpty          => hashbrownLib.fnAddr C.hbMpl "hashbrown_is_empty"
  | some .clear            => hashbrownLib.fnAddr C.hbMpl "hashbrown_clear"

private def DispatchRegs (C : HbCliLayout) (sp_m : BitVec 64) (s1 : State) : Option CliCmd → Prop
  | none                   => True
  | some (.insert k v)     => s1.readReg64 Reg.lr = C.std.userMainAddr + 0x2b8#64 ∧ s1.readReg64 .x0 = sp_m + 0x20#64 ∧ s1.readReg64 .x1 = k ∧ s1.readReg64 .x2 = v
  | some (.get k)          => s1.readReg64 Reg.lr = C.std.userMainAddr + 0x278#64 ∧ s1.readReg64 .x0 = sp_m + 0x20#64 ∧ s1.readReg64 .x1 = k
  | some (.remove k)       => s1.readReg64 Reg.lr = C.std.userMainAddr + 0x17c#64 ∧ s1.readReg64 .x0 = sp_m + 0x20#64 ∧ s1.readReg64 .x1 = k
  | some (.contains k)     => s1.readReg64 Reg.lr = C.std.userMainAddr + 0x298#64 ∧ s1.readReg64 .x0 = sp_m + 0x20#64 ∧ s1.readReg64 .x1 = k
  | some (.withCapacity _) => True
  | some .len              => s1.readReg64 Reg.lr = C.std.userMainAddr + 0x2a4#64 ∧ s1.readReg64 .x0 = sp_m + 0x20#64
  | some .isEmpty          => s1.readReg64 Reg.lr = C.std.userMainAddr + 0x208#64 ∧ s1.readReg64 .x0 = sp_m + 0x20#64
  | some .clear            => s1.readReg64 Reg.lr = C.std.userMainAddr + 0x2c0#64 ∧ s1.readReg64 .x0 = sp_m + 0x20#64

private theorem dispatch_slot_wp {Q : Program} {C : HbCliLayout}
    {target sp_m r0 r1 r2 : BitVec 64} {cmd : Option CliCmd} {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (hc : HbMainCmdCode Q C) (hslot : ParseCmdSlot cmd r0 r1 r2)
    (hpc : s.pc = C.std.userMainAddr + 0x1dc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_m) (hx29 : s.readReg64 .x29 = sp_m + 0x80#64)
    (hNext : ∀ s1 : State, s1.pc = dispatchTargetPc C cmd → s1.status = .Running →
      PureCpuStep s s1 → DispatchRegs C sp_m s1 cmd →
      SepWP Q target s1 (((sp_m + 0x48#64) ↦₆₄ r0) ∗ ((sp_m + 0x50#64) ↦₆₄ r1) ∗ ((sp_m + 0x58#64) ↦₆₄ r2) ∗ Rest) post) :
    SepWP Q target s (((sp_m + 0x48#64) ↦₆₄ r0) ∗ ((sp_m + 0x50#64) ↦₆₄ r1) ∗ ((sp_m + 0x58#64) ↦₆₄ r2) ∗ Rest) post := by
  have hNext' : ∀ s1 : State, s1.pc = dispatchTargetPc C cmd → s1.status = .Running →
      PureCpuStep s s1 → DispatchRegs C sp_m s1 cmd → SepWP Q target s1
        ((((sp_m + 0x80#64) + (-0x38#64)) ↦₆₄ r0) ∗ (((sp_m + 0x80#64) + (-0x30#64)) ↦₆₄ r1) ∗
         ((((sp_m + 0x80#64) + (-0x30#64)) + 8#64) ↦₆₄ r2) ∗ Rest) post := fun s1 h1 h2 h3 h4 =>
    SepWP.weaken_pre (by simp only [fp_off_48 sp_m, fp_off_50 sp_m, fp_off_58 sp_m]; sep_entail) (hNext s1 h1 h2 h3 h4)
  conv at hNext' => intro s1 h1 h2 h3 h4; arg 4; simp only [BitVec.reduceNeg]
  conv => arg 4; simp only [fp_off_48 sp_m, fp_off_50 sp_m, fp_off_58 sp_m, BitVec.reduceNeg]
  have hc' := hc.rustMainLoop; unpack_loop_code hc'
  dsimp only [Reg.x29, Reg.x0, Reg.x1, Reg.x2, Reg.lr] at *
  rcases cmd with _ | ⟨k, v⟩ | k | k | k | cap | _ | _ | _ <;> dsimp only [dispatchTargetPc, DispatchRegs] at hNext'
  · subst hslot; wp_steps 7; exact hNext' _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) trivial
  · rcases hslot with ⟨rfl, rfl, rfl⟩; wp_steps 9; wp_steps 1; norm_jmp
    exact hNext' _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) ⟨wp_a, wp_a, wp_a, wp_a⟩
  · rcases hslot with ⟨rfl, rfl⟩; wp_steps 5; wp_steps 4; wp_steps 1; norm_jmp
    exact hNext' _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) ⟨wp_a, wp_a, wp_a⟩
  · rcases hslot with ⟨rfl, rfl⟩; wp_steps 5; wp_steps 4; wp_steps 1; norm_jmp
    exact hNext' _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) ⟨wp_a, wp_a, wp_a⟩
  · rcases hslot with ⟨rfl, rfl⟩; wp_steps 9; wp_steps 1; norm_jmp
    exact hNext' _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) ⟨wp_a, wp_a, wp_a⟩
  · rcases hslot with ⟨rfl, rfl, _⟩; wp_steps 7; exact hNext' _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) trivial
  · subst hslot; wp_steps 8; wp_steps 1; norm_jmp; exact hNext' _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) ⟨wp_a, wp_a⟩
  · subst hslot; wp_steps 10; wp_steps 1; norm_jmp; exact hNext' _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) ⟨wp_a, wp_a⟩
  · subst hslot; wp_steps 10; wp_steps 1; norm_jmp; exact hNext' _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) ⟨wp_a, wp_a⟩

/-! ## Command loop induction and table drop -/

private def CmdLoopRestNo60 {P : Program} {L : Nat} (C : HbCliLayout)
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (sp_m : BitVec 64) (haveLse : BitVec 8) (baseLc baseBlk : Nat)
    (bm : BitVec 64) (init : Bool) (e_err : BitVec 32) (c0 c1 c2 : BitVec 64) (s : State) : SepProp :=
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  M.Heap γ (baseLc + hbStdoutCost init + hbMapCost A bm) (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) s ∗
  HbStdoutInv C M γ init ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbCmdRoData C ∗
  (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ HbThreadIdInv C s.tpidrEl0 ∗ (muslErrnoAddr s ↦₃₂ e_err) ∗
  memRegion (sp_m + 0x40#64) 8 ∗ ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ c1) ∗ ((sp_m + 0x58#64) ↦₆₄ c2) ∗
  memRegion (sp_m + 0x98#64) 8 ∗ stackAt sp_m 4432

private theorem CmdLoopRestNo60.transport {P : Program} {L : Nat} {C : HbCliLayout}
    {M : MallocngCoreIface P C.mallocng (hbStdLimits L)} {γ : GhostName} {CodeInv : Memory → Prop}
    {hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2}
    {sp_m : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk : Nat} {bm : BitVec 64} {init : Bool}
    {e_err : BitVec 32} {c0 c1 c2 : BitVec 64} {s sf : State} (htp : sf.tpidrEl0 = s.tpidrEl0) (hvm : VmFieldsPreserved s sf) :
    CmdLoopRestNo60 C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 c1 c2 s ⊢
    CmdLoopRestNo60 C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 c1 c2 sf := by
  unfold CmdLoopRestNo60; have herr : muslErrnoAddr s = muslErrnoAddr sf := by simp [muslErrnoAddr, htp]
  rw [herr, ← htp]; exact sepConj_mono_left (M.heap_transport hvm.brk_eq hvm.brkStart_eq hvm.physMemAvail_eq hvm.perm_eq)

private theorem cmdLoopRes_unpack_qpairs {P : Program} {L : Nat} {C : HbCliLayout}
    {M : MallocngCoreIface P C.mallocng (hbStdLimits L)} {γ : GhostName} {CodeInv : Memory → Prop}
    {hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2}
    {sp_m : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk u : Nat}
    {m : Map64} {bm : BitVec 64} {init : Bool} {e_err : BitVec 32} {c0 c1 c2 : BitVec 64} {s : State} :
    CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ d0 : BitVec 128, ∃∗ d1 : BitVec 128,
        ((sp_m + 0x20#64) ↦₁₂₈ q0) ∗ (((sp_m + 0x20#64) + 16#64) ↦₁₂₈ q1) ∗
        ((sp_m + 0x60#64) ↦₁₂₈ d0) ∗ (((sp_m + 0x60#64) + 16#64) ↦₁₂₈ d1) ∗
        HbMapMoved C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv) m bm u q0 q1 ∗
        CmdLoopRestNo60 C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 c1 c2 s := by
  have hm := U64MapRep_unpack_qpair C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv) (sp_m + 0x20#64) m bm u
  have hd := memRegion32_to_qpair (sp_m + 0x60#64)
  have h1 : CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s ⊢
      U64MapRep C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv) (sp_m + 0x20#64) m bm u ∗ memRegion (sp_m + 0x60#64) 32 ∗
      CmdLoopRestNo60 C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 c1 c2 s := by
    dsimp only [CmdLoopRes, CmdLoopRest, CmdLoopRestNo60]; sep_entail
  refine Entails.trans h1 (Entails.trans (sepConj_mono hm (sepConj_mono_left hd)) ?_)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d0; apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro q0; apply Entails.sepExists_elim; intro q1
  exact Entails.sepExists_right q0 (Entails.sepExists_right q1
    (Entails.sepExists_right d0 (Entails.sepExists_right d1 (by sep_entail))))

private theorem withCap_dropAndAlloc_wp {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (K : HbCmdCallees C M γ CodeInv hCodeInv)
    {target sp_m bm cap c0 c2 : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk vecCap u : Nat}
    {m : Map64} {init : Bool} {e_err : BitVec 32} {s_ref s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hsp_hi : sp_m.toNat + 0x80 ≤ 2 ^ 64)
    (hbaseLc : baseLc ≤ mallocngBlockCost 8192 + hbByteVecCost vecCap) (hbaseBlk : baseBlk ≤ 2)
    (hcap : vecCap ≤ 2 * L + 32) (hcap_le : cap.toNat ≤ MaxWithCapacity)
    (hpc0 : s0.pc = C.std.userMainAddr + 0x2c4#64) (hrun0 : s0.status = .Running)
    (hst0 : CmdLoopState C sp_m s_ref s0) (hci0 : CodeInv s0.mem)
    (hNext : ∀ (s4 : State) (e2 : BitVec 32), let bm' := capToBucketMask cap.toNat
      s4.pc = C.std.userMainAddr + 0x2e4#64 → s4.status = .Running → CmdLoopState C sp_m s_ref s4 → CodeInv s4.mem →
      s4.trace = s0.trace → s4.readReg64 .x22 = s0.readReg64 .x22 → s4.readReg64 .x26 = s0.readReg64 .x26 →
      s4.readReg64 .x27 = s0.readReg64 .x27 →
      SepWP P target s4 (hbRodata C.hbPl ∗ U64MapRep C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv) (sp_m + 0x60#64) [] bm' 0 ∗
        memRegion (sp_m + 0x20#64) 32 ∗
        CmdLoopRestNo60 C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm' init e2 c0 cap c2 s4 ∗ F) post) :
    SepWP P target s0 (hbRodata C.hbPl ∗
      CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 cap c2 s0 ∗ F) post := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  obtain ⟨_, _, h60_al, h60_fit⟩ := sp_main_frame_facts hst0.2.1 hst0.1 hsp_hi
  have hcan := loop_withCap_budget M γ CodeInv hCodeInv (init := init) hcap_le hbaseLc hbaseBlk hcap
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left cmdLoopRes_unpack_qpairs)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro q0; apply SepWP.exists_left; intro q1
  apply SepWP.exists_left; intro d0; apply SepWP.exists_left; intro d1
  refine SepWP.weaken_pre (by dsimp only [CmdLoopRestNo60]; sep_entail)
    (withCap_moveTo60_wp hCodeInv K.hcCmd K.hext K.hsvc
      (Rest := hbRodata C.hbPl ∗ HbMapMoved C.hbPl A m bm u q0 q1 ∗
        M.Heap γ (baseLc + hbStdoutCost init + hbMapCost A bm) (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) s0 ∗
        HbStdoutInv C M γ init ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbCmdRoData C ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ HbThreadIdInv C s0.tpidrEl0 ∗ (muslErrnoAddr s0 ↦₃₂ e_err) ∗
        memRegion (sp_m + 0x40#64) 8 ∗ ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x58#64) ↦₆₄ c2) ∗
        memRegion (sp_m + 0x98#64) 8 ∗ stackAt sp_m 4432 ∗ F) hpc0 hrun0 hst0 hci0
      fun s1 hpc1 hrun1 hst1 hvm1 hci1 htr1 hlr1 hx0_1 hx21_1 hx22_1 hx26_1 hx27_1 => ?_)
  have htp10 : s1.tpidrEl0 = s0.tpidrEl0 := hst1.2.2.2.1.trans hst0.2.2.2.1.symm
  have hstk_drop := stackAt_split_bottom_of_eq sp_m 4432 MallocngStackBytes 336
  have hrep60 := U64MapRep_repack_qpair C.hbPl A (dst := sp_m + 0x60#64) m bm u q0 q1 h60_al h60_fit
  have hreg20 := qpair_to_memRegion32 (sp_m + 0x20#64) q0 q1
  refine SepWP.weaken_pre (show _ ⊢ U64MapRep C.hbPl A (sp_m + 0x60#64) m bm u ∗ memRegion (sp_m + 0x20#64) 32 ∗
      hbRodata C.hbPl ∗ CmdLoopRestNo60 C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 cap c2 s1 ∗ F from by
    refine Entails.trans ?_ (sepConj_mono hrep60 (sepConj_mono hreg20
      (sepConj_mono_right (sepConj_mono_left (CmdLoopRestNo60.transport htp10 hvm1)))))
    dsimp only [CmdLoopRestNo60]; sep_entail) ?_
  refine call_hbDrop M γ CodeInv hCodeInv (lc0 := baseLc + hbStdoutCost init) (blk0 := baseBlk + hbStdoutBlocks init) (e0 := e_err)
    (F := memRegion (sp_m + 0x20#64) 32 ∗ hbRodata C.hbPl ∗ HbStdoutInv C M γ init ∗
      (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbCmdRoData C ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      HbThreadIdInv C s1.tpidrEl0 ∗ memRegion (sp_m + 0x40#64) 8 ∗ ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ cap) ∗
      ((sp_m + 0x58#64) ↦₆₄ c2) ∗ memRegion (sp_m + 0x98#64) 8 ∗ memRegion (sp_m - BitVec.ofNat 64 4432) 336 ∗ F)
    K.hDrop hci1 hpc1 hrun1 hst1.2.1 hlr1 hx0_1
    (fun R hm => by dsimp only [CmdLoopRestNo60] at hm; rw [hstk_drop] at hm; rw [hst1.1]; exact (by sep_frame : _ → _) hm)
    fun s2 e1 hpc2 hrun2 hsp2 hcs2 halloc2 => ?_
  have hst2 := hst1.of_cs_fs hsp2 halloc2.1 halloc2.2.2.2.1 halloc2.2.2.1 hcs2; have hci2 := hCodeInv halloc2.2.2.2.2 hci1
  refine withCap_prep_wp hCodeInv K.hcCmd K.hext K.hsvc hpc2 hrun2
    hst2.2.2.2.2.2.2.2.2.2.2.2.2 hci2 fun s3 hpc3 hrun3 hcpu3 hvm3 hci3 hlr3 hx0_3 hx8_3 => ?_
  have hst3 := hst2.of_cpu hcpu3; have htp32 : s3.tpidrEl0 = s2.tpidrEl0 := hcpu3.2.2.2.1.1
  have herr23 : muslErrnoAddr s2 = muslErrnoAddr s3 := by simp [muslErrnoAddr, htp32]
  have hstk_wc := stackAt_split_bottom_of_eq sp_m 4432 (80 + MallocngStackBytes) 256
  have hx0_3' : s3.readReg64 .x0 = cap := hx0_3.trans (hcs2.readReg64_x21.trans hx21_1)
  refine SepWP.weaken_pre (show _ ⊢ hbRodata C.hbPl ∗ memRegion (sp_m + 0x60#64) 32 ∗
      M.Heap γ (baseLc + hbStdoutCost init) (baseBlk + hbStdoutBlocks init) s3 ∗ (muslErrnoAddr s3 ↦₃₂ e1) ∗
      stackAt sp_m 4432 ∗ memRegion (sp_m + 0x20#64) 32 ∗ hbRodata C.hbPl ∗ HbStdoutInv C M γ init ∗
      (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbCmdRoData C ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      HbThreadIdInv C s3.tpidrEl0 ∗ memRegion (sp_m + 0x40#64) 8 ∗ ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ cap) ∗
      ((sp_m + 0x58#64) ↦₆₄ c2) ∗ memRegion (sp_m + 0x98#64) 8 ∗ F from by
    rw [hst1.1, ← halloc2.2.2.2.1, ← htp32, herr23]
    have hstk' : memRegion (sp_m - BitVec.ofNat 64 4432) 336 ∗ stackAt sp_m MallocngStackBytes ⊢ stackAt sp_m 4432 := by
      rw [hstk_drop]; exact Entails.refl _
    have hht := M.heap_transport (γ := γ) (lc := baseLc + hbStdoutCost init) (blk := baseBlk + hbStdoutBlocks init)
      hvm3.brk_eq hvm3.brkStart_eq hvm3.physMemAvail_eq hvm3.perm_eq
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono hht
      (sepConj_mono_right (sepConj_mono_left hstk'))))); sep_entail) ?_
  refine call_hbWithCapacityInf M γ CodeInv hCodeInv (lc0 := baseLc + hbStdoutCost init) (blk0 := baseBlk + hbStdoutBlocks init) (e0 := e1)
    (F := memRegion (sp_m + 0x20#64) 32 ∗ hbRodata C.hbPl ∗ HbStdoutInv C M γ init ∗
      (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbCmdRoData C ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      HbThreadIdInv C s3.tpidrEl0 ∗ memRegion (sp_m + 0x40#64) 8 ∗ ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ cap) ∗
      ((sp_m + 0x58#64) ↦₆₄ c2) ∗ memRegion (sp_m + 0x98#64) 8 ∗ memRegion (sp_m - BitVec.ofNat 64 4432) 256 ∗ F)
    K.hWithCap hci3 h60_al h60_fit hcan hpc3 hrun3 hst3.2.1 hlr3 hx0_3' hx8_3
    (fun R hm => by rw [hstk_wc] at hm; rw [hst3.1]; exact (by sep_frame : _ → _) hm)
    fun s4 e2 hpc4 hrun4 hsp4 hcs4 halloc4 => ?_
  have hst4 := hst3.of_cs_fs hsp4 halloc4.1 halloc4.2.2.2.1 halloc4.2.2.1 hcs4; have hci4 := hCodeInv halloc4.2.2.2.2 hci3
  refine SepWP.weaken_pre (by
    dsimp only [CmdLoopRestNo60]; rw [hst3.1, ← halloc4.2.2.2.1]
    have hstk' : memRegion (sp_m - BitVec.ofNat 64 4432) 256 ∗ stackAt sp_m (80 + MallocngStackBytes) ⊢ stackAt sp_m 4432 := by
      rw [hstk_wc]; exact Entails.refl _
    have hro : hbRodata C.hbPl ∗ hbRodata C.hbPl ⊢ hbRodata C.hbPl := by rw [hbRodata_dup_eq]; exact Entails.refl _
    refine Entails.trans ?_ (sepConj_mono hro (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right hstk')))))))))))))))); sep_entail)
    (hNext s4 e2 hpc4 hrun4 hst4 hci4
      (halloc4.2.1.trans (hcpu3.2.2.1.trans (halloc2.2.1.trans htr1)))
      (hcs4.readReg64_x22.trans (hcpu3.2.2.2.2.readReg64_x22.trans (hcs2.readReg64_x22.trans hx22_1)))
      (hcs4.readReg64_x26.trans (hcpu3.2.2.2.2.readReg64_x26.trans (hcs2.readReg64_x26.trans hx26_1)))
      (hcs4.readReg64_x27.trans (hcpu3.2.2.2.2.readReg64_x27.trans (hcs2.readReg64_x27.trans hx27_1))))

private theorem execArm_withCap_wp {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (K : HbCmdCallees C M γ CodeInv hCodeInv)
    {target sp_m nextPtr bm cap c0 c2 : BitVec 64} {hasMore init : Bool} {haveLse : BitVec 8}
    {baseLc baseBlk vecCap u k_ins : Nat} {m : Map64} {e_err : BitVec 32} {s_ref s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hsp_hi : sp_m.toNat + 0x80 ≤ 2 ^ 64)
    (hbaseLc : baseLc ≤ mallocngBlockCost 8192 + hbByteVecCost vecCap) (hbaseBlk : baseBlk ≤ 2)
    (hcap : vecCap ≤ 2 * L + 32) (hcap_le : cap.toNat ≤ MaxWithCapacity)
    (hpc0 : s0.pc = C.std.userMainAddr + 0x2c4#64) (hrun0 : s0.status = .Running)
    (hst0 : CmdLoopState C sp_m s_ref s0) (hci0 : CodeInv s0.mem)
    (hx27_0 : s0.readReg64 .x27 = nextPtr) (hx26_0 : s0.readReg64 .x26 = if hasMore then 0#64 else 1#64)
    (hNext : ∀ (sf : State) (bm' : BitVec 64) (e_err' : BitVec 32),
      sf.pc = (if hasMore then C.std.userMainAddr + 0x184#64 else C.std.userMainAddr + 0x300#64) →
      sf.status = .Running → CmdLoopState C sp_m s_ref sf → CodeInv sf.mem →
      sf.trace = s0.trace → sf.readReg64 .x0 = nextPtr → sf.readReg64 .x22 = s0.readReg64 .x22 →
      (bm' = 0#64 ∨ ValidBucketMask bm') → (bm' ≠ 0#64 → bm'.toNat + 1 ≤ max 8192 (3 * k_ins)) →
      SepWP P target sf (hbRodata C.hbPl ∗
        CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk [] bm' k_ins init e_err' c0 cap c2 sf ∗ F) post) :
    SepWP P target s0 (hbRodata C.hbPl ∗
      CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 cap c2 s0 ∗ F) post := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  obtain ⟨h20_al, h20_fit, _, _⟩ := sp_main_frame_facts hst0.2.1 hst0.1 hsp_hi
  obtain ⟨hbm'_wf, _, hbm'_bnd⟩ := capToBucketMask_wf_of_le_maxWithCap hcap_le
  refine withCap_dropAndAlloc_wp M γ CodeInv hCodeInv K hsp_hi hbaseLc hbaseBlk hcap hcap_le
    hpc0 hrun0 hst0 hci0 fun s4 e2 hpc4 hrun4 hst4 hci4 htr4 hx22_4 hx26_4 hx27_4 => ?_
  let bm' := capToBucketMask cap.toNat
  have hm60 := U64MapRep_unpack_qpair C.hbPl A (sp_m + 0x60#64) [] bm' 0; have hd20 := memRegion32_to_qpair (sp_m + 0x20#64)
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono hm60 (sepConj_mono_left hd20))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro d0'; apply SepWP.exists_left; intro d1'
  apply SepWP.exists_left; intro q0'; apply SepWP.exists_left; intro q1'
  refine SepWP.weaken_pre (by sep_entail)
    (withCap_moveTo20_wp hCodeInv K.hcCmd K.hext K.hsvc
      (Rest := hbRodata C.hbPl ∗ HbMapMoved C.hbPl A [] bm' 0 q0' q1' ∗
        CmdLoopRestNo60 C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm' init e2 c0 cap c2 s4 ∗ F)
      hpc4 hrun4 hst4.1 hst4.2.1 hst4.2.2.2.2.2.2.2.2.2.2.2.2 hci4 fun s5 hpc5 hrun5 hcpu5 hvm5 hci5 => ?_)
  have hst5 := hst4.of_cpu hcpu5
  have hrep20 := Entails.trans (U64MapRep_repack_qpair C.hbPl A (dst := sp_m + 0x20#64) [] bm' 0 q0' q1' h20_al h20_fit)
    (U64MapRep_mono_u C.hbPl A (sp_m + 0x20#64) [] bm' (Nat.zero_le k_ins))
  have hreg60 := qpair_to_memRegion32 (sp_m + 0x60#64) q0' q1'
  refine SepWP.weaken_pre (show _ ⊢ hbRodata C.hbPl ∗
      CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk [] bm' k_ins init e2 c0 cap c2 s5 ∗ F from by
    dsimp only [CmdLoopRes, CmdLoopRest]
    refine Entails.trans (show _ ⊢ ((sp_m + 0x20#64) ↦₁₂₈ q0' ∗ ((sp_m + 0x20#64) + 16#64) ↦₁₂₈ q1' ∗
        HbMapMoved C.hbPl A [] bm' 0 q0' q1') ∗ ((sp_m + 0x60#64) ↦₁₂₈ q0' ∗ ((sp_m + 0x60#64) + 16#64) ↦₁₂₈ q1') ∗
      CmdLoopRestNo60 C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm' init e2 c0 cap c2 s4 ∗ hbRodata C.hbPl ∗ F
      from by sep_entail) ?_
    refine Entails.trans (sepConj_mono hrep20 (sepConj_mono hreg60
      (sepConj_mono_left (CmdLoopRestNo60.transport hcpu5.2.2.2.1.1 hvm5)))) ?_
    dsimp only [CmdLoopRestNo60]; sep_entail) ?_
  exact tailAt0x17c_wp hCodeInv K.hcCmd K.hext K.hsvc
    (Pre := fun st => hbRodata C.hbPl ∗ CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk [] bm' k_ins init e2 c0 cap c2 st ∗ F)
    (fun htp hvm => sepConj_mono_right (sepConj_mono_left (CmdLoopRes.transport htp hvm))) hpc5 hrun5 hst5 hci5
    (hcpu5.2.2.2.2.readReg64_x27.trans (hx27_4.trans hx27_0))
    (hcpu5.2.2.2.2.readReg64_x26.trans (hx26_4.trans hx26_0))
    fun sf hpcf hrunf hstf hcif htrf hx0f hx22f => hNext sf bm' e2 hpcf hrunf hstf hcif
      (htrf.trans (hcpu5.2.2.1.trans htr4)) hx0f (hx22f.trans (hcpu5.2.2.2.2.readReg64_x22.trans hx22_4)) hbm'_wf (hbm'_bnd k_ins)

private theorem CmdLoopRest.of_stdState {P : Program} {L : Nat} {C : HbCliLayout}
    {M : MallocngCoreIface P C.mallocng (hbStdLimits L)} {γ : GhostName} {CodeInv : Memory → Prop}
    {hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2}
    {sp_m : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk : Nat} {bm : BitVec 64} {init : Bool}
    {e_err : BitVec 32} {c0 c1 c2 : BitVec 64} {s sf : State} (hstd : StdStatePreserved s sf) (hfz : s.mem.KeepsFrozen sf.mem) :
    CmdLoopRest C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 c1 c2 s ⊢
    CmdLoopRest C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 c1 c2 sf :=
  CmdLoopRest.transport hstd.2.2.1 ((HbNonVmPreserved.of_stdState hstd hfz).heap_transport M)

private theorem printBoolAndTail_wp {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (K : HbCmdCallees C M γ CodeInv hCodeInv)
    {target sp_m nextPtr off bm : BitVec 64} {b hasMore init : Bool} {haveLse : BitVec 8} {baseLc baseBlk u : Nat}
    {m : Map64} {e_err : BitVec 32} {c0 c1 c2 : BitVec 64} {s_ref s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hoff : off = 0x208#64 ∨ off = 0x298#64)
    (hbudget : 1024 ≤ (hbStdLimits L).maxReq ∧
      (baseLc + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm) + mallocngBlockCost 1024 ≤ (hbStdLimits L).maxPeakCost ∧
      (baseBlk + tableAllocBlocks bm) + 1 ≤ (hbStdLimits L).maxPeakBlocks)
    (hpc0 : s0.pc = C.std.userMainAddr + off) (hrun0 : s0.status = .Running)
    (hst0 : CmdLoopState C sp_m s_ref s0) (hci0 : CodeInv s0.mem) (hx0_0 : s0.readReg64 .x0 = if b then 1#64 else 0#64)
    (hx27_0 : s0.readReg64 .x27 = nextPtr) (hx26_0 : s0.readReg64 .x26 = if hasMore then 0#64 else 1#64)
    (hNext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = (if hasMore then C.std.userMainAddr + 0x184#64 else C.std.userMainAddr + 0x300#64) →
      sf.status = .Running → CmdLoopState C sp_m s_ref sf → CodeInv sf.mem →
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatBoolResult b) →
      sf.readReg64 .x0 = nextPtr → sf.readReg64 .x22 = s0.readReg64 .x22 →
      SepWP P target sf (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u true e1 c0 c1 c2 sf ∗ F) post) :
    SepWP P target s0 (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s0 ∗ F) post := by
  have hbl : (off = 0x208#64 ∧ C.printBoolAddr = C.printBoolAddr) ∨ (off = 0x298#64 ∧ C.printBoolAddr = C.printBoolAddr) ∨
      (off = 0x2a4#64 ∧ C.printBoolAddr = C.printU64Addr) := by rcases hoff with rfl | rfl <;> simp
  have hoff4 : off + 4#64 = 0x20c#64 ∨ off + 4#64 = 0x29c#64 ∨ off + 4#64 = 0x2a8#64 ∨
      off + 4#64 = 0x2b8#64 ∨ off + 4#64 = 0x2c0#64 ∨ off + 4#64 = 0x2fc#64 := by rcases hoff with rfl | rfl <;> decide
  refine bl_print_step_wp hCodeInv K.hcCmd K.hext K.hsvc hbl hpc0 hrun0 hci0
    fun s1 hpc1 hrun1 hcpu1 hvm1 hci1 hlr1 hx0_1 => ?_
  have hst1 := hst0.of_cpu hcpu1
  refine SepWP.weaken_pre (sepConj_mono_left (CmdLoopRes.transport hcpu1.2.2.2.1.1 hvm1)) ?_
  refine call_hbPrintBool_loop M γ CodeInv hCodeInv K.hPrintBool hst1 hci1 (fun _ => hbudget)
    hpc1 hrun1 hlr1 (hx0_1.trans hx0_0) fun s2 e1 hpc2 hrun2 hst2 hcs2 hci2 htr2 => ?_
  exact jumpToTail_wp hCodeInv K.hcCmd K.hext K.hsvc
    (Pre := fun st => CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u true e1 c0 c1 c2 st ∗ F)
    (fun htp hvm => sepConj_mono_left (CmdLoopRes.transport htp hvm)) hoff4 hpc2 hrun2 hst2 hci2
    (hcs2.readReg64_x27.trans (hcpu1.2.2.2.2.readReg64_x27.trans hx27_0))
    (hcs2.readReg64_x26.trans (hcpu1.2.2.2.2.readReg64_x26.trans hx26_0))
    fun sf hpcf hrunf hstf hcif htrf hx0f hx22f => hNext sf e1 hpcf hrunf hstf hcif
      (htrf.trans (htr2.trans (by rw [hcpu1.2.2.1]))) hx0f (hx22f.trans (hcs2.readReg64_x22.trans hcpu1.2.2.2.2.readReg64_x22))

private theorem execArm_get_wp {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (K : HbCmdCallees C M γ CodeInv hCodeInv)
    {target sp_m nextPtr bm k c0 c1 c2 : BitVec 64} {hasMore init : Bool} {haveLse : BitVec 8}
    {baseLc baseBlk u : Nat} {m : Map64} {e_err : BitVec 32} {s_ref s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hsp_lo : 0x310 ≤ sp_m.toNat)
    (hbudget : 1024 ≤ (hbStdLimits L).maxReq ∧
      (baseLc + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm) + mallocngBlockCost 1024 ≤ (hbStdLimits L).maxPeakCost ∧
      (baseBlk + tableAllocBlocks bm) + 1 ≤ (hbStdLimits L).maxPeakBlocks)
    (hpc0 : s0.pc = hashbrownLib.fnAddr C.hbMpl "hashbrown_get") (hrun0 : s0.status = .Running)
    (hst0 : CmdLoopState C sp_m s_ref s0) (hci0 : CodeInv s0.mem) (hlr0 : s0.readReg64 Reg.lr = C.std.userMainAddr + 0x278#64)
    (hx0_0 : s0.readReg64 .x0 = sp_m + 0x20#64) (hx1_0 : s0.readReg64 .x1 = k)
    (hx27_0 : s0.readReg64 .x27 = nextPtr) (hx26_0 : s0.readReg64 .x26 = if hasMore then 0#64 else 1#64)
    (hNext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = (if hasMore then C.std.userMainAddr + 0x184#64 else C.std.userMainAddr + 0x300#64) →
      sf.status = .Running → CmdLoopState C sp_m s_ref sf → CodeInv sf.mem →
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatGetResult (cliMapLookup k m)) →
      sf.readReg64 .x0 = nextPtr → sf.readReg64 .x22 = s0.readReg64 .x22 →
      SepWP P target sf (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u true e1 c0 c1 c2 sf ∗ F) post) :
    SepWP P target s0 (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s0 ∗ F) post := by
  refine call_hbGet K.hGet hci0 hpc0 hrun0 hst0.2.1 hlr0 hx0_0 hx1_0
    (F := CmdLoopRest C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 c1 c2 s0 ∗ F)
    (fun R hm => by dsimp only [CmdLoopRes] at hm; exact (by sep_frame : _ → _) hm)
    fun s1 hpc1 hrun1 hsp1 hcs1 hres1 hstd1 hfz1 => ?_
  have hst1 := hst0.of_cs_fs hsp1 hstd1.1 hstd1.2.2.1 hstd1.2.2.2.1 hcs1; have hci1 := hCodeInv hfz1 hci0
  refine SepWP.weaken_pre (show _ ⊢ CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s1 ∗ F from by
    dsimp only [CmdLoopRes]; exact Entails.trans (by sep_entail)
      (sepConj_mono_left (sepConj_mono_right (CmdLoopRest.of_stdState hstd1 hfz1)))) ?_
  rcases hlk : cliMapLookup k m with _ | v <;> rw [hlk] at hres1
  · refine post_get_none_wp hCodeInv K.hcCmd K.hext K.hsvc hpc1 hrun1 hres1 hci1
      fun s2 hpc2 hrun2 hcpu2 hvm2 hci2 hlr2 hx0_2 hx1_2 => ?_
    have hst2 := hst1.of_cpu hcpu2
    refine SepWP.weaken_pre (sepConj_mono_left (CmdLoopRes.transport hcpu2.2.2.2.1.1 hvm2)) ?_
    refine call_hbPrintNone_loop M γ CodeInv hCodeInv K.hPrintNone hst2 hci2 (fun _ => hbudget)
      hpc2 hrun2 hlr2 (hx0_2.trans hst1.2.2.2.2.2.2.2.1) hx1_2 fun s3 e1 hpc3 hrun3 hst3 hcs3 hci3 htr3 => ?_
    exact jumpToTail_wp hCodeInv K.hcCmd K.hext K.hsvc
      (Pre := fun st => CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u true e1 c0 c1 c2 st ∗ F)
      (fun htp hvm => sepConj_mono_left (CmdLoopRes.transport htp hvm))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hpc3 hrun3 hst3 hci3
      (hcs3.readReg64_x27.trans (hcpu2.2.2.2.2.readReg64_x27.trans (hcs1.readReg64_x27.trans hx27_0)))
      (hcs3.readReg64_x26.trans (hcpu2.2.2.2.2.readReg64_x26.trans (hcs1.readReg64_x26.trans hx26_0)))
      fun sf hpcf hrunf hstf hcif htrf hx0f hx22f => hNext sf e1 hpcf hrunf hstf hcif
        (htrf.trans (htr3.trans (by rw [hlk, hcpu2.2.2.1, hstd1.2.1]))) hx0f
        (hx22f.trans (hcs3.readReg64_x22.trans (hcpu2.2.2.2.2.readReg64_x22.trans hcs1.readReg64_x22)))
  · refine post_get_some_wp hCodeInv K.hcCmd K.hext K.hsvc hpc1 hrun1 hres1.1 hres1.2 hci1
      fun s2 hpc2 hrun2 hcpu2 hvm2 hci2 hlr2 hx0_2 => ?_
    have hst2 := hst1.of_cpu hcpu2
    refine SepWP.weaken_pre (sepConj_mono_left (CmdLoopRes.transport hcpu2.2.2.2.1.1 hvm2)) ?_
    refine call_hbPrintU64_loop M γ CodeInv hCodeInv K.hPrintU64 hst2 hci2 hsp_lo (fun _ => hbudget)
      hpc2 hrun2 hlr2 hx0_2 fun s3 e1 hpc3 hrun3 hst3 hcs3 hci3 htr3 => ?_
    exact jumpToTail_wp hCodeInv K.hcCmd K.hext K.hsvc
      (Pre := fun st => CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u true e1 c0 c1 c2 st ∗ F)
      (fun htp hvm => sepConj_mono_left (CmdLoopRes.transport htp hvm))
      (Or.inr (Or.inr (Or.inl rfl))) hpc3 hrun3 hst3 hci3
      (hcs3.readReg64_x27.trans (hcpu2.2.2.2.2.readReg64_x27.trans (hcs1.readReg64_x27.trans hx27_0)))
      (hcs3.readReg64_x26.trans (hcpu2.2.2.2.2.readReg64_x26.trans (hcs1.readReg64_x26.trans hx26_0)))
      fun sf hpcf hrunf hstf hcif htrf hx0f hx22f => hNext sf e1 hpcf hrunf hstf hcif
        (htrf.trans (htr3.trans (by rw [hlk, hcpu2.2.2.1, hstd1.2.1]))) hx0f
        (hx22f.trans (hcs3.readReg64_x22.trans (hcpu2.2.2.2.2.readReg64_x22.trans hcs1.readReg64_x22)))

private theorem parseAndDispatch_wp {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (K : HbCmdCallees C M γ CodeInv hCodeInv)
    {target sp_m linePtr bm c0 c1 c2 : BitVec 64} {line : List (BitVec 8)} {init : Bool} {haveLse : BitVec 8}
    {baseLc baseBlk u : Nat} {m : Map64} {e_err : BitVec 32} {s_ref s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hptr_nz : linePtr ≠ 0#64) (hptr_fit : linePtr.toNat + line.length < 2 ^ 64)
    (hpc0 : s0.pc = C.std.userMainAddr + 0x1d4#64) (hrun0 : s0.status = .Running)
    (hst0 : CmdLoopState C sp_m s_ref s0) (hci0 : CodeInv s0.mem)
    (hx0_0 : s0.readReg64 .x0 = linePtr) (hx1_0 : s0.readReg64 .x1 = BitVec.ofNat 64 line.length)
    (hNext : ∀ (s3 : State) (c0' c1' c2' : BitVec 64),
      ParseCmdSlot (parseCommand line) c0' c1' c2' →
      s3.pc = dispatchTargetPc C (parseCommand line) → s3.status = .Running → CmdLoopState C sp_m s_ref s3 → CodeInv s3.mem →
      DispatchRegs C sp_m s3 (parseCommand line) → s3.trace = s0.trace → s3.readReg64 .x22 = s0.readReg64 .x22 →
      s3.readReg64 .x26 = s0.readReg64 .x26 → s3.readReg64 .x27 = s0.readReg64 .x27 →
      SepWP P target s3 ((linePtr ↦ₛ line) ∗
        CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0' c1' c2' s3 ∗ F) post) :
    SepWP P target s0 ((linePtr ↦ₛ line) ∗
      CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s0 ∗ F) post := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  let RoTail := (C.falseNlAddr ↦ᵣ falseNlBytes) ∗ (C.trueNlAddr ↦ᵣ trueNlBytes) ∗
    (C.errInvalidCmdAddr ↦ᵣ errInvalidCmdBytes) ∗ (C.noneNlAddr ↦ᵣ noneNlBytes) ∗
    (C.nlByteAddr ↦ᵣ nlByteBytes) ∗ (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    HbAdapterWriteVtableRo C ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ (C.captureUsedAddr ↦₈ᵣ 0#8)
  have hro_eq : HbCmdRoData C = HbParseRoData C ∗ RoTail := rfl
  have hstk_p := stackAt_split_bottom_of_eq sp_m 4432 128 4304
  have h48_8 : (sp_m + 0x48#64) + 8#64 = sp_m + 0x50#64 := by bv_lin
  have h48_16 : (sp_m + 0x48#64) + 16#64 = sp_m + 0x58#64 := by bv_lin
  have hcQ := K.hcCmd.withSvc nonVmSvc
  refine sepWP_cpu_cut (mid := dispatchTargetPc C (parseCommand line)) hCodeInv hci0 K.hext K.hsvc ?_
  refine parse_prep_wp hcQ hpc0 hrun0 hst0.2.2.2.2.2.2.2.2.2.2.2.2 fun s1 hpc1 hrun1 hcpu1 hlr1 hx0_1 hx1_1 hx8_1 => ?_
  have hsp1 : s1.sp = sp_m := hcpu1.1.trans hst0.1
  have hsp_al1 : s1.spAligned = true := by simpa [State.spAligned, hsp1, ← hst0.1] using hst0.2.1
  refine SepWP.weaken_pre (show _ ⊢ (linePtr ↦ₛ line) ∗ ((sp_m + 0x48#64) ↦₆₄ c0) ∗ (((sp_m + 0x48#64) + 8#64) ↦₆₄ c1) ∗
      (((sp_m + 0x48#64) + 16#64) ↦₆₄ c2) ∗ HbParseRoData C ∗ stackAt sp_m 128 ∗ (U64MapRep C.hbPl A (sp_m + 0x20#64) m bm u ∗
       M.Heap γ (baseLc + hbStdoutCost init + hbMapCost A bm) (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) s0 ∗
       HbStdoutInv C M γ init ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ RoTail ∗
       (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ HbThreadIdInv C s0.tpidrEl0 ∗ (muslErrnoAddr s0 ↦₃₂ e_err) ∗
       memRegion (sp_m + 0x40#64) 8 ∗ memRegion (sp_m + 0x60#64) 32 ∗ memRegion (sp_m + 0x98#64) 8 ∗
       memRegion (sp_m - BitVec.ofNat 64 4432) 4304 ∗ F) from by
    dsimp only [CmdLoopRes, CmdLoopRest]; rw [hro_eq, hstk_p, h48_8, h48_16]; sep_entail) ?_
  refine hbParseCommand_wp hcQ hptr_nz hptr_fit hpc1 hrun1 hsp1 hsp_al1 hlr1 (hx0_1.trans hx0_0) (hx1_1.trans hx1_0) hx8_1
    fun s2 c0' c1' c2' hslot hpc2 hrun2 hcpu2 => ?_
  have hcpu02 := hcpu1.trans hcpu2
  refine SepWP.weaken_pre (show _ ⊢ ((sp_m + 0x48#64) ↦₆₄ c0') ∗ ((sp_m + 0x50#64) ↦₆₄ c1') ∗ ((sp_m + 0x58#64) ↦₆₄ c2') ∗
      ((linePtr ↦ₛ line) ∗ U64MapRep C.hbPl A (sp_m + 0x20#64) m bm u ∗
       M.Heap γ (baseLc + hbStdoutCost init + hbMapCost A bm) (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) s0 ∗
       HbStdoutInv C M γ init ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbCmdRoData C ∗
       (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ HbThreadIdInv C s0.tpidrEl0 ∗ (muslErrnoAddr s0 ↦₃₂ e_err) ∗
       memRegion (sp_m + 0x40#64) 8 ∗ memRegion (sp_m + 0x60#64) 32 ∗ memRegion (sp_m + 0x98#64) 8 ∗ stackAt sp_m 4432 ∗ F)
    from by rw [hro_eq, hstk_p, h48_8, h48_16]; sep_entail) ?_
  refine dispatch_slot_wp hcQ hslot hpc2 hrun2 (hcpu02.1.trans hst0.1)
    (hcpu02.2.2.2.2.readReg64_x29.trans hst0.2.2.2.2.2.2.2.2.2.2.2.2)
    fun s3 hpc3 hrun3 hcpu3 hdisp => SepWP.done hpc3 hrun3 fun hvm3 hci3 => ?_
  have hcpu03 := hcpu02.trans hcpu3
  refine SepWP.weaken_pre (show _ ⊢ (linePtr ↦ₛ line) ∗
      CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0' c1' c2' s3 ∗ F from by
    refine Entails.trans (show _ ⊢ (linePtr ↦ₛ line) ∗
        CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0' c1' c2' s0 ∗ F from by
      dsimp only [CmdLoopRes, CmdLoopRest]; sep_entail) ?_
    exact sepConj_mono_right (sepConj_mono_left (CmdLoopRes.transport hcpu03.2.2.2.1.1 hvm3)))
    (hNext s3 c0' c1' c2' hslot hpc3 hrun3 (hst0.of_cpu hcpu03) hci3 hdisp hcpu03.2.2.1
      hcpu03.2.2.2.2.readReg64_x22 hcpu03.2.2.2.2.readReg64_x26 hcpu03.2.2.2.2.readReg64_x27)

private theorem execLine_wp {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (K : HbCmdCallees C M γ CodeInv hCodeInv)
    {target sp_m linePtr nextPtr bm c0 c1 c2 : BitVec 64} {line out0 err0 : List (BitVec 8)} {hasMore init : Bool}
    {haveLse : BitVec 8} {baseLc baseBlk vecCap k_ins : Nat} {m : Map64} {e_err : BitVec 32}
    {s_ref s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hL : L ≤ HashbrownCliMaxStdin) (hsp_lo : 0x310 ≤ sp_m.toNat) (hsp_hi : sp_m.toNat + 0x80 ≤ 2 ^ 64)
    (hbaseLc : baseLc ≤ mallocngBlockCost 8192 + hbByteVecCost vecCap) (hbaseBlk : baseBlk ≤ 2) (hcap : vecCap ≤ 2 * L + 32)
    (hptr_nz : linePtr ≠ 0#64) (hptr_fit : linePtr.toNat + line.length < 2 ^ 64)
    (hins0 : 11 * k_ins ≤ L + 1) (hins_cur : isInsertLine line = true → 11 * (k_ins + 1) ≤ L + 1)
    (hm_len : m.length ≤ k_ins) (hbm_wf : bm = 0#64 ∨ ValidBucketMask bm)
    (hbm_bound : bm ≠ 0#64 → bm.toNat + 1 ≤ max 8192 (3 * k_ins))
    (hpc0 : s0.pc = C.std.userMainAddr + 0x1d4#64) (hrun0 : s0.status = .Running)
    (hst0 : CmdLoopState C sp_m s_ref s0) (hci0 : CodeInv s0.mem)
    (hx0_0 : s0.readReg64 .x0 = linePtr) (hx1_0 : s0.readReg64 .x1 = BitVec.ofNat 64 line.length)
    (hx27_0 : s0.readReg64 .x27 = nextPtr) (hx26_0 : s0.readReg64 .x26 = if hasMore then 0#64 else 1#64)
    (hout0 : ProcessOutcome.traceStreamBytes .stdout s0.trace = out0)
    (herr0 : ProcessOutcome.traceStreamBytes .stderr s0.trace = err0)
    (hNext : ∀ (sf : State) (bm' : BitVec 64) (init' : Bool) (e_err' : BitVec 32) (c0' c1' c2' : BitVec 64),
      let r1 := evalLinesStep (m, out0, err0) line; let k_ins' := k_ins + (if isInsertLine line then 1 else 0)
      sf.pc = (if hasMore then C.std.userMainAddr + 0x184#64 else C.std.userMainAddr + 0x300#64) →
      sf.status = .Running → CmdLoopState C sp_m s_ref sf → CodeInv sf.mem →
      sf.readReg64 .x0 = nextPtr → sf.readReg64 .x22 = s0.readReg64 .x22 →
      ProcessOutcome.traceStreamBytes .stdout sf.trace = r1.2.1 → ProcessOutcome.traceStreamBytes .stderr sf.trace = r1.2.2 →
      11 * k_ins' ≤ L + 1 → r1.1.length ≤ k_ins' → (bm' = 0#64 ∨ ValidBucketMask bm') →
      (bm' ≠ 0#64 → bm'.toNat + 1 ≤ max 8192 (3 * k_ins')) →
      SepWP P target sf ((linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗
        CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk r1.1 bm' k_ins' init' e_err' c0' c1' c2' sf ∗ F) post) :
    SepWP P target s0 ((linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗
      CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm k_ins init e_err c0 c1 c2 s0 ∗ F) post := by
  let k_ins' := k_ins + (if isInsertLine line then 1 else 0)
  have hins' : 11 * k_ins' ≤ L + 1 := by
    dsimp only [k_ins']; cases h : isInsertLine line
    · simpa using hins0
    · exact hins_cur h
  have hmlen' : (evalLinesStep (m, out0, err0) line).1.length ≤ k_ins' :=
    Nat.le_trans (evalLinesStep_mapLength_step (m, out0, err0) line) (Nat.add_le_add_right hm_len _)
  have hbm_mono : bm ≠ 0#64 → bm.toNat + 1 ≤ max 8192 (3 * k_ins') := fun hne =>
    Nat.le_trans (hbm_bound hne) (by dsimp only [k_ins']; omega)
  have hpbud := loop_print_budget M γ CodeInv hCodeInv hL hbaseLc hbaseBlk hcap hins0 hbm_wf hbm_bound
  have hPreRes : ∀ {m1 bm1 u1 i1 e1 a0 a1 a2} {s1 s2 : State}, s2.tpidrEl0 = s1.tpidrEl0 → VmFieldsPreserved s1 s2 →
      (linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗ CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m1 bm1 u1 i1 e1 a0 a1 a2 s1 ∗ F ⊢
      (linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗ CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m1 bm1 u1 i1 e1 a0 a1 a2 s2 ∗ F :=
    fun htp hvm => sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (CmdLoopRes.transport htp hvm)))
  refine SepWP.weaken_pre (by sep_entail)
    (parseAndDispatch_wp M γ CodeInv hCodeInv K (F := hbRodata C.hbPl ∗ F) hptr_nz hptr_fit hpc0 hrun0 hst0 hci0 hx0_0 hx1_0
      fun s3 c0' c1' c2' hslot hpc3 hrun3 hst3 hci3 hdisp htr3 hx22_3 hx26_3 hx27_3 => ?_)
  have hx26_3' := hx26_3.trans hx26_0; have hx27_3' := hx27_3.trans hx27_0
  rcases hcmd : parseCommand line with _ | ⟨k, v⟩ | k | k | k | cap | _ | _ | _ <;>
    rw [hcmd] at hslot hpc3 hdisp <;> dsimp only [dispatchTargetPc, DispatchRegs] at hpc3 hdisp
  · refine SepWP.weaken_pre (by sep_entail)
      (errAt0x220_wp M γ CodeInv hCodeInv K.hcCmd K.hcSys K.hatom K.hv K.hext K.hsvc
        (F := (linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗ F) hpc3 hrun3 hst3 hci3 hx27_3' hx26_3'
        fun sf hpcf hrunf hstf hcif htrf hx0f hx22f =>
          SepWP.weaken_pre (by simp only [evalLinesStep_of_parseCommand_none _ _ _ _ hcmd, isInsertLine, hcmd]; sep_entail)
            (hNext sf bm init e_err c0' c1' c2' hpcf hrunf hstf hcif hx0f (hx22f.trans hx22_3)
              (by simp [htrf, htr3, traceStreamBytes_append, hout0, hcmd])
              (by simp [htrf, htr3, traceStreamBytes_append, herr0, hcmd]) hins' hmlen' hbm_wf hbm_mono))
  · have his : isInsertLine line = true := by simp [isInsertLine, hcmd]
    have hstk_i := stackAt_split_bottom_of_eq sp_m 4432 (176 + MallocngStackBytes) 160
    refine call_hbInsertInf M γ CodeInv hCodeInv (lc0 := baseLc + hbStdoutCost init) (blk0 := baseBlk + hbStdoutBlocks init) (e0 := e_err)
      (F := (linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗ HbStdoutInv C M γ init ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
        HbCmdRoData C ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ HbThreadIdInv C s3.tpidrEl0 ∗ memRegion (sp_m + 0x40#64) 8 ∗
        ((sp_m + 0x48#64) ↦₆₄ c0') ∗ ((sp_m + 0x50#64) ↦₆₄ c1') ∗ ((sp_m + 0x58#64) ↦₆₄ c2') ∗
        memRegion (sp_m + 0x60#64) 32 ∗ memRegion (sp_m + 0x98#64) 8 ∗ memRegion (sp_m - BitVec.ofNat 64 4432) 160 ∗ F)
      K.hIns hci3 (loop_reserve_budget M γ CodeInv hCodeInv hL hbaseLc hbaseBlk hcap (hins_cur his) hm_len hbm_wf hbm_bound)
      hpc3 hrun3 hst3.2.1 hdisp.1 hdisp.2.1 hdisp.2.2.1 hdisp.2.2.2
      (fun R hm => by dsimp only [CmdLoopRes, CmdLoopRest] at hm; rw [hstk_i] at hm; rw [hst3.1]; exact (by sep_frame : _ → _) hm)
      fun s4 bm' e1 hpc4 hrun4 hsp4 hcs4 halloc4 hvmask => ?_
    obtain ⟨hwf', hbnd'⟩ := ValidNextMask.buckets_le_max_three_mul (B := 8192) (by decide) hvmask hbm_wf hbm_bound
    refine SepWP.weaken_pre (show _ ⊢ (linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗
        CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk (cliMapInsert k v m) bm' (k_ins + 1) init e1 c0' c1' c2' s4 ∗ F from by
      dsimp only [CmdLoopRes, CmdLoopRest]; rw [hst3.1, ← halloc4.2.2.2.1, hstk_i]; sep_entail)
      (jumpToTail_wp hCodeInv K.hcCmd K.hext K.hsvc hPreRes (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hpc4 hrun4
        (hst3.of_cs_fs hsp4 halloc4.1 halloc4.2.2.2.1 halloc4.2.2.1 hcs4) (hCodeInv halloc4.2.2.2.2 hci3)
        (hcs4.readReg64_x27.trans hx27_3') (hcs4.readReg64_x26.trans hx26_3')
        fun sf hpcf hrunf hstf hcif htrf hx0f hx22f =>
          SepWP.weaken_pre (by simp only [evalLinesStep_of_parseCommand_insert _ _ _ _ _ _ hcmd, isInsertLine, hcmd]; sep_entail)
            (hNext sf bm' init e1 c0' c1' c2' hpcf hrunf hstf hcif hx0f (hx22f.trans (hcs4.readReg64_x22.trans hx22_3))
              (by simp [evalLinesStep_of_parseCommand_insert _ _ _ _ _ _ hcmd, htrf, halloc4.2.1, htr3, hout0])
              (by simp [evalLinesStep_of_parseCommand_insert _ _ _ _ _ _ hcmd, htrf, halloc4.2.1, htr3, herr0])
              hins' hmlen' hwf' (by simpa [k_ins', his] using hbnd')))
  · exact SepWP.weaken_pre (by sep_entail)
      (execArm_get_wp M γ CodeInv hCodeInv K (F := (linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗ F)
        hsp_lo hpbud hpc3 hrun3 hst3 hci3 hdisp.1 hdisp.2.1 hdisp.2.2 hx27_3' hx26_3'
        fun sf e1 hpcf hrunf hstf hcif htrf hx0f hx22f =>
          SepWP.weaken_pre (by simp only [evalLinesStep_of_parseCommand_get _ _ _ _ _ hcmd, isInsertLine, hcmd]; sep_entail)
            (hNext sf bm true e1 c0' c1' c2' hpcf hrunf hstf hcif hx0f (hx22f.trans hx22_3)
              (by simp [htrf, htr3, traceStreamBytes_append, hout0, hcmd])
              (by simp [htrf, htr3, traceStreamBytes_append, herr0, hcmd]) hins' hmlen' hbm_wf hbm_mono))
  · refine call_hbRemove K.hRem hci3 hpc3 hrun3 hst3.2.1 hdisp.1 hdisp.2.1 hdisp.2.2
      (F := (linePtr ↦ₛ line) ∗ CmdLoopRest C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0' c1' c2' s3 ∗ hbRodata C.hbPl ∗ F)
      (fun R hm => by dsimp only [CmdLoopRes] at hm; exact (by sep_frame : _ → _) hm) fun s4 hpc4 hrun4 hsp4 hcs4 hstd4 hfz4 => ?_
    refine SepWP.weaken_pre (show _ ⊢ (linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗
          CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk (cliMapErase k m) bm k_ins init e_err c0' c1' c2' s4 ∗ F from by
        dsimp only [CmdLoopRes]; refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (CmdLoopRest.of_stdState hstd4 hfz4))))); sep_entail)
      (tailAt0x17c_wp hCodeInv K.hcCmd K.hext K.hsvc hPreRes hpc4 hrun4
        (hst3.of_cs_fs hsp4 hstd4.1 hstd4.2.2.1 hstd4.2.2.2.1 hcs4) (hCodeInv hfz4 hci3)
        (hcs4.readReg64_x27.trans hx27_3') (hcs4.readReg64_x26.trans hx26_3')
        fun sf hpcf hrunf hstf hcif htrf hx0f hx22f =>
          SepWP.weaken_pre (by simp only [evalLinesStep_of_parseCommand_remove _ _ _ _ _ hcmd, isInsertLine, hcmd]; sep_entail)
            (hNext sf bm init e_err c0' c1' c2' hpcf hrunf hstf hcif hx0f (hx22f.trans (hcs4.readReg64_x22.trans hx22_3))
              (by simp [evalLinesStep_of_parseCommand_remove _ _ _ _ _ hcmd, htrf, hstd4.2.1, htr3, hout0])
              (by simp [evalLinesStep_of_parseCommand_remove _ _ _ _ _ hcmd, htrf, hstd4.2.1, htr3, herr0]) hins' hmlen' hbm_wf hbm_mono))
  · refine call_hbContainsKey K.hContains hci3 hpc3 hrun3 hst3.2.1 hdisp.1 hdisp.2.1 hdisp.2.2
      (F := (linePtr ↦ₛ line) ∗ CmdLoopRest C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0' c1' c2' s3 ∗ hbRodata C.hbPl ∗ F)
      (fun R hm => by dsimp only [CmdLoopRes] at hm; exact (by sep_frame : _ → _) hm) fun s4 hpc4 hrun4 hsp4 hcs4 hres4 hstd4 hfz4 => ?_
    refine SepWP.weaken_pre (show _ ⊢ CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm k_ins init e_err c0' c1' c2' s4 ∗
          ((linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗ F) from by
        dsimp only [CmdLoopRes]; refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_right (CmdLoopRest.of_stdState hstd4 hfz4))); sep_entail)
      (printBoolAndTail_wp M γ CodeInv hCodeInv K (Or.inr rfl) hpbud hpc4 hrun4
        (hst3.of_cs_fs hsp4 hstd4.1 hstd4.2.2.1 hstd4.2.2.2.1 hcs4) (hCodeInv hfz4 hci3) hres4
        (hcs4.readReg64_x27.trans hx27_3') (hcs4.readReg64_x26.trans hx26_3')
        fun sf e1 hpcf hrunf hstf hcif htrf hx0f hx22f =>
          SepWP.weaken_pre (by simp only [evalLinesStep_of_parseCommand_contains _ _ _ _ _ hcmd, isInsertLine, hcmd]; sep_entail)
            (hNext sf bm true e1 c0' c1' c2' hpcf hrunf hstf hcif hx0f (hx22f.trans (hcs4.readReg64_x22.trans hx22_3))
              (by simp [htrf, hstd4.2.1, htr3, traceStreamBytes_append, hout0, hcmd])
              (by simp [htrf, hstd4.2.1, htr3, traceStreamBytes_append, herr0, hcmd]) hins' hmlen' hbm_wf hbm_mono))
  · rcases hslot with ⟨_, rfl, hcap_le⟩; exact SepWP.weaken_pre (by sep_entail)
      (execArm_withCap_wp M γ CodeInv hCodeInv K (k_ins := k_ins') (F := (linePtr ↦ₛ line) ∗ F)
        hsp_hi hbaseLc hbaseBlk hcap hcap_le hpc3 hrun3 hst3 hci3 hx27_3' hx26_3'
        fun sf bm' e1 hpcf hrunf hstf hcif htrf hx0f hx22f hwf' hbnd' =>
          SepWP.weaken_pre (by simp only [evalLinesStep_of_parseCommand_withCapacity _ _ _ _ _ hcmd]; sep_entail)
            (hNext sf bm' init e1 c0' c1' c2' hpcf hrunf hstf hcif hx0f (hx22f.trans hx22_3)
              (by simp [evalLinesStep_of_parseCommand_withCapacity _ _ _ _ _ hcmd, htrf, htr3, hout0])
              (by simp [evalLinesStep_of_parseCommand_withCapacity _ _ _ _ _ hcmd, htrf, htr3, herr0]) hins' hmlen' hwf' hbnd'))
  · refine call_hbLen K.hLen hci3 hpc3 hrun3 hst3.2.1 hdisp.1 hdisp.2
      (F := (linePtr ↦ₛ line) ∗ CmdLoopRest C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0' c1' c2' s3 ∗ hbRodata C.hbPl ∗ F)
      (fun R hm => by dsimp only [CmdLoopRes] at hm; exact (by sep_frame : _ → _) hm) fun s4 hpc4 hrun4 hsp4 hcs4 hres4 hstd4 hfz4 => ?_
    have hst4 := hst3.of_cs_fs hsp4 hstd4.1 hstd4.2.2.1 hstd4.2.2.2.1 hcs4
    refine bl_print_step_wp hCodeInv K.hcCmd K.hext K.hsvc (Or.inr (Or.inr ⟨rfl, rfl⟩)) hpc4 hrun4 (hCodeInv hfz4 hci3)
      fun s5 hpc5 hrun5 hcpu5 hvm5 hci5 hlr5 hx0_5 => ?_
    refine SepWP.weaken_pre (show _ ⊢ CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm k_ins init e_err c0' c1' c2' s5 ∗
          ((linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗ F) from by
        refine Entails.trans (show _ ⊢ CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm k_ins init e_err c0' c1' c2' s4 ∗
            ((linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗ F) from by
          dsimp only [CmdLoopRes]; refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_right (CmdLoopRest.of_stdState hstd4 hfz4))); sep_entail)
          (sepConj_mono_left (CmdLoopRes.transport hcpu5.2.2.2.1.1 hvm5))) ?_
    refine call_hbPrintU64_loop M γ CodeInv hCodeInv K.hPrintU64 (hst4.of_cpu hcpu5) hci5 hsp_lo (fun _ => hpbud)
      hpc5 hrun5 hlr5 (hx0_5.trans hres4) fun s6 e1 hpc6 hrun6 hst6 hcs6 hci6 htr6 => ?_
    exact jumpToTail_wp hCodeInv K.hcCmd K.hext K.hsvc
      (Pre := fun st => CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm k_ins true e1 c0' c1' c2' st ∗ ((linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗ F))
      (fun htp hvm => sepConj_mono_left (CmdLoopRes.transport htp hvm)) (Or.inr (Or.inr (Or.inl rfl))) hpc6 hrun6 hst6 hci6
      (hcs6.readReg64_x27.trans (hcpu5.2.2.2.2.readReg64_x27.trans (hcs4.readReg64_x27.trans hx27_3')))
      (hcs6.readReg64_x26.trans (hcpu5.2.2.2.2.readReg64_x26.trans (hcs4.readReg64_x26.trans hx26_3')))
      fun sf hpcf hrunf hstf hcif htrf hx0f hx22f =>
        SepWP.weaken_pre (by simp only [evalLinesStep_of_parseCommand_len _ _ _ _ hcmd, isInsertLine, hcmd]; sep_entail)
          (hNext sf bm true e1 c0' c1' c2' hpcf hrunf hstf hcif hx0f
            (hx22f.trans (hcs6.readReg64_x22.trans (hcpu5.2.2.2.2.readReg64_x22.trans (hcs4.readReg64_x22.trans hx22_3))))
            (by rw [evalLinesStep_of_parseCommand_len _ _ _ _ hcmd, htrf, htr6, hcpu5.2.2.1, hstd4.2.1, htr3,
                    traceStreamBytes_append, traceStreamBytes_stdout_ofBytes, hout0]; exact formatGetResult_len_eq m out0 hL hins0 hm_len)
            (by simp [htrf, htr6, hcpu5.2.2.1, hstd4.2.1, htr3, traceStreamBytes_append, herr0, hcmd]) hins' hmlen' hbm_wf hbm_mono)
  · refine call_hbIsEmpty K.hIsEmpty hci3 hpc3 hrun3 hst3.2.1 hdisp.1 hdisp.2
      (F := (linePtr ↦ₛ line) ∗ CmdLoopRest C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0' c1' c2' s3 ∗ hbRodata C.hbPl ∗ F)
      (fun R hm => by dsimp only [CmdLoopRes] at hm; exact (by sep_frame : _ → _) hm) fun s4 hpc4 hrun4 hsp4 hcs4 hres4 hstd4 hfz4 => ?_
    refine SepWP.weaken_pre (show _ ⊢ CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm k_ins init e_err c0' c1' c2' s4 ∗
          ((linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗ F) from by
        dsimp only [CmdLoopRes]; refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_right (CmdLoopRest.of_stdState hstd4 hfz4))); sep_entail)
      (printBoolAndTail_wp M γ CodeInv hCodeInv K (Or.inl rfl) hpbud hpc4 hrun4
        (hst3.of_cs_fs hsp4 hstd4.1 hstd4.2.2.1 hstd4.2.2.2.1 hcs4) (hCodeInv hfz4 hci3) hres4
        (hcs4.readReg64_x27.trans hx27_3') (hcs4.readReg64_x26.trans hx26_3')
        fun sf e1 hpcf hrunf hstf hcif htrf hx0f hx22f =>
          SepWP.weaken_pre (by simp only [evalLinesStep_of_parseCommand_isEmpty _ _ _ _ hcmd, isInsertLine, hcmd]; sep_entail)
            (hNext sf bm true e1 c0' c1' c2' hpcf hrunf hstf hcif hx0f (hx22f.trans (hcs4.readReg64_x22.trans hx22_3))
              (by simp [htrf, hstd4.2.1, htr3, traceStreamBytes_append, hout0, hcmd])
              (by simp [htrf, hstd4.2.1, htr3, traceStreamBytes_append, herr0, hcmd]) hins' hmlen' hbm_wf hbm_mono))
  · have hstk_c := stackAt_split_bottom_of_eq sp_m 4432 32 4400
    refine call_hbClear K.hClear hci3 hpc3 hrun3 hst3.2.1 hdisp.1 hdisp.2
      (F := (linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗
        M.Heap γ (baseLc + hbStdoutCost init + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm) (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) s3 ∗
        HbStdoutInv C M γ init ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbCmdRoData C ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ HbThreadIdInv C s3.tpidrEl0 ∗ (muslErrnoAddr s3 ↦₃₂ e_err) ∗
        memRegion (sp_m + 0x40#64) 8 ∗ ((sp_m + 0x48#64) ↦₆₄ c0') ∗ ((sp_m + 0x50#64) ↦₆₄ c1') ∗
        ((sp_m + 0x58#64) ↦₆₄ c2') ∗ memRegion (sp_m + 0x60#64) 32 ∗ memRegion (sp_m + 0x98#64) 8 ∗
        memRegion (sp_m - BitVec.ofNat 64 4432) 4400 ∗ F)
      (fun R hm => by dsimp only [CmdLoopRes, CmdLoopRest] at hm; rw [hstk_c] at hm; rw [hst3.1]; exact (by sep_frame : _ → _) hm)
      fun s4 hpc4 hrun4 hsp4 hcs4 hstd4 hfz4 => ?_
    have herr34 : muslErrnoAddr s3 = muslErrnoAddr s4 := by simp [muslErrnoAddr, hstd4.2.2.1]
    have hht := (HbNonVmPreserved.of_stdState hstd4 hfz4).heap_transport M (γ := γ)
      (lc := baseLc + hbStdoutCost init + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm) (blk := baseBlk + hbStdoutBlocks init + tableAllocBlocks bm)
    refine SepWP.weaken_pre (show _ ⊢ (linePtr ↦ₛ line) ∗ hbRodata C.hbPl ∗
        CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk [] bm k_ins init e_err c0' c1' c2' s4 ∗ F from by
      dsimp only [CmdLoopRes, CmdLoopRest]; rw [hst3.1, ← hstd4.2.2.1, herr34, hstk_c]
      exact Entails.trans (by sep_entail)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hht))))))
      (jumpToTail_wp hCodeInv K.hcCmd K.hext K.hsvc hPreRes (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hpc4 hrun4
        (hst3.of_cs_fs hsp4 hstd4.1 hstd4.2.2.1 hstd4.2.2.2.1 hcs4) (hCodeInv hfz4 hci3)
        (hcs4.readReg64_x27.trans hx27_3') (hcs4.readReg64_x26.trans hx26_3')
        fun sf hpcf hrunf hstf hcif htrf hx0f hx22f =>
          SepWP.weaken_pre (by simp only [evalLinesStep_of_parseCommand_clear _ _ _ _ hcmd, isInsertLine, hcmd]; sep_entail)
            (hNext sf bm init e_err c0' c1' c2' hpcf hrunf hstf hcif hx0f (hx22f.trans (hcs4.readReg64_x22.trans hx22_3))
              (by simp [evalLinesStep_of_parseCommand_clear _ _ _ _ hcmd, htrf, hstd4.2.1, htr3, hout0])
              (by simp [evalLinesStep_of_parseCommand_clear _ _ _ _ hcmd, htrf, hstd4.2.1, htr3, herr0]) hins' hmlen' hbm_wf hbm_mono))

private theorem tableDrop_wp {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (K : HbCmdCallees C M γ CodeInv hCodeInv)
    {target sp_m bm : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk u : Nat} {m : Map64} {init : Bool}
    {e_err : BitVec 32} {c0 c1 c2 : BitVec 64} {s_ref s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hsp_hi : sp_m.toNat + 0x80 ≤ 2 ^ 64) (hpc0 : s0.pc = C.std.userMainAddr + 0x300#64) (hrun0 : s0.status = .Running)
    (hst0 : CmdLoopState C sp_m s_ref s0) (hci0 : CodeInv s0.mem)
    (hNext : ∀ (sf : State) (e_err' : BitVec 32), sf.pc = C.std.userMainAddr + 0x310#64 → sf.status = .Running →
      CmdLoopState C sp_m s_ref sf → CodeInv sf.mem → sf.trace = s0.trace →
      SepWP P target sf ((M.Heap γ (baseLc + hbStdoutCost init) (baseBlk + hbStdoutBlocks init) sf ∗
        HbStdoutInv C M γ init ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ hbRodata C.hbPl ∗ HbCmdRoData C ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ HbThreadIdInv C sf.tpidrEl0 ∗ (muslErrnoAddr sf ↦₃₂ e_err') ∗
        memRegion (sp_m + 0x98#64) 8 ∗ stackAt (sp_m + 0x80#64) 96 ∗ stackAt sp_m 4432) ∗ F) post) :
    SepWP P target s0 (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s0 ∗ F) post := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  obtain ⟨_, _, h60_al, h60_fit⟩ := sp_main_frame_facts hst0.2.1 hst0.1 hsp_hi
  refine SepWP.weaken_pre (sepConj_mono_left cmdLoopRes_unpack_qpairs) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro q0; apply SepWP.exists_left; intro q1
  apply SepWP.exists_left; intro d0; apply SepWP.exists_left; intro d1
  refine SepWP.weaken_pre (by sep_entail)
    (tableDrop_moveTo60_wp hCodeInv K.hcCmd K.hext K.hsvc
      (Rest := HbMapMoved C.hbPl A m bm u q0 q1 ∗ CmdLoopRestNo60 C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 c1 c2 s0 ∗ F)
      hpc0 hrun0 hst0.1 hst0.2.1 hst0.2.2.2.2.2.2.2.2.2.2.2.2 hci0 fun s1 hpc1 hrun1 hcpu1 hvm1 hci1 hlr1 hx0_1 => ?_)
  have hst1 := hst0.of_cpu hcpu1; have hstk_drop := stackAt_split_bottom_of_eq sp_m 4432 MallocngStackBytes 336
  have hrep60 := U64MapRep_repack_qpair C.hbPl A (dst := sp_m + 0x60#64) m bm u q0 q1 h60_al h60_fit
  have hreg20 := qpair_to_memRegion32 (sp_m + 0x20#64) q0 q1
  refine SepWP.weaken_pre (show _ ⊢ U64MapRep C.hbPl A (sp_m + 0x60#64) m bm u ∗ memRegion (sp_m + 0x20#64) 32 ∗
      CmdLoopRestNo60 C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 c1 c2 s1 ∗ F from by
    refine Entails.trans ?_ (sepConj_mono hrep60 (sepConj_mono hreg20 (sepConj_mono_left (CmdLoopRestNo60.transport hcpu1.2.2.2.1.1 hvm1)))); sep_entail) ?_
  refine call_hbDrop M γ CodeInv hCodeInv (lc0 := baseLc + hbStdoutCost init) (blk0 := baseBlk + hbStdoutBlocks init) (e0 := e_err)
    (F := memRegion (sp_m + 0x20#64) 32 ∗ HbStdoutInv C M γ init ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbCmdRoData C ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ HbThreadIdInv C s1.tpidrEl0 ∗ memRegion (sp_m + 0x40#64) 8 ∗
      ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ c1) ∗ ((sp_m + 0x58#64) ↦₆₄ c2) ∗
      memRegion (sp_m + 0x98#64) 8 ∗ memRegion (sp_m - BitVec.ofNat 64 4432) 336 ∗ F)
    K.hDrop hci1 hpc1 hrun1 hst1.2.1 hlr1 hx0_1
    (fun R hm => by dsimp only [CmdLoopRestNo60] at hm; rw [hstk_drop] at hm; rw [hst1.1]; exact (by sep_frame : _ → _) hm)
    fun sf e1 hpcf hrunf hspf hcsf halloc => ?_
  have hstf := hst1.of_cs_fs hspf halloc.1 halloc.2.2.2.1 halloc.2.2.1 hcsf; have hcif := hCodeInv halloc.2.2.2.2 hci1
  refine SepWP.weaken_pre (by
    rw [hst1.1, ← halloc.2.2.2.1]
    have hstk' : memRegion (sp_m - BitVec.ofNat 64 4432) 336 ∗ stackAt sp_m MallocngStackBytes ⊢ stackAt sp_m 4432 := by
      rw [hstk_drop]; exact Entails.refl _
    refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono (mainLocal96_repack sp_m c0 c1 c2) hstk'))))))))))); sep_entail)
    (hNext sf e1 hpcf hrunf hstf hcif (halloc.2.1.trans hcpu1.2.2.1))

private theorem cmdLoop_ind_wp {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (K : HbCmdCallees C M γ CodeInv hCodeInv)
    {target sp_m remPtr bm c0 c1 c2 : BitVec 64} {core remBytes out0 err0 : List (BitVec 8)}
    {doneLines remLines : List (List (BitVec 8))} {init : Bool} {haveLse : BitVec 8}
    {baseLc baseBlk vecCap : Nat} {m : Map64} {e_err : BitVec 32} {s_ref s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hL : L ≤ HashbrownCliMaxStdin) (hsp_lo : 0x310 ≤ sp_m.toNat) (hsp_hi : sp_m.toNat + 0x80 ≤ 2 ^ 64)
    (hbaseLc : baseLc ≤ mallocngBlockCost 8192 + hbByteVecCost vecCap) (hbaseBlk : baseBlk ≤ 2)
    (hcap : vecCap ≤ 2 * L + 32) (hcore_le : core.length ≤ L)
    (hsplit_all : splitOnByte 0x0a#8 core = doneLines ++ remLines) (hsplit_rem : splitOnByte 0x0a#8 remBytes = remLines)
    (hptr_nz : remPtr ≠ 0#64) (hptr_fit : remPtr.toNat + remBytes.length < 2 ^ 64)
    (hins0 : 11 * (doneLines.filter isInsertLine).length ≤ L + 1)
    (hm_len : m.length ≤ (doneLines.filter isInsertLine).length) (hbm_wf : bm = 0#64 ∨ ValidBucketMask bm)
    (hbm_bound : bm ≠ 0#64 → bm.toNat + 1 ≤ max 8192 (3 * (doneLines.filter isInsertLine).length))
    (hpc0 : s0.pc = C.std.userMainAddr + 0x184#64) (hrun0 : s0.status = .Running)
    (hst0 : CmdLoopState C sp_m s_ref s0) (hci0 : CodeInv s0.mem)
    (hx0_0 : s0.readReg64 .x0 = remPtr) (hx22_0 : s0.readReg64 .x22 = BitVec.ofNat 64 remBytes.length)
    (hout0 : ProcessOutcome.traceStreamBytes .stdout s0.trace = out0) (herr0 : ProcessOutcome.traceStreamBytes .stderr s0.trace = err0)
    (hNext : ∀ (sf : State) (bm' : BitVec 64) (u_f : Nat) (init' : Bool) (e_err' : BitVec 32) (c0' c1' c2' : BitVec 64),
      let r := remLines.foldl evalLinesStep (m, out0, err0)
      sf.pc = C.std.userMainAddr + 0x300#64 → sf.status = .Running → CmdLoopState C sp_m s_ref sf → CodeInv sf.mem →
      ProcessOutcome.traceStreamBytes .stdout sf.trace = r.2.1 → ProcessOutcome.traceStreamBytes .stderr sf.trace = r.2.2 →
      SepWP P target sf ((remPtr ↦ₛ remBytes) ∗ hbRodata C.hbPl ∗
        CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk r.1 bm' u_f init' e_err' c0' c1' c2' sf ∗ F) post) :
    SepWP P target s0 ((remPtr ↦ₛ remBytes) ∗ hbRodata C.hbPl ∗
      CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm (doneLines.filter isInsertLine).length init e_err c0 c1 c2 s0 ∗ F) post := by
  induction remLines generalizing remBytes remPtr doneLines bm init e_err c0 c1 c2 m out0 err0 s0 F with
  | nil => exact False.elim (splitOnByte_ne_nil 0x0a#8 remBytes hsplit_rem)
  | cons curLine tailLines ih =>
    have hins_cur : isInsertLine curLine = true → 11 * ((doneLines.filter isInsertLine).length + 1) ≤ L + 1 :=
      fun hc => Nat.le_trans (splitOnByte_insertCount_bound hsplit_all hc) (Nat.add_le_add_right hcore_le 1)
    have hfilt_step : ((doneLines ++ [curLine]).filter isInsertLine).length =
        (doneLines.filter isInsertLine).length + (if isInsertLine curLine then 1 else 0) := by
      cases h : isInsertLine curLine <;> simp [List.filter_append, h]
    refine sepWP_cpu_cut (mid := C.std.userMainAddr + 0x1d4#64) hCodeInv hci0 K.hext K.hsvc ?_
    refine nlScan_wp (K.hcCmd.withSvc nonVmSvc) hptr_nz hptr_fit hpc0 hrun0 hx0_0 hx22_0 ?_ ?_
    · intro s1 k cL rB nP hk hsplit_f hcur_fit hnext_nz hnext_fit hpc1 hrun1 hnl1 hx0_1 hx1_1 hx26_1 hx27_1 hx22_1
      dsimp only [cL, rB, nP] at *
      obtain ⟨htake, hdrop_split⟩ := List.cons.inj (hsplit_f.symm.trans hsplit_rem)
      refine SepWP.done hpc1 hrun1 fun hvm1 hci1 => ?_
      refine SepWP.weaken_pre (show _ ⊢ (remPtr ↦ₛ curLine) ∗ hbRodata C.hbPl ∗
          CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm (doneLines.filter isInsertLine).length init e_err c0 c1 c2 s1 ∗
          (((remPtr + BitVec.ofNat 64 k) ↦₈ 0x0a#8) ∗ ((remPtr + BitVec.ofNat 64 (k + 1)) ↦ₛ remBytes.drop (k + 1)) ∗ F) from by
        rw [htake]; refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (CmdLoopRes.transport hnl1.2.2.2.1.1 hvm1)))); sep_entail) ?_
      exact execLine_wp M γ CodeInv hCodeInv K (hasMore := true) hL hsp_lo hsp_hi hbaseLc hbaseBlk hcap
        hptr_nz (by rwa [← htake]) hins0 hins_cur hm_len hbm_wf hbm_bound hpc1 hrun1 (hst0.of_nlScan hnl1)
        hci1 hx0_1 (by rwa [← htake]) hx27_1 (by simpa using hx26_1) (by simp [hnl1.2.2.1, hout0]) (by simp [hnl1.2.2.1, herr0])
        fun s2 bm1 init1 e1 c0_1 c1_1 c2_1 hpc2 hrun2 hst2 hci2 hx0_2 hx22_2 hout2 herr2 hins1 hmlen1 hwf1 hbnd1 =>
          let r1 := evalLinesStep (m, out0, err0) curLine
          SepWP.weaken_pre (by rw [← hfilt_step]; sep_entail)
            (ih (doneLines := doneLines ++ [curLine]) (m := r1.1) (out0 := r1.2.1) (err0 := r1.2.2)
              (F := (remPtr ↦ₛ curLine) ∗ ((remPtr + BitVec.ofNat 64 k) ↦₈ 0x0a#8) ∗ F)
              (by simpa [List.append_assoc] using hsplit_all) hdrop_split hnext_nz hnext_fit
              (by rwa [hfilt_step]) (by rwa [hfilt_step]) hwf1 (by rwa [hfilt_step])
              hpc2 hrun2 hst2 hci2 hx0_2 (hx22_2.trans hx22_1) hout2 herr2
              fun sf bm' u_f init' e_err' c0' c1' c2' hpcf hrunf hstf hcif houtf herrf =>
                SepWP.weaken_pre (by rw [pointsToBytes_focus8 remPtr remBytes k hk,
                    splitOnByte_getD_eq_sep 0x0a#8 k remBytes hk hsplit_f, htake]; sep_entail)
                  (hNext sf bm' u_f init' e_err' c0' c1' c2' hpcf hrunf hstf hcif houtf herrf))
    · intro s1 hsplit_e hpc1 hrun1 hnl1 hx0_1 hx1_1 hx26_1 hx27_1
      obtain ⟨hrem_eq, htail_eq⟩ := List.cons.inj (hsplit_e.symm.trans hsplit_rem); subst hrem_eq; cases htail_eq
      refine SepWP.done hpc1 hrun1 fun hvm1 hci1 => SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (CmdLoopRes.transport hnl1.2.2.2.1.1 hvm1)))) ?_
      exact execLine_wp M γ CodeInv hCodeInv K (hasMore := false) hL hsp_lo hsp_hi hbaseLc hbaseBlk hcap
        hptr_nz hptr_fit hins0 hins_cur hm_len hbm_wf hbm_bound hpc1 hrun1 (hst0.of_nlScan hnl1)
        hci1 hx0_1 hx1_1 hx27_1 (by simpa using hx26_1) (by simp [hnl1.2.2.1, hout0]) (by simp [hnl1.2.2.1, herr0])
        fun sf bm' init' e_err' c0' c1' c2' hpcf hrunf hstf hcif _ _ houtf herrf _ _ _ _ =>
          hNext sf bm' _ init' e_err' c0' c1' c2' hpcf hrunf hstf hcif houtf herrf

/-- Continuation-passing `SepWP` specification for `hashbrown_cli::main` from `u + 0x13c`
    (`hashbrown_new` setup) through `u + 0x310` (`hashbrown_drop` return). -/
theorem hbMain_cmdLoop_wp {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (K : HbCmdCallees C M γ CodeInv hCodeInv)
    {target sp_m vecPtr : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk vecCap : Nat} {core : List (BitVec 8)}
    {init0 : Bool} {e_err0 : BitVec 32} {s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hL : L ≤ HashbrownCliMaxStdin) (hsp_lo : 0x310 ≤ sp_m.toNat) (hsp_hi : sp_m.toNat + 0x80 ≤ 2 ^ 64)
    (hbaseLc : baseLc ≤ mallocngBlockCost 8192 + hbByteVecCost vecCap) (hbaseBlk : baseBlk ≤ 2)
    (hcap : vecCap ≤ 2 * L + 32) (hcore_le : core.length ≤ L) (hvec_nz : vecPtr ≠ 0#64) (hvec_fit : vecPtr.toNat + core.length < 2 ^ 64)
    (hpc0 : s0.pc = C.std.userMainAddr + 0x13c#64) (hrun0 : s0.status = .Running)
    (hsp0 : s0.sp = sp_m) (hsp_al0 : s0.spAligned = true) (hci0 : CodeInv s0.mem)
    (hx9_0 : s0.readReg64 .x9 = vecPtr) (hx22_0 : s0.readReg64 .x22 = BitVec.ofNat 64 core.length) (hx29_0 : s0.readReg64 .x29 = sp_m + 0x80#64)
    (hNext : ∀ (sf : State) (init' : Bool) (e_err' : BitVec 32), let res := evalLines (splitOnByte 0x0a#8 core)
      sf.pc = C.std.userMainAddr + 0x310#64 → sf.status = .Running → sf.sp = sp_m → sf.spAligned = true →
      sf.fs = s0.fs → sf.tpidrEl0 = s0.tpidrEl0 → sf.sigActions = s0.sigActions → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 .x28 = s0.readReg64 .x28 → sf.readReg64 .x29 = sp_m + 0x80#64 → CodeInv sf.mem →
      ProcessOutcome.traceStreamBytes .stdout sf.trace = ProcessOutcome.traceStreamBytes .stdout s0.trace ++ res.1 →
      ProcessOutcome.traceStreamBytes .stderr sf.trace = ProcessOutcome.traceStreamBytes .stderr s0.trace ++ res.2 →
      SepWP P target sf (((vecPtr ↦ₛ core) ∗ M.Heap γ (baseLc + hbStdoutCost init') (baseBlk + hbStdoutBlocks init') sf ∗
        HbStdoutInv C M γ init' ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ hbRodata C.hbPl ∗ HbCmdRoData C ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ HbThreadIdInv C sf.tpidrEl0 ∗ (muslErrnoAddr sf ↦₃₂ e_err') ∗
        memRegion (sp_m + 0x98#64) 8 ∗ stackAt (sp_m + 0x80#64) 96 ∗ stackAt sp_m 4432) ∗ F) post) :
    SepWP P target s0 (((vecPtr ↦ₛ core) ∗ M.Heap γ (baseLc + hbStdoutCost init0) (baseBlk + hbStdoutBlocks init0) s0 ∗
      HbStdoutInv C M γ init0 ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ hbRodata C.hbPl ∗ HbCmdRoData C ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ HbThreadIdInv C s0.tpidrEl0 ∗ (muslErrnoAddr s0 ↦₃₂ e_err0) ∗
      memRegion (sp_m + 0x98#64) 8 ∗ stackAt (sp_m + 0x80#64) 96 ∗ stackAt sp_m 4432) ∗ F) post := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  obtain ⟨h20_al, h20_fit, _, _⟩ := sp_main_frame_facts hsp_al0 hsp0 hsp_hi
  conv => arg 4; rw [mainLocal96_eq sp_m]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro c0; apply SepWP.exists_left; intro c1; apply SepWP.exists_left; intro c2
  refine init_pre_new_wp hCodeInv K.hcCmd K.hext K.hsvc hpc0 hrun0 hci0
    fun s1 hpc1 hrun1 hsp1 hal1 hfs1 htr1 htp1 hsig1 hv1 hvm1 hci1 hlr1 hx8_1 hx19_1 hx22_1 hx28_1 hx29_1 => ?_
  have hmc0 : hbMapCost A 0#64 = 0 := by simp [hbMapCost]
  have htb0 : tableAllocBlocks 0#64 = 0 := by simp [tableAllocBlocks]
  have herr01 : muslErrnoAddr s0 = muslErrnoAddr s1 := by simp [muslErrnoAddr, htp1]
  have hht01 := M.heap_transport (γ := γ) (lc := baseLc + hbStdoutCost init0) (blk := baseBlk + hbStdoutBlocks init0)
    hvm1.brk_eq hvm1.brkStart_eq hvm1.physMemAvail_eq hvm1.perm_eq
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hht01))) ?_
  refine call_hbNew K.hNew hci1 h20_al h20_fit hpc1 hrun1 (hal1.trans hsp_al0) hlr1 (hx8_1.trans (by rw [hsp0]))
    (F := (vecPtr ↦ₛ core) ∗ CmdLoopRest C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk 0#64 init0 e_err0 c0 c1 c2 s1 ∗ F)
    (fun R hm => by dsimp only [CmdLoopRest]; rw [hmc0, htb0, Nat.add_zero, Nat.add_zero, htp1, ← herr01]; exact (by sep_frame : _ → _) hm)
    fun s2 hpc2 hrun2 hsp2 hcs2 hstd2 hfz2 => ?_
  refine SepWP.weaken_pre (show _ ⊢ (vecPtr ↦ₛ core) ∗ hbRodata C.hbPl ∗
      CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk [] 0#64 0 init0 e_err0 c0 c1 c2 s2 ∗ F from by
    dsimp only [CmdLoopRes]; refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (CmdLoopRest.of_stdState hstd2 hfz2))))); sep_entail) ?_
  refine init_post_new_wp hCodeInv (s_ref := s0) K.hcCmd K.hext K.hsvc
    (Pre := fun st => (vecPtr ↦ₛ core) ∗ hbRodata C.hbPl ∗ CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk [] 0#64 0 init0 e_err0 c0 c1 c2 st ∗ F)
    (fun htp hvm => sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (CmdLoopRes.transport htp hvm))))
    hpc2 hrun2 (hsp2.trans (hsp1.trans hsp0)) (by simpa [State.spAligned, hsp2] using hal1.trans hsp_al0)
    (hstd2.1.trans hfs1) (hstd2.2.2.1.trans htp1) (hstd2.2.2.2.1.trans hsig1) (hcs2.vregs.trans hv1)
    (hcs2.readReg64_x19.trans (hx19_1.trans hx9_0)) (hcs2.readReg64_x28.trans hx28_1)
    (hcs2.readReg64_x29.trans (hx29_1.trans hx29_0)) (hCodeInv hfz2 hci1)
    fun s3 hpc3 hrun3 hst3 hci3 htr3 hx0_3 hx22_3 => ?_
  have htr30 : s3.trace = s0.trace := htr3.trans (hstd2.2.1.trans htr1)
  refine cmdLoop_ind_wp M γ CodeInv hCodeInv K (doneLines := []) (remLines := splitOnByte 0x0a#8 core)
    hL hsp_lo hsp_hi hbaseLc hbaseBlk hcap hcore_le rfl rfl hvec_nz hvec_fit (Nat.zero_le _) (Nat.le_refl 0)
    (Or.inl rfl) (fun h => False.elim (h rfl)) hpc3 hrun3 hst3 hci3 hx0_3
    (hx22_3.trans (hcs2.readReg64_x22.trans (hx22_1.trans hx22_0))) rfl rfl
    fun s4 bm' u_f init' e4 c0' c1' c2' hpc4 hrun4 hst4 hci4 hout4 herr4 => ?_
  refine SepWP.weaken_pre (by sep_entail)
    (tableDrop_wp M γ CodeInv hCodeInv K (F := (vecPtr ↦ₛ core) ∗ hbRodata C.hbPl ∗ F) hsp_hi hpc4 hrun4 hst4 hci4
      fun sf e_err' hpcf hrunf hstf hcif htrf => ?_)
  have hpre := evalLinesStep_foldl_prefix (splitOnByte 0x0a#8 core) []
    (ProcessOutcome.traceStreamBytes .stdout s0.trace) (ProcessOutcome.traceStreamBytes .stderr s0.trace) [] []
  simp only [List.append_nil] at hpre
  refine SepWP.weaken_pre (by
      refine Entails.trans (show _ ⊢ (hbRodata C.hbPl ∗ hbRodata C.hbPl) ∗
          ((vecPtr ↦ₛ core) ∗ M.Heap γ (baseLc + hbStdoutCost init') (baseBlk + hbStdoutBlocks init') sf ∗
           HbStdoutInv C M γ init' ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbCmdRoData C ∗
           (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ HbThreadIdInv C sf.tpidrEl0 ∗ (muslErrnoAddr sf ↦₃₂ e_err') ∗
           memRegion (sp_m + 0x98#64) 8 ∗ stackAt (sp_m + 0x80#64) 96 ∗ stackAt sp_m 4432 ∗ F) from by sep_entail) ?_
      rw [hbRodata_dup_eq C.hbPl]; sep_entail)
    (hNext sf init' e_err' hpcf hrunf hstf.1 hstf.2.1 hstf.2.2.1 hstf.2.2.2.1 hstf.2.2.2.2.1
      hstf.2.2.2.2.2.1 hstf.2.2.2.2.2.2.2.2.2.2.2.1 hstf.2.2.2.2.2.2.2.2.2.2.2.2 hcif
      (by rw [htrf, hout4, htr30, evalLines_eq_foldl, hpre]) (by rw [htrf, herr4, htr30, evalLines_eq_foldl, hpre]))

end CaseStudies.Hashbrown.Proofs.StdCli
