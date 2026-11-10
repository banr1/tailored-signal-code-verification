/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec.CoreMemrchr
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
import VerifiedLibraries.RustStd.Proofs.Wave1.CoreMemrchr
import VerifiedLibraries.RustStd.Proofs.Wave1.CoreMemrchrLemmas
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Read-Only `core::slice::memchr::memrchr` Hook Discharge (`HookDischarge.RustStd.MemrchrRO`)

Real-code proof that `rustc 1.98.1`'s `aarch64-unknown-linux-musl` `core::slice::memchr::memrchr`
(`coreMemrchrWords`, the 65 reachable relocation-free 32-bit instruction words `[0x00 .. 0x100]` of
`coreMultiLib` block `2`, allocating a 16 B stack frame) satisfies the read-only haystack contract
`CalleesRO.memrchrSpecRO stk` and `withVmPreserved (memrchrSpecRO stk)` whenever
`16 ≤ stk ∧ stk ≤ 2 ^ 64`, plus `coreMultiLib` (`MultiPlacedLib`) and ideal-hook (`toSat`) bridges.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement MultiPlacedLib patchRelocs)
open VerifiedLibraries.RustStd (coreMultiLib coreMemrchrSym cmNoSvc0_2
  sepWP_seg_rebase_pure SameCpuState lastIndexOf
  NoMatchFrom noMatchFrom_self noMatchFrom_step_one noMatchFrom_step_one_sub
  noMatchFrom_step_chunk16 memrchrLastIdx_eq_none memrchrLastIdx_eq_some_of_hit
  memrchrRepeatByte64 lowByte_mov_and_ff memrchrSwarBics_eq_zero_iff
  memrchrHeadBV memrchrHeadBV_lt8 memrchrHeadBV_eq_ofNat
  sub32_zext64_and15_eq ofNat_sub_and15_eq_mod16 memrchr_split_of_ge
  memrchr_prefix_check_false memrchr_loop1_ptr_eq memrchr_loop1_hit_idx
  memrchr_loop2_ptr_eq memrchr_loop3_ptr_eq)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsMemrchrSym memrchrHook)
open CryptoVerification.SignalSession.Cli.MainHops (MemrchrCall cliExternsPlaced_memrchr memrchrIdx)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.Fine (VmPreserved.of_eq hookOk_withVmPreserved hookSat_of_hookOk)
open LibsignalBinary.Heap.SpecBudget (subroutine_ok_of_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (memrchrHook_ro_ok
  memrchrHook_vmPreserved memrchrSpecRO pointsToBytesRO_focus8)

/-! ## 1. Reachable Relocation-Free `core::slice::memchr::memrchr` Words (`65` Words = `260` B) -/

/-- Exact 65 reachable 32-bit AArch64 instruction words (`260` bytes, offsets `0 .. 256`) of
    `core::slice::memchr::memrchr` in `VerifiedLibraries.RustStd.coreMultiLib` block `2`
    (`rustc 1.98.1` `aarch64-unknown-linux-musl` `libcore`). Offsets `260 .. 292` in block `2` are
    the two unreachable `slice_index_fail` panic blocks guarded by false bounds checks at `+0x34`
    and `+0xcc`. -/
@[expose] def coreMemrchrWords : List (BitVec 32) := [
  0xa9bf7bfd#32, 0x910003fd#32, 0x91001c29#32, 0x2a0003e8#32, 0xaa0203e0#32, 0x927df129#32,
  0xaa0203ea#32, 0xcb010129#32, 0xeb09005f#32, 0x540000c3#32, 0x4b09004a#32, 0x92400d4a#32,
  0xeb0a0040#32, 0x54000723#32, 0xaa0903ea#32, 0x8b01004c#32, 0xaa1f03eb#32, 0x12001d09#32,
  0xcb000048#32, 0xd100058c#32, 0xeb0b011f#32, 0x54000120#32, 0x385ff58d#32, 0x9100056b#32,
  0x6b0901bf#32, 0x54ffff61#32, 0xcb0b0041#32, 0x52800020#32, 0xa8c17bfd#32, 0xd65f03c0#32,
  0xb200c3e8#32, 0xb200c3ec#32, 0xb201c3ed#32, 0x9b087d2b#32, 0xf280200c#32, 0xaa0003e8#32,
  0xeb0a001f#32, 0x540001a9#32, 0x8b08002e#32, 0xd1004100#32, 0xa97f39cf#32, 0xca0b01ef#32,
  0xca0b01ce#32, 0xcb0f0190#32, 0xcb0e0191#32, 0xaa0f020f#32, 0xaa0e022e#32, 0x8a0e01ee#32,
  0xea2e01bf#32, 0x54fffe40#32, 0xeb02011f#32, 0x540001c8#32, 0xd100042a#32, 0x52800020#32,
  0xb4000108#32, 0x3868694b#32, 0xd1000501#32, 0xaa0103e8#32, 0x6b09017f#32, 0x54ffff61#32,
  0xa8c17bfd#32, 0xd65f03c0#32, 0xaa1f03e0#32, 0xa8c17bfd#32, 0xd65f03c0#32
]

/-- `VerifiedLibraries.RustStd.lastIndexOf` is definitionally `MainHops.memrchrIdx`. -/
theorem lastIndexOf_eq_memrchrIdx (c : BitVec 8) (bs : List (BitVec 8)) :
    lastIndexOf c bs = memrchrIdx c bs := rfl

/-! ## 2. Read-Only Slice Focus & Pure Segment Preservation Invariants -/

private theorem cmFocus8RO (p : BitVec 64) (bs : List (BitVec 8)) (idx : Nat)
    (hidx : idx < bs.length) :
    (p ↦ᵣ bs) =
      ((p + BitVec.ofNat 64 idx) ↦₈ᵣ bs.getD idx 0#8) ∗
      ((p ↦ᵣ bs.take idx) ∗ ((p + BitVec.ofNat 64 idx + 1#64) ↦ᵣ bs.drop (idx + 1))) := by
  rw [pointsToBytesRO_focus8 p hidx, List.getElem_eq_getD]

private theorem pointsToBytesRO_focus16_words (p : BitVec 64) (bs : List (BitVec 8)) {cur : Nat}
    (h16 : 16 ≤ cur) (hcur : cur ≤ bs.length) :
    ∃ w0 w1 : BitVec 64,
      (bs.drop (cur - 16)).take 16 = unpack64 w0 ++ unpack64 w1 ∧
      (p ↦ᵣ bs) =
        ((p + BitVec.ofNat 64 (cur - 16)) ↦₆₄ᵣ w0) ∗
        (((p + BitVec.ofNat 64 (cur - 16)) + 8#64) ↦₆₄ᵣ w1) ∗
        ((p ↦ᵣ bs.take (cur - 16)) ∗
         ((p + BitVec.ofNat 64 cur) ↦ᵣ bs.drop cur)) := by
  have hlen16 : ((bs.drop (cur - 16)).take 16).length = 16 := by simp; omega
  obtain ⟨w0, w1, hchunk, _⟩ := exists_unpack64_of_length_16 hlen16
  refine ⟨w0, w1, hchunk, ?_⟩
  have hsplit := pointsToBytesRO_split3 p bs (cur - 16) 16 (by omega)
  have hcur_eq : cur - 16 + 16 = cur := by omega
  rw [hcur_eq] at hsplit
  rw [hsplit, hchunk, pointsToBytesRO_append,
      show (unpack64 w0).length = 8 from rfl, show BitVec.ofNat 64 8 = 8#64 from rfl,
      ← pointsTo64RO_eq_pointsToBytesRO, ← pointsTo64RO_eq_pointsToBytesRO]
  sep_ac_rfl

private theorem vmPreserved_setMem_of_perm {s s' : State} {m : Memory}
    (hp : m.perm = s'.mem.perm) (h : VmPreserved s s') :
    VmPreserved s (s'.setMem m) :=
  h.trans ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun a => by
    have ha := congrFun hp a
    cases s'; exact ha, fun _ _ _ => by cases s'; rfl⟩

private theorem step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post) :
    SepWP prog target_pc s P post := by
  unfold SepWP; intro R hm
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm
  have hm2 := hstore2.store hm1
  have hcan1 := hstore1.writable hm
  have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s =
      ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  have hn := hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))
  unfold SepWP at hn
  exact hn R hm2

section
arm64_proof_prelude

private def CmSavedGprs (s0 s1 : State) : Prop :=
  s1.readReg64 .x19 = s0.readReg64 .x19 ∧ s1.readReg64 .x20 = s0.readReg64 .x20 ∧
  s1.readReg64 .x21 = s0.readReg64 .x21 ∧ s1.readReg64 .x22 = s0.readReg64 .x22 ∧
  s1.readReg64 .x23 = s0.readReg64 .x23 ∧ s1.readReg64 .x24 = s0.readReg64 .x24 ∧
  s1.readReg64 .x25 = s0.readReg64 .x25 ∧ s1.readReg64 .x26 = s0.readReg64 .x26 ∧
  s1.readReg64 .x27 = s0.readReg64 .x27 ∧ s1.readReg64 .x28 = s0.readReg64 .x28

private theorem CmSavedGprs.trans {s0 s1 s2 : State}
    (a : CmSavedGprs s0 s1) (b : CmSavedGprs s1 s2) : CmSavedGprs s0 s2 :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.1.trans a.2.2.2.1,
   b.2.2.2.2.1.trans a.2.2.2.2.1, b.2.2.2.2.2.1.trans a.2.2.2.2.2.1,
   b.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.2.1,
   b.2.2.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2.2.2.trans a.2.2.2.2.2.2.2.2.2⟩

private structure CmBodyPreserved (s_entry s : State) (sp0 : BitVec 64) : Prop where
  running : s.status = .Running
  sp_eq : s.sp = sp0 - 16#64
  sp_al : s.spAligned = true
  gprs : CmSavedGprs s_entry s
  vregs : calleeSavedVRegs s = calleeSavedVRegs s_entry
  trace_eq : s.trace = s_entry.trace
  fs_eq : s.fs = s_entry.fs
  vm : VmPreserved s_entry s

private structure CmExitState (s_entry sf : State) (sp0 fp0 lr0 : BitVec 64)
    (c : BitVec 8) (bs : List (BitVec 8)) : Prop where
  pc_eq : sf.pc = lr0
  running : sf.status = .Running
  sp_eq : sf.sp = sp0
  fp_eq : sf.readReg64 .fp = fp0
  lr_eq : sf.readReg64 .lr = lr0
  gprs : CmSavedGprs s_entry sf
  vregs : calleeSavedVRegs sf = calleeSavedVRegs s_entry
  trace_eq : sf.trace = s_entry.trace
  fs_eq : sf.fs = s_entry.fs
  vm : VmPreserved s_entry sf
  ret_ok : RustAbi.optionU64.holds sf ((lastIndexOf c bs).map (BitVec.ofNat 64))

private abbrev cmFrameRO (p sp0 fp0 lr0 : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (p ↦ᵣ bs) ∗ ((sp0 - 16#64) ↦₆₄ fp0) ∗ ((sp0 - 8#64) ↦₆₄ lr0)

private theorem stackFrameAt16_eq_pair (sp0 : BitVec 64) :
    stackFrameAt sp0 16 =
      ∃∗ st0, ∃∗ st1, ((sp0 - 16#64) ↦₆₄ st0) ∗ ((sp0 - 8#64) ↦₆₄ st1) := by
  rw [← stackAt_eq_stackFrameAt sp0 16, stackAt_eq_cells sp0 2]
  dsimp only [cells]
  simp only [Nat.reduceMul, sepConj_emp, sepExists_sepConj_right, bv_lin_norm]

private theorem byte_cmp32_of_eq {x y : BitVec 8} (h : x = y) :
    (BitVec.setWidth 32 x == BitVec.setWidth 32 y) = true ∧
    (BitVec.setWidth 32 x != BitVec.setWidth 32 y) = false := by
  subst h; simp

private theorem byte_cmp32_of_ne {x y : BitVec 8} (h : x ≠ y) :
    (BitVec.setWidth 32 x == BitVec.setWidth 32 y) = false ∧
    (BitVec.setWidth 32 x != BitVec.setWidth 32 y) = true := by
  have hne32 : BitVec.setWidth 32 x ≠ BitVec.setWidth 32 y := by
    intro heq
    apply h
    have h8 := congrArg (BitVec.setWidth 8) heq
    simpa using h8
  exact ⟨beq_false_of_ne hne32, bne_iff_ne.mpr hne32⟩

/-! ## 3. Loop 3 (`+0xd8`): Reverse Prefix Byte Scan (`↦ᵣ`) -/

private theorem cmLoop3RO {prog : Program} {fnBase : BitVec 64}
    (hc : prog.hasCode fnBase coreMemrchrWords)
    {s_entry : State} {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)}
    {post : State → SepProp → Prop}
    (hn : bs.length < 2 ^ 64)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrameRO p sp0 fp0 lr0 bs)) :
    ∀ (cur : Nat) (s : State),
      cur ≤ bs.length →
      s.pc = fnBase + 216#64 →
      CmBodyPreserved s_entry s sp0 →
      s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 cur →
      s.readReg64 (.gpr 10#5) = p - 1#64 →
      s.readReg64 .x0 = 1#64 →
      s.readReg64 (.gpr 9#5) = c.zeroExtend 64 →
      NoMatchFrom c bs cur →
      SepWP prog lr0 s (cmFrameRO p sp0 fp0 lr0 bs) post
  | 0, s, _hcur, hpc, hpres, hx8, _hx10, _hx0, _hx9, hnomatch => by
    have hnone : lastIndexOf c bs = none := memrchrLastIdx_eq_none hnomatch
    have hrun := hpres.running
    have hsp := hpres.sp_eq
    have hsp_al := hpres.sp_al
    have hsp0_al : (sp0 &&& 15#64 == 0#64) = true := by
      have h1 : (sp0 - 16#64) &&& 15#64 = 0#64 := by simpa [State.spAligned, hsp] using hsp_al
      exact beq_iff_eq.mpr (by simpa [arm64_norm] using h1)
    wp_conv_pre => rw [cmFrameRO]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact hpost _ ⟨rfl, by simpa [arm64_norm] using hrun,
      by simp [arm64_norm],
      by simp [arm64_norm],
      by simp [arm64_norm],
      CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
      (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
      by simpa [arm64_norm] using hpres.trace_eq,
      by simpa [arm64_norm] using hpres.fs_eq,
      by simpa [arm64_norm] using hpres.vm,
      by simp [hnone, RustAbi.optionU64, arm64_norm]⟩
  | idx + 1, s, hcur, hpc, hpres, hx8, hx10, hx0, hx9, hnomatch => by
    have hidx : idx < bs.length := by omega
    have hne0 : BitVec.ofNat 64 (idx + 1) ≠ 0#64 := by bv_omega
    have hbeq0 : (BitVec.ofNat 64 (idx + 1) == 0#64) = false := beq_false_of_ne hne0
    obtain ⟨hptr, hsub1⟩ := memrchr_loop3_ptr_eq p idx
    have hrun := hpres.running
    have hsp := hpres.sp_eq
    have hsp_al := hpres.sp_al
    by_cases hbc : bs.getD idx 0#8 = c
    · have hsome : lastIndexOf c bs = some idx := memrchrLastIdx_eq_some_of_hit hidx hbc hnomatch
      obtain ⟨hcmp_eq, hcmp_ne⟩ := byte_cmp32_of_eq hbc
      have hsp0_al : (sp0 &&& 15#64 == 0#64) = true := by
        have h1 : (sp0 - 16#64) &&& 15#64 = 0#64 := by simpa [State.spAligned, hsp] using hsp_al
        exact beq_iff_eq.mpr (by simpa [arm64_norm] using h1)
      wp_conv_pre => rw [cmFrameRO, cmFocus8RO p bs idx hidx, ← hptr, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      conv => arg 2; rw [hptr, ← sepConj_assoc, ← cmFocus8RO p bs idx hidx]
      exact hpost _ ⟨rfl, by simpa [arm64_norm] using hrun,
        by simp [arm64_norm],
        by simp [arm64_norm],
        by simp [arm64_norm],
        CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
        (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
        by simpa [arm64_norm] using hpres.trace_eq,
        by simpa [arm64_norm] using hpres.fs_eq,
        by simpa [arm64_norm] using hpres.vm,
        by simp [hsome, RustAbi.optionU64, arm64_norm, hx0]⟩
    · have hnomatch' : NoMatchFrom c bs idx := noMatchFrom_step_one hidx hbc hnomatch
      obtain ⟨hcmp_eq, hcmp_ne⟩ := byte_cmp32_of_ne hbc
      apply SepWP.cut (mid := fnBase + 216#64)
      wp_conv_pre => rw [cmFrameRO, cmFocus8RO p bs idx hidx, ← hptr, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr, ← sepConj_assoc, ← cmFocus8RO p bs idx hidx]
      exact cmLoop3RO hc hn hpost idx _ (by omega) rfl
        ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
         by simpa [arm64_norm] using hsp_al,
         CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
         (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
         by simpa [arm64_norm] using hpres.trace_eq,
         by simpa [arm64_norm] using hpres.fs_eq,
         by simpa [arm64_norm] using hpres.vm⟩
        (by simp [arm64_norm])
        (by simp [arm64_norm, hx10])
        (by simp [arm64_norm, hx0])
        (by simp [arm64_norm, hx9])
        hnomatch'

/-! ## 4. Post-SWAR Bounds Check (`+0xc8 → +0xd8`) & Loop 2 (`+0x8c`): 16-Byte GPR SWAR Scan -/

private theorem cmAfterLoop2RO {prog : Program} {fnBase : BitVec 64}
    (hc : prog.hasCode fnBase coreMemrchrWords)
    {s_entry s : State} {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)}
    {cur : Nat} {post : State → SepProp → Prop}
    (hn : bs.length < 2 ^ 64)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrameRO p sp0 fp0 lr0 bs))
    (hcur : cur ≤ bs.length)
    (hpc : s.pc = fnBase + 200#64)
    (hpres : CmBodyPreserved s_entry s sp0)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 cur)
    (hx1 : s.readReg64 .x1 = p)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hx9 : s.readReg64 (.gpr 9#5) = c.zeroExtend 64)
    (hnomatch : NoMatchFrom c bs cur) :
    SepWP prog lr0 s (cmFrameRO p sp0 fp0 lr0 bs) post := by
  obtain ⟨hhi_false, hule_true⟩ := memrchr_prefix_check_false hcur hn
  have hrun := hpres.running
  have hsp := hpres.sp_eq
  have hsp_al := hpres.sp_al
  apply SepWP.cut (mid := fnBase + 216#64)
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  exact cmLoop3RO hc hn hpost cur _ hcur rfl
    ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
     by simpa [arm64_norm] using hsp_al,
     CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
     (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
     by simpa [arm64_norm] using hpres.trace_eq,
     by simpa [arm64_norm] using hpres.fs_eq,
     by simpa [arm64_norm] using hpres.vm⟩
    (by simp [arm64_norm, hx8])
    (by simp [arm64_norm])
    (by simp [arm64_norm])
    (by simp [arm64_norm, hx9])
    hnomatch

private theorem cmLoop2RO {prog : Program} {fnBase : BitVec 64}
    (hc : prog.hasCode fnBase coreMemrchrWords)
    {s_entry : State} {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)}
    {lo : Nat} {post : State → SepProp → Prop}
    (hn : bs.length < 2 ^ 64)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrameRO p sp0 fp0 lr0 bs)) :
    ∀ (q : Nat) (s : State),
      lo + 16 * q ≤ bs.length →
      s.pc = fnBase + 140#64 →
      CmBodyPreserved s_entry s sp0 →
      s.readReg64 .x0 = BitVec.ofNat 64 (lo + 16 * q) →
      s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 lo →
      s.readReg64 .x1 = p →
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length →
      s.readReg64 (.gpr 9#5) = c.zeroExtend 64 →
      s.readReg64 (.gpr 11#5) = memrchrRepeatByte64 c →
      s.readReg64 (.gpr 12#5) = 72340172838076672#64 →
      s.readReg64 (.gpr 13#5) = 9259542123273814144#64 →
      NoMatchFrom c bs (lo + 16 * q) →
      SepWP prog lr0 s (cmFrameRO p sp0 fp0 lr0 bs) post
  | 0, s, hcur, hpc, hpres, hx0, hx10, hx1, hx2, hx9, _hx11, _hx12, _hx13, hnomatch => by
    simp only [Nat.mul_zero, Nat.add_zero] at hcur hx0 hnomatch
    have hrun := hpres.running
    have hsp := hpres.sp_eq
    have hsp_al := hpres.sp_al
    apply SepWP.cut (mid := fnBase + 200#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact cmAfterLoop2RO hc hn hpost hcur rfl
      ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
       by simpa [arm64_norm] using hsp_al,
       CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
       (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
       by simpa [arm64_norm] using hpres.trace_eq,
       by simpa [arm64_norm] using hpres.fs_eq,
       by simpa [arm64_norm] using hpres.vm⟩
      (by simp [arm64_norm])
      (by simp [arm64_norm, hx1])
      (by simp [arm64_norm, hx2])
      (by simp [arm64_norm, hx9])
      hnomatch
  | q' + 1, s, hcur, hpc, hpres, hx0, hx10, hx1, hx2, hx9, hx11, hx12, hx13, hnomatch => by
    let cur := lo + 16 * (q' + 1)
    have h16 : 16 ≤ cur := by dsimp [cur]; omega
    have hcur_lt : cur < 2 ^ 64 := by dsimp [cur] at *; omega
    have hcur_sub16 : cur - 16 = lo + 16 * q' := by dsimp [cur]; omega
    have hls_false : (BitVec.ofNat 64 cur).ule (BitVec.ofNat 64 lo) = false := by
      simp [BitVec.ule, BitVec.toNat_ofNat]
      dsimp [cur]; omega
    have hgt_true : (BitVec.ofNat 64 lo).ult (BitVec.ofNat 64 cur) = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat]
      dsimp [cur]; omega
    obtain ⟨hptr16, hsub16⟩ := memrchr_loop2_ptr_eq p h16 hcur_lt
    obtain ⟨w0, w1, hchunk, hfocus⟩ := pointsToBytesRO_focus16_words p bs h16 hcur
    have hrun := hpres.running
    have hsp := hpres.sp_eq
    have hsp_al := hpres.sp_al
    let rep := memrchrRepeatByte64 c
    let u0 := w0 ^^^ rep
    let u1 := w1 ^^^ rep
    let swarFlags :=
      9259542123273814144#64 &&&
        ~~~(((72340172838076672#64 - u0) ||| u0) &&& ((72340172838076672#64 - u1) ||| u1))
    by_cases hswar : swarFlags = 0#64
    · have hswar_beq : (swarFlags == 0#64) = true := beq_iff_eq.mpr hswar
      obtain ⟨hw0, hw1⟩ := (memrchrSwarBics_eq_zero_iff w0 w1 c).mp hswar
      have hnomatch' : NoMatchFrom c bs (lo + 16 * q') := by
        rw [← hcur_sub16]
        exact noMatchFrom_step_chunk16 h16 hcur hchunk hw0 hw1 hnomatch
      apply SepWP.cut (mid := fnBase + 140#64)
      wp_conv_pre => rw [cmFrameRO, hfocus, ← hptr16, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← sepConj_assoc, hptr16, ← hfocus]
      exact cmLoop2RO hc hn hpost q' _ (by omega) rfl
        ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
         by simpa [arm64_norm] using hsp_al,
         CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
         (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
         by simpa [arm64_norm] using hpres.trace_eq,
         by simpa [arm64_norm] using hpres.fs_eq,
         by simpa [arm64_norm] using hpres.vm⟩
        (by simp [arm64_norm, hsub16, hcur_sub16, cur])
        (by simp [arm64_norm, hx10])
        (by simp [arm64_norm, hx1])
        (by simp [arm64_norm, hx2])
        (by simp [arm64_norm, hx9])
        (by simp [arm64_norm, hx11])
        (by simp [arm64_norm, hx12])
        (by simp [arm64_norm, hx13])
        hnomatch'
    · have hswar_beq : (swarFlags == 0#64) = false := beq_false_of_ne hswar
      apply SepWP.cut (mid := fnBase + 200#64)
      wp_conv_pre => rw [cmFrameRO, hfocus, ← hptr16, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← sepConj_assoc, hptr16, ← hfocus]
      exact cmAfterLoop2RO hc hn hpost hcur rfl
        ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
         by simpa [arm64_norm] using hsp_al,
         CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
         (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
         by simpa [arm64_norm] using hpres.trace_eq,
         by simpa [arm64_norm] using hpres.fs_eq,
         by simpa [arm64_norm] using hpres.vm⟩
        (by simp [arm64_norm])
        (by simp [arm64_norm, hx1])
        (by simp [arm64_norm, hx2])
        (by simp [arm64_norm, hx9])
        hnomatch

/-! ## 5. Loop 1 (`+0x50`), Join (`+0x3c`), & Prologue (`+0x00 .. +0x38`) -/

private theorem cmLoop1RO {prog : Program} {fnBase : BitVec 64}
    (hc : prog.hasCode fnBase coreMemrchrWords)
    {s_entry : State} {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)}
    {lo mid q : Nat} {post : State → SepProp → Prop}
    (hn : bs.length < 2 ^ 64)
    (hmid_eq : mid = lo + 16 * q)
    (hmid_le : mid ≤ bs.length)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrameRO p sp0 fp0 lr0 bs)) :
    ∀ (rem k : Nat) (s : State),
      rem + k = bs.length - mid →
      s.pc = fnBase + 80#64 →
      CmBodyPreserved s_entry s sp0 →
      s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (bs.length - mid) →
      s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 k →
      s.readReg64 (.gpr 12#5) = (p + BitVec.ofNat 64 bs.length - 1#64) - BitVec.ofNat 64 k →
      s.readReg64 (.gpr 9#5) = c.zeroExtend 64 →
      s.readReg64 .x0 = BitVec.ofNat 64 mid →
      s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 lo →
      s.readReg64 .x1 = p →
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length →
      NoMatchFrom c bs (bs.length - k) →
      SepWP prog lr0 s (cmFrameRO p sp0 fp0 lr0 bs) post
  | 0, k, s, hrem, hpc, hpres, hx8, hx11, _hx12, hx9, hx0, hx10, hx1, hx2, hnomatch => by
    have hk_eq : k = bs.length - mid := by omega
    subst hk_eq
    have hsub_mid : bs.length - (bs.length - mid) = mid := by omega
    rw [hsub_mid] at hnomatch
    have hrun := hpres.running
    have hsp := hpres.sp_eq
    have hsp_al := hpres.sp_al
    apply SepWP.cut (mid := fnBase + 140#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact cmLoop2RO hc hn hpost q _ (hmid_eq ▸ hmid_le) rfl
      ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
       by simpa [arm64_norm] using hsp_al,
       CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
       (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
       by simpa [arm64_norm] using hpres.trace_eq,
       by simpa [arm64_norm] using hpres.fs_eq,
       by simpa [arm64_norm] using hpres.vm⟩
      (by simp [arm64_norm, hx0, hmid_eq])
      (by simp [arm64_norm, hx10])
      (by simp [arm64_norm, hx1])
      (by simp [arm64_norm, hx2])
      (by simp [arm64_norm, hx9])
      (by simp [arm64_norm, memrchrRepeatByte64])
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (hmid_eq ▸ hnomatch)
  | rem' + 1, k, s, hrem, hpc, hpres, hx8, hx11, hx12, hx9, hx0, hx10, hx1, hx2, hnomatch => by
    have hk_lt_sub : k < bs.length - mid := by omega
    have hk_lt_n : k < bs.length := by omega
    let idx := bs.length - 1 - k
    have hidx : idx < bs.length := by dsimp [idx]; omega
    have hne_k : BitVec.ofNat 64 (bs.length - mid) ≠ BitVec.ofNat 64 k := by bv_omega
    have hbeq_k : (BitVec.ofNat 64 (bs.length - mid) == BitVec.ofNat 64 k) = false :=
      beq_false_of_ne hne_k
    have hptr := memrchr_loop1_ptr_eq p hk_lt_n hn
    have hhit_idx := memrchr_loop1_hit_idx hk_lt_n hn
    rw [BitVec.ofNat_add] at hhit_idx
    have hrun := hpres.running
    have hsp := hpres.sp_eq
    have hsp_al := hpres.sp_al
    by_cases hbc : bs.getD idx 0#8 = c
    · have habove_idx : NoMatchFrom c bs (idx + 1) := by
        have heq : idx + 1 = bs.length - k := by dsimp [idx]; omega
        exact heq ▸ hnomatch
      have hsome : lastIndexOf c bs = some idx := memrchrLastIdx_eq_some_of_hit hidx hbc habove_idx
      obtain ⟨hcmp_eq, hcmp_ne⟩ := byte_cmp32_of_eq hbc
      have hsp0_al : (sp0 &&& 15#64 == 0#64) = true := by
        have h1 : (sp0 - 16#64) &&& 15#64 = 0#64 := by simpa [State.spAligned, hsp] using hsp_al
        exact beq_iff_eq.mpr (by simpa [arm64_norm] using h1)
      rw [hptr] at hx12
      wp_conv_pre => rw [cmFrameRO, cmFocus8RO p bs idx hidx, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      conv => arg 2; rw [← sepConj_assoc, ← cmFocus8RO p bs idx hidx]
      exact hpost _ ⟨rfl, by simpa [arm64_norm] using hrun,
        by simp [arm64_norm],
        by simp [arm64_norm],
        by simp [arm64_norm],
        CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
        (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
        by simpa [arm64_norm] using hpres.trace_eq,
        by simpa [arm64_norm] using hpres.fs_eq,
        by simpa [arm64_norm] using hpres.vm,
        by simp [hsome, RustAbi.optionU64, arm64_norm, idx]⟩
    · have hnomatch' : NoMatchFrom c bs (bs.length - (k + 1)) :=
        noMatchFrom_step_one_sub hk_lt_n hbc hnomatch
      obtain ⟨hcmp_eq, hcmp_ne⟩ := byte_cmp32_of_ne hbc
      rw [hptr] at hx12
      apply SepWP.cut (mid := fnBase + 80#64)
      wp_conv_pre => rw [cmFrameRO, cmFocus8RO p bs idx hidx, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← sepConj_assoc, ← cmFocus8RO p bs idx hidx]
      exact cmLoop1RO hc hn hmid_eq hmid_le hpost rem' (k + 1) _ (by omega) rfl
        ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
         by simpa [arm64_norm] using hsp_al,
         CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
         (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
         by simpa [arm64_norm] using hpres.trace_eq,
         by simpa [arm64_norm] using hpres.fs_eq,
         by simpa [arm64_norm] using hpres.vm⟩
        (by simp [arm64_norm, hx8])
        (by simp [arm64_norm, BitVec.ofNat_add])
        (by simp only [arm64_norm]; rw [← hptr, BitVec.ofNat_add]; bv_lin)
        (by simp [arm64_norm, hx9])
        (by simp [arm64_norm, hx0])
        (by simp [arm64_norm, hx10])
        (by simp [arm64_norm, hx1])
        (by simp [arm64_norm, hx2])
        hnomatch'

private theorem cmFromJoin3cRO {prog : Program} {fnBase : BitVec 64}
    (hc : prog.hasCode fnBase coreMemrchrWords)
    {s_entry s : State} {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)}
    {lo mid q : Nat} {post : State → SepProp → Prop}
    (hn : bs.length < 2 ^ 64)
    (hmid_eq : mid = lo + 16 * q)
    (hmid_le : mid ≤ bs.length)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrameRO p sp0 fp0 lr0 bs))
    (hpc : s.pc = fnBase + 60#64)
    (hpres : CmBodyPreserved s_entry s sp0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 mid)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 lo)
    (hx1 : s.readReg64 .x1 = p)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hx8_low : BitVec.zeroExtend 64 (BitVec.setWidth 32 (s.readReg64 (.gpr 8#5)) &&& 255#32) = c.zeroExtend 64) :
    SepWP prog lr0 s (cmFrameRO p sp0 fp0 lr0 bs) post := by
  have hsub_n_mid : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 mid =
      BitVec.ofNat 64 (bs.length - mid) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hadd_p : BitVec.ofNat 64 bs.length + p - 1#64 =
      (p + BitVec.ofNat 64 bs.length - 1#64) - BitVec.ofNat 64 0 := by
    bv_lin
  have hrun := hpres.running
  have hsp := hpres.sp_eq
  have hsp_al := hpres.sp_al
  apply SepWP.cut (mid := fnBase + 80#64)
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  exact cmLoop1RO hc hn hmid_eq hmid_le hpost (bs.length - mid) 0 _ (by omega) rfl
    ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
     by simpa [arm64_norm] using hsp_al,
     CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
     (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
     by simpa [arm64_norm] using hpres.trace_eq,
     by simpa [arm64_norm] using hpres.fs_eq,
     by simpa [arm64_norm] using hpres.vm⟩
    (by simp only [arm64_norm]; rw [← hmid_eq]; exact hsub_n_mid)
    (by simp [arm64_norm])
    (by simp [arm64_norm, hadd_p])
    (by simp [arm64_norm, hx8_low])
    (by simp [arm64_norm, hx0])
    (by simp [arm64_norm, hx10])
    (by simp [arm64_norm, hx1])
    (by simp [arm64_norm, hx2])
    (by simpa using noMatchFrom_self c bs)

private theorem coreMemrchrRO_sepWP {prog : Program} {fnBase : BitVec 64}
    (hc : prog.hasCode fnBase coreMemrchrWords)
    {s1 : State} {p st0 st1 : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)}
    {post : State → SepProp → Prop}
    (hn : bs.length < 2 ^ 64)
    (hpc1 : s1.pc = fnBase)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.spAligned = true)
    (hc_low : (s1.readReg64 .x0).setWidth 8 = c)
    (hx1_1 : s1.readReg64 .x1 = p)
    (hx2_1 : s1.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hpost : ∀ sf : State,
      CmExitState s1 sf s1.sp (s1.readReg64 .fp) (s1.readReg64 .lr) c bs →
      post sf (cmFrameRO p s1.sp (s1.readReg64 .fp) (s1.readReg64 .lr) bs)) :
    SepWP prog (s1.readReg64 .lr) s1
      ((p ↦ᵣ bs) ∗ ((s1.sp - 16#64) ↦₆₄ st0) ∗ ((s1.sp - 8#64) ↦₆₄ st1)) post := by
  let head := (memrchrHeadBV p).toNat
  have hhead_lt8 : head < 8 := memrchrHeadBV_lt8 p
  have hhead_bv : memrchrHeadBV p = BitVec.ofNat 64 head := memrchrHeadBV_eq_ofNat p
  refine step_stp64_perm (ea := s1.sp - 16#64) (ea2 := s1.sp - 8#64)
    (wb := some (.sp, s1.sp - 16#64))
    hpc1 hrun1
    (Program.fetch_of_hasCode_decodeAt 0 hc (BitVec.add_zero fnBase).symm rfl)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, Reg.fromSPBits] using hsp1)
    (by simp [evalAddrMode, Reg.fromSPBits, arm64_norm]; bv_omega)
    (by simp [arm64_norm])
    rfl rfl
    (SepStore64.right (SepStore64.left (SepStore64.here rfl)))
    (SepStore64.right (SepStore64.right (SepStore64.here rfl))) ?_
  intro m0 hm0_perm
  dsimp only [applyWriteback]
  by_cases hlt : bs.length < head
  · have hult_true : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 head) = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat]
      omega
    apply SepWP.cut (mid := fnBase + 60#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun1) ?_
    exact cmFromJoin3cRO hc (s_entry := s1) (lo := bs.length) (mid := bs.length) (q := 0)
      hn (by omega) (by omega) hpost rfl
      ⟨by simpa [arm64_norm] using hrun1, by simp [arm64_norm],
       by simpa [arm64_norm] using hsp1,
       by simp [CmSavedGprs, arm64_norm],
       by simp [calleeSavedVRegs, arm64_norm],
       by simp [arm64_norm],
       by simp [arm64_norm],
       by refine vmPreserved_setMem_of_perm ?_ (by simp [arm64_norm]); simpa [arm64_norm] using hm0_perm⟩
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (by simp [arm64_norm, hx1_1])
      (by simp [arm64_norm, hx2_1])
      (by simpa [arm64_norm, hc_low] using lowByte_mov_and_ff (s1.readReg64 .x0))
  · have hge : head ≤ bs.length := by omega
    have hult_false : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 head) = false := by
      simp [BitVec.ult, BitVec.toNat_ofNat]
      omega
    have hand15 :
        BitVec.zeroExtend 64 ((BitVec.ofNat 64 bs.length).setWidth 32 - (BitVec.ofNat 64 head).setWidth 32) &&& 15#64 =
          BitVec.ofNat 64 ((bs.length - head) % 16) := by
      rw [sub32_zext64_and15_eq, ofNat_sub_and15_eq_mod16 hge hn]
    obtain ⟨_htl_le, htl_ult_false, hmid_bv, hmid_eq, hmid_le⟩ := memrchr_split_of_ge hge hn
    apply SepWP.cut (mid := fnBase + 60#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun1) ?_
    exact cmFromJoin3cRO hc (s_entry := s1) (lo := head) (mid := bs.length - (bs.length - head) % 16)
      (q := (bs.length - head) / 16) hn hmid_eq hmid_le hpost rfl
      ⟨by simpa [arm64_norm] using hrun1, by simp [arm64_norm],
       by simpa [arm64_norm] using hsp1,
       by simp [CmSavedGprs, arm64_norm],
       by simp [calleeSavedVRegs, arm64_norm],
       by simp [arm64_norm],
       by simp [arm64_norm],
       by refine vmPreserved_setMem_of_perm ?_ (by simp [arm64_norm]); simpa [arm64_norm] using hm0_perm⟩
      (by simp [arm64_norm, ← hmid_eq])
      (by simp [arm64_norm])
      (by simp [arm64_norm, hx1_1])
      (by simp [arm64_norm, hx2_1])
      (by simpa [arm64_norm, hc_low] using lowByte_mov_and_ff (s1.readReg64 .x0))

private theorem optionU64_to_memrchrMatch {sf : State} {c : BitVec 8} {bs : List (BitVec 8)}
    (hret : RustAbi.optionU64.holds sf ((lastIndexOf c bs).map (BitVec.ofNat 64))) :
    match memrchrIdx c bs with
    | some i => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 i
    | none => sf.readReg64 .x0 = 0#64 := by
  rw [lastIndexOf_eq_memrchrIdx] at hret
  cases hidx : memrchrIdx c bs with
  | none => simpa [hidx, RustAbi.optionU64] using hret
  | some i => simpa [hidx, RustAbi.optionU64] using hret

private theorem memrchrSpecRO_16_simulates_stk {stk : Nat}
    (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    SpecSimulates (withVmPreserved (memrchrSpecRO 16))
      (withVmPreserved (memrchrSpecRO stk)) := by
  refine SpecSimulates.of_map fun x R s0 hpre => ?_
  dsimp only [withVmPreserved, memrchrSpecRO] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hpure, hpre⟩ := hpre
  rw [stackAt_shrink s0.sp stk 16 hstk.1 hstk.2] at hpre
  refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 16) ∗ R, ?_, ?_⟩
  · dsimp only [withVmPreserved, memrchrSpecRO]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.mono (by sep_entail) hpre⟩
  · intro sf _hret _hcc hpost
    dsimp only [withVmPreserved, memrchrSpecRO] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨hvm, hpost⟩ := hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨hpost_p, hpost⟩ := hpost
    rw [stackAt_shrink s0.sp stk 16 hstk.1 hstk.2]
    exact ⟨hvm, hpost_p, Satisfies.mono (by sep_entail) hpost⟩

private theorem coreMemrchr_memrchrSpecRO_16_vm_ok {prog : Program} {entry : BitVec 64}
    (hc : prog.hasWords entry coreMemrchrWords) :
    subroutine_ok prog entry (withVmPreserved (memrchrSpecRO 16)) := by
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withVmPreserved, memrchrSpecRO] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hn⟩, hpre⟩ := hpre
  rw [stackAt_eq_stackFrameAt s0.sp 16 (by decide),
    stackFrameAt16_eq_pair s0.sp] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨st0, st1, hpre⟩
  have hpre_init :
      s0.mem ⊨ ((x.p ↦ᵣ x.bs) ∗ ((s0.sp - 16#64) ↦₆₄ st0) ∗ ((s0.sp - 8#64) ↦₆₄ st1)) ∗ R :=
    Satisfies.mono (by sep_entail) hpre
  refine ⟨_, hpre_init, ?_⟩
  refine coreMemrchrRO_sepWP hc hn hpc hrun hsp hx0 hx1 hx2 ?_
  intro sf hexit
  have hcs : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    exact ⟨hexit.gprs.1, hexit.gprs.2.1, hexit.gprs.2.2.1, hexit.gprs.2.2.2.1,
      hexit.gprs.2.2.2.2.1, hexit.gprs.2.2.2.2.2.1, hexit.gprs.2.2.2.2.2.2.1,
      hexit.gprs.2.2.2.2.2.2.2.1, hexit.gprs.2.2.2.2.2.2.2.2.1,
      hexit.gprs.2.2.2.2.2.2.2.2.2, hexit.fp_eq, hexit.vregs⟩
  refine ⟨fun hm_f => ?_, hexit.sp_eq, hcs⟩
  have hmatch := optionU64_to_memrchrMatch hexit.ret_ok
  refine Satisfies.mono ?_ hm_f
  apply sepConj_mono_left
  dsimp only [cmFrameRO]
  rw [stackAt_eq_stackFrameAt s0.sp 16 (by decide), stackFrameAt16_eq_pair s0.sp]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_right (s0.readReg64 .fp) <|
    Entails.sepExists_right (s0.readReg64 .lr) ?_
  rw [pure_sepConj_of_true hexit.vm, pure_sepConj_of_true ⟨hexit.trace_eq, hexit.fs_eq, hmatch⟩]
  sep_entail

/-! ## 6. Layout-Generic Real-Code `hasWords` Contracts (`16 ≤ stk ∧ stk ≤ 2 ^ 64`) -/

/-- Real-code `withVmPreserved (memrchrSpecRO stk)` discharge over `prog.hasWords entry coreMemrchrWords`
    for `16 ≤ stk ∧ stk ≤ 2 ^ 64` (requires no global hook-freeness on `prog`). -/
theorem coreMemrchr_memrchrSpecRO_vm_ok {prog : Program} {entry : BitVec 64}
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64)
    (hc : prog.hasWords entry coreMemrchrWords) :
    subroutine_ok prog entry (withVmPreserved (memrchrSpecRO stk)) :=
  (memrchrSpecRO_16_simulates_stk hstk).subroutine_ok
    (coreMemrchr_memrchrSpecRO_16_vm_ok hc)

/-- Real-code `memrchrSpecRO stk` discharge over `prog.hasWords entry coreMemrchrWords`
    for `16 ≤ stk ∧ stk ≤ 2 ^ 64`. -/
theorem coreMemrchr_memrchrSpecRO_ok {prog : Program} {entry : BitVec 64}
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64)
    (hc : prog.hasWords entry coreMemrchrWords) :
    subroutine_ok prog entry (memrchrSpecRO stk) :=
  subroutine_ok_of_withVmPreserved (coreMemrchr_memrchrSpecRO_vm_ok hstk hc)

/-- Specialization of `coreMemrchr_memrchrSpecRO_vm_ok` at `stk = extHookStack` (`16384`). -/
theorem coreMemrchr_memrchrSpecRO_extHookStack_vm_ok {prog : Program} {entry : BitVec 64}
    (hc : prog.hasWords entry coreMemrchrWords) :
    subroutine_ok prog entry (withVmPreserved (memrchrSpecRO extHookStack)) :=
  coreMemrchr_memrchrSpecRO_vm_ok (by decide) hc

/-- Specialization of `coreMemrchr_memrchrSpecRO_ok` at `stk = extHookStack` (`16384`). -/
theorem coreMemrchr_memrchrSpecRO_extHookStack_ok {prog : Program} {entry : BitVec 64}
    (hc : prog.hasWords entry coreMemrchrWords) :
    subroutine_ok prog entry (memrchrSpecRO extHookStack) :=
  coreMemrchr_memrchrSpecRO_ok (by decide) hc

/-! ## 7. `coreMultiLib` (`MultiPlacedLib` Block `2`) Real-Code Bridges -/

/-- `coreMultiLib` block `2` holds `coreMemrchrWords` at `coreMultiLib.fnAddr mpl coreMemrchrSym`
    for every valid `MultiPlacement` and extern table `externs`. -/
theorem coreMemrchr_blockProgram_hasWords {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl)
    {externs : String → Option (State → State)} {svc : State → State} :
    (coreMultiLib.blockProgram mpl 2 externs (fun _ => none) svc).hasWords
      (coreMultiLib.fnAddr mpl coreMemrchrSym) coreMemrchrWords := by
  have hseg := (MultiPlacedLib.hasWords_of_checkSegment (lib := coreMultiLib) (mpl := mpl)
    (i := 2) (by decide) (fo := 0) (ws := coreMemrchrWords) (R := [])
    (X := externs) (svc := svc) hpl (by decide)).1
  have hfn : coreMultiLib.fnAddr mpl coreMemrchrSym = mpl.base 2 :=
    fnAddr_eq_base hpl 2 coreMemrchrSym (by decide) (by decide)
  rw [hfn]
  simpa [patchRelocs] using hseg

private theorem blockProgram_rebase_eq (lib : MultiPlacedLib) (mpl : MultiPlacement) (i : Nat) :
    (lib.blockProgram mpl i).rebase (mpl.base i) (fun _ => none) = lib.blockProgram mpl i := rfl

private theorem coreMemrchr_placed_memrchrSpecRO_16_vm_ok {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreMemrchrSym)
      (coreMultiLib.withCodeLoaded mpl (withVmPreserved (memrchrSpecRO 16))) := by
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hsp
  have hfn : coreMultiLib.fnAddr mpl coreMemrchrSym = mpl.base 2 :=
    fnAddr_eq_base hpl 2 coreMemrchrSym (by decide) (by decide)
  rw [hfn] at hpc
  dsimp only [MultiPlacedLib.withCodeLoaded, withVmPreserved, memrchrSpecRO] at hpre ⊢
  rw [sepConj_comm _ ⌜coreMultiLib.CodeLoaded mpl s0.mem⌝,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hn⟩, hpre⟩
  rw [stackAt_eq_stackFrameAt s0.sp 16 (by decide),
    stackFrameAt16_eq_pair s0.sp] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨st0, st1, hpre⟩
  have hpre_init :
      s0.mem ⊨ ((x.p ↦ᵣ x.bs) ∗ ((s0.sp - 16#64) ↦₆₄ st0) ∗ ((s0.sp - 8#64) ↦₆₄ st1)) ∗ R :=
    Satisfies.mono (by sep_entail) hpre
  refine ⟨_, hpre_init, ?_⟩
  apply sepWP_seg_rebase_pure hext 2 (by decide) cmNoSvc0_2 hcl (mid := s0.readReg64 .lr)
  intro s1' hcpu1
  have hpc1 : s1'.pc = mpl.base 2 := hcpu1.pc_eq.trans hpc
  have hrun1 : s1'.status = .Running := hcpu1.status_eq.trans hrun
  have hsp1_al : s1'.spAligned = true := hcpu1.spAligned.trans hsp
  have hsp1 : s1'.sp = s0.sp := hcpu1.sp_eq
  have hx1_1 : s1'.readReg64 .x1 = x.p := (hcpu1.readReg64 .x1).trans hx1
  have hx2_1 : s1'.readReg64 .x2 = BitVec.ofNat 64 x.bs.length := (hcpu1.readReg64 .x2).trans hx2
  have hc_low : (s1'.readReg64 .x0).setWidth 8 = x.c := by
    rw [hcpu1.readReg64 .x0]; exact hx0
  have hlr0_eq : s1'.readReg64 .lr = s0.readReg64 .lr := hcpu1.readReg64 .lr
  have hc_reb : ((coreMultiLib.blockProgram mpl 2).rebase (mpl.base 2) (fun _ => none)).hasCode
      (mpl.base 2) coreMemrchrWords := by
    rw [blockProgram_rebase_eq]
    have hhw := coreMemrchr_blockProgram_hasWords hpl
      (externs := fun _ => none) (svc := Syscall.standard)
    rwa [hfn] at hhw
  rw [← hlr0_eq]
  wp_conv_pre => rw [← hsp1]
  refine coreMemrchrRO_sepWP hc_reb hn hpc1 hrun1 hsp1_al hc_low hx1_1 hx2_1 ?_
  intro sf' hexit sm hcpu_out _hcl_out hnsp
  have hpc_sm : sm.pc = s1'.readReg64 .lr := hcpu_out.pc_eq.trans hexit.pc_eq
  have hrun_sm : sm.status = .Running := hcpu_out.status_eq.trans hexit.running
  have hsp_sm : sm.sp = s0.sp := (hcpu_out.sp_eq.trans hexit.sp_eq).trans hsp1
  have hcs_sm : CalleeSavedPreserved s0 sm := by
    refine SameCpuState.calleeSavedPreserved hcpu1 hcpu_out ?_
    rw [CalleeSavedPreserved.iff_regs]
    exact ⟨hexit.gprs.1, hexit.gprs.2.1, hexit.gprs.2.2.1, hexit.gprs.2.2.2.1,
      hexit.gprs.2.2.2.2.1, hexit.gprs.2.2.2.2.2.1, hexit.gprs.2.2.2.2.2.2.1,
      hexit.gprs.2.2.2.2.2.2.2.1, hexit.gprs.2.2.2.2.2.2.2.2.1,
      hexit.gprs.2.2.2.2.2.2.2.2.2, hexit.fp_eq, hexit.vregs⟩
  have hret_sm : RustAbi.optionU64.holds sm ((lastIndexOf x.c x.bs).map (BitVec.ofNat 64)) := by
    have hret := hexit.ret_ok
    cases hopt : (lastIndexOf x.c x.bs).map (BitVec.ofNat 64) with
    | none =>
      rw [hopt] at hret
      exact (hcpu_out.readReg64 .x0).trans hret
    | some v =>
      rw [hopt] at hret
      exact ⟨(hcpu_out.readReg64 .x0).trans hret.1,
             (hcpu_out.readReg64 .x1).trans hret.2⟩
  have hvm_sm : VmPreserved s0 sm :=
    VmPreserved.of_eq hnsp.2.2.2.1 hnsp.2.2.1
      (hcpu_out.tpidrEl0_eq.trans (hexit.vm.1.2.2.trans hcpu1.tpidrEl0_eq))
      hnsp.2.2.2.2.1 hnsp.2.1 (by intro _ _ _; simp [hnsp.2.2.2.2.2.2])
  have hmatch := optionU64_to_memrchrMatch hret_sm
  refine SepWP.done hpc_sm hrun_sm ⟨fun hm_f => ?_, hsp_sm, hcs_sm⟩
  refine Satisfies.mono ?_ hm_f
  apply sepConj_mono_left
  dsimp only [cmFrameRO]
  rw [hsp1, stackAt_eq_stackFrameAt s0.sp 16 (by decide), stackFrameAt16_eq_pair s0.sp]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_right (s1'.readReg64 .fp) <|
    Entails.sepExists_right (s1'.readReg64 .lr) ?_
  rw [pure_sepConj_of_true hvm_sm, pure_sepConj_of_true ⟨hnsp.1, hnsp.2.2.2.2.2.2, hmatch⟩]
  sep_entail

/-- Placement-generic real-code discharge on any hook-free program `P`: `coreMultiLib`'s
    `core::slice::memchr::memrchr` satisfies
    `coreMultiLib.withCodeLoaded mpl (withVmPreserved (memrchrSpecRO stk))` for `16 ≤ stk ∧ stk ≤ 2 ^ 64`. -/
theorem coreMemrchr_placed_memrchrSpecRO_vm_ok {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ pc, P.externAt? pc = none)
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreMemrchrSym)
      (coreMultiLib.withCodeLoaded mpl (withVmPreserved (memrchrSpecRO stk))) :=
  ((memrchrSpecRO_16_simulates_stk hstk).withCodeLoaded coreMultiLib mpl).subroutine_ok
    (coreMemrchr_placed_memrchrSpecRO_16_vm_ok hpl hext)

/-- Non-`VmPreserved` variant of `coreMemrchr_placed_memrchrSpecRO_vm_ok`. -/
theorem coreMemrchr_placed_memrchrSpecRO_ok {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ pc, P.externAt? pc = none)
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreMemrchrSym)
      (coreMultiLib.withCodeLoaded mpl (memrchrSpecRO stk)) := by
  have hsim : SpecSimulates (withVmPreserved (memrchrSpecRO stk)) (memrchrSpecRO stk) := by
    refine SpecSimulates.of_map fun x R s0 hpre => ⟨x, R, hpre, fun sf _ _ hpost => ?_⟩
    dsimp only [withVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  exact (hsim.withCodeLoaded coreMultiLib mpl).subroutine_ok
    (coreMemrchr_placed_memrchrSpecRO_vm_ok hpl hext hstk)

/-- `MultiPlacedLib.subroutineOk` for `coreMemrchrSym` against `withVmPreserved (memrchrSpecRO stk)`
    (`16 ≤ stk ∧ stk ≤ 2 ^ 64`). -/
theorem coreMemrchr_memrchrSpecRO_vm_subroutineOk {stk : Nat}
    (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    coreMultiLib.subroutineOk coreMemrchrSym
      (fun _ => withVmPreserved (memrchrSpecRO stk)) :=
  ⟨by decide, 2, 0, by decide, fun mpl hpl =>
    coreMemrchr_placed_memrchrSpecRO_vm_ok hpl
      (MultiPlacedLib.externAt?_blockProgram_none coreMultiLib mpl 2) hstk⟩

/-- `MultiPlacedLib.subroutineOk` for `coreMemrchrSym` against `memrchrSpecRO stk`
    (`16 ≤ stk ∧ stk ≤ 2 ^ 64`). -/
theorem coreMemrchr_memrchrSpecRO_subroutineOk {stk : Nat}
    (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    coreMultiLib.subroutineOk coreMemrchrSym (fun _ => memrchrSpecRO stk) :=
  ⟨by decide, 2, 0, by decide, fun mpl hpl =>
    coreMemrchr_placed_memrchrSpecRO_ok hpl
      (MultiPlacedLib.externAt?_blockProgram_none coreMultiLib mpl 2) hstk⟩

end

/-! ## 8. Ideal-Hook `toSat` Bridges (`memrchrHook → HookSat`) -/

/-- `memrchrHook` satisfies `withVmPreserved (memrchrSpecRO stk)` for every `stk : Nat`. -/
theorem memrchrHook_ro_vm_ok (stk : Nat) :
    HookOk memrchrHook (withVmPreserved (memrchrSpecRO stk)) :=
  hookOk_withVmPreserved (memrchrHook_ro_ok stk) memrchrHook_vmPreserved

/-- `toSat` bridge for `memrchrSpecRO stk`: any hook table mapping `sym` to `memrchrHook`
    satisfies `HookSat H sym (memrchrSpecRO stk)`. -/
theorem memrchrSpecRO_toSat {H : String → Option (State → State)} {sym : String}
    (stk : Nat) (h : H sym = some memrchrHook) :
    HookSat H sym (memrchrSpecRO stk) :=
  hookSat_of_hookOk h (memrchrHook_ro_ok stk)

/-- `toSat` bridge for `withVmPreserved (memrchrSpecRO stk)`: any hook table mapping `sym` to
    `memrchrHook` satisfies `HookSat H sym (withVmPreserved (memrchrSpecRO stk))`. -/
theorem memrchrSpecRO_vm_toSat {H : String → Option (State → State)} {sym : String}
    (stk : Nat) (h : H sym = some memrchrHook) :
    HookSat H sym (withVmPreserved (memrchrSpecRO stk)) :=
  hookSat_of_hookOk h (memrchrHook_ro_vm_ok stk)

/-- `cliExternsPlaced` instantiation of `memrchrSpecRO_toSat` at `lsMemrchrSym`. -/
theorem cliExternsPlaced_memrchrRO_toSat (mmpl : MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) lsMemrchrSym (memrchrSpecRO stk) :=
  memrchrSpecRO_toSat stk (cliExternsPlaced_memrchr mmpl W)

/-- `cliExternsPlaced` instantiation of `memrchrSpecRO_vm_toSat` at `lsMemrchrSym`. -/
theorem cliExternsPlaced_memrchrRO_vm_toSat (mmpl : MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) lsMemrchrSym (withVmPreserved (memrchrSpecRO stk)) :=
  memrchrSpecRO_vm_toSat stk (cliExternsPlaced_memrchr mmpl W)

end LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO
