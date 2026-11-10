/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.BV
public import ProofLib.ProgramReflection
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.MuslStage1Init
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.WPp
public import LibsignalBinary.Specifications.LibsignalPublicApi
public import LibsignalBinary.Proofs.TripleRatchet.Hooks
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Flat In-Image `<String as Clone>::clone` Proofs

Proves `stringCloneSpec A` for the 33-instruction (`132`-byte) AArch64 implementation of
`<alloc::string::String as core::clone::Clone>::clone` on `libsignalSessionCode.rebase`,
`trTrapProgAt`, and `tripleRatchetProgAt`.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Proofs.Common.StringCloneFlat

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open ProofLib.ProgramReflection
open ProofLib.StdStartup
open ProofLib.StdStartup.Stage1Internal (step_str64_perm)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (libsignalSessionCode libsignalSessionCode_tree)
open CryptoVerification.RustHeap
  (RustAlloc vecHeader vecU8 vecU8At allocHookStack LayoutOk
   allocFailedEvent allocFailedIn rustAllocSpec AllocHooks)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalPublicApi (stringCloneHookName stringCloneSpec)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack shimName allocName memcpyName handleErrorName
   sessionShimSpec sessionMemcpyRegionSpec sessionShim_hookOk
   hookMemcpy_region_trace_ok trTrapProgAt tripleRatchetProgAt
   trapsOnly_trTrap_kit subroutine_ok_kit_of_trTrap
   shim_ok_at_trap alloc_ok_at_trap session_memcpy_region_ok_at_trap
   panic_at_handle_error_trap)

/-! ## Arithmetic, Memory, and Stack Helpers -/

private theorem bv_sub_add_cancel48 (sp : BitVec 64) : sp - 48#64 + 48#64 = sp := by bv_omega
private theorem bv_add_neg48 (sp : BitVec 64) : sp + (-48#64) = sp - 48#64 := by bv_omega
private theorem bv_add_neg16 (sp : BitVec 64) : sp + (-16#64) = sp - 16#64 := by bv_omega
private theorem sub_add_base_cancel (b x y d : BitVec 64) :
    (b + x) - ((b + y) + d) = x - (y + d) := by bv_omega

@[local simp, local arm64_norm]
private theorem setMem_setMem_eq (s : State) (m1 m2 : Memory) :
    (s.setMem m1).setMem m2 = s.setMem m2 := by cases s; rfl
@[local simp, local arm64_norm]
private theorem setPC_setMem_eq (s : State) (m : Memory) (pc : BitVec 64) :
    (s.setMem m).setPC pc = (s.setPC pc).setMem m := by cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_setMem_eq (s : State) (m : Memory) : (s.setMem m).mem = m := by cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_setPC_eq (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_writeReg64_eq (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl

private theorem step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W64 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setMem, State.setPC, State.writeReg64, hsp, haddr,
      hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 (funext fun a => by rw [Memory.perm_write64, Memory.perm_write64])) hm2

local macro "wp_str64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

local macro "wp_stp64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stp64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_cancel48 bv_add_neg48 bv_add_neg16

private theorem spAligned_sub48 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 48#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_robdd

private theorem extHookStack_split_48 (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackFrameAt sp 48 ∗
        (stackAt (sp - 48#64) allocHookStack ∗
          stackFrameAt (sp - 48#64 - 4096#64) 12240) := by
  unfold stackAt extHookStack allocHookStack
  change memRegion (sp - 16384#64) 16384 = _
  rw [← stackFrameAt_eq_memRegion sp 16384 (by decide),
      ← stackFrameAt_eq_memRegion (sp - 48#64) 4096 (by decide),
      show (16384 : Nat) = 48 + 16336 from rfl,
      stackFrameAt_split sp 48 16336 (by decide),
      show (16336 : Nat) = 4096 + 12240 from rfl,
      stackFrameAt_split (sp - 48#64) 4096 12240 (by decide)]

private theorem stackFrameAt48_eq (sp : BitVec 64) :
    stackFrameAt sp 48 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
        ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
        ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

private theorem pack_stack48 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
     ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
     ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢ stackFrameAt sp 48 := by
  rw [stackFrameAt48_eq sp]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.refl _))))))

private theorem sepWP_done_let {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (h : ∀ sm, sm = s → sm.pc = mid → sm.status = .Running → SepWPp prog ret sm P Q Qp oom) :
    SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp oom) oom :=
  SepWP.done hpc hrun (h s rfl hpc hrun)

private theorem memRegion24_eq_exists_pts (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) from rfl,
      memRegion_split a 8 (8 + 8) (by decide),
      memRegion_split (a + 8#64) 8 8 (by decide),
      memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [sepExists_sepConj_left]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right, sepExists_sepConj_right]

/-! ## Instruction List and `Vec<u8>` Helpers -/

/-- Verbatim 33-instruction (`0x00..0x84`, `132` B) AArch64 machine code of
    `<alloc::string::String as core::clone::Clone>::clone` (`rustc 1.98.1`). -/
def rustStringCloneInstrs
    (fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64) : List Instr :=
  [ .stp .W64 .x29 .x30 (.PreIndex .sp (-0x30#64)), .stp .W64 .x22 .x21 (.Offset .sp 0x10#64),
    .stp .W64 .x20 .x19 (.Offset .sp 0x20#64), .addSubImm .W64 .ADD .x29 .sp 0x0#12 false,
    .ldr .W64 .X64 false .x19 (.Offset .x0 0x10#64), .logicalShift .W64 .ORR .x20 .xzr .x8 .LSL 0,
    .cbz .W64 false .x19 0x44#64, .ldr .W64 .X64 false .x22 (.Offset .x0 0x8#64),
    .bl (shimAddr - (fnAddr + 0x20#64)), .logicalShift .W64 .ORR .x0 .xzr .x19 .LSL 0,
    .moveWide .W32 .MOVZ .x1 0x1#16 0, .bl (allocAddr - (fnAddr + 0x2c#64)),
    .cbz .W64 false .x0 0x48#64, .logicalShift .W64 .ORR .x1 .xzr .x22 .LSL 0,
    .logicalShift .W64 .ORR .x2 .xzr .x19 .LSL 0, .logicalShift .W64 .ORR .x21 .xzr .x0 .LSL 0,
    .bl (memcpyAddr - (fnAddr + 0x40#64)), .stp .W64 .x19 .x21 (.Offset .x20 0x0#64),
    .str .X64 .x19 (.Offset .x20 0x10#64), .ldp .W64 false .x20 .x19 (.Offset .sp 0x20#64),
    .ldp .W64 false .x22 .x21 (.Offset .sp 0x10#64), .ldp .W64 false .x29 .x30 (.PostIndex .sp 0x30#64),
    .ret .x30, .moveWide .W32 .MOVZ .x21 0x1#16 0,
    .stp .W64 .x19 .x21 (.Offset .x20 0x0#64), .str .X64 .x19 (.Offset .x20 0x10#64),
    .ldp .W64 false .x20 .x19 (.Offset .sp 0x20#64), .ldp .W64 false .x22 .x21 (.Offset .sp 0x10#64),
    .ldp .W64 false .x29 .x30 (.PostIndex .sp 0x30#64), .ret .x30,
    .moveWide .W32 .MOVZ .x0 0x1#16 0, .logicalShift .W64 .ORR .x1 .xzr .x19 .LSL 0,
    .bl (handleErrorAddr - (fnAddr + 0x80#64)) ]

private abbrev FetchSeq (P : Program) (fnAddr : BitVec 64) (ls : List Instr) : Prop :=
  ∀ (i : Nat) (hi : i < ls.length),
    P.fetch (fnAddr + BitVec.ofNat 64 (4 * i)) = some ls[i]

private theorem fetch_seq_at {P : Program} {fnAddr off : BitVec 64} {ls : List Instr} {inst : Instr}
    (i : Nat) (hf : FetchSeq P fnAddr ls)
    (hi : ls[i]? = some inst := by rfl)
    (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) :
    P.fetch (fnAddr + off) = some inst := by
  have hlt : i < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have h := hf i hlt
  rw [List.getElem?_eq_getElem hlt] at hi
  cases hi
  rwa [hoff] at h

private theorem fetch_seq_at0 {P : Program} {fnAddr : BitVec 64} {ls : List Instr} {inst : Instr}
    (hf : FetchSeq P fnAddr ls) (hi : ls[0]? = some inst := by rfl) :
    P.fetch fnAddr = some inst := by
  simpa using fetch_seq_at 0 hf hi rfl

private theorem vecGhostAt_bytes_lt_2pow63 {A : RustAlloc}
    {m : Memory} {g : VecGhost} {p : BitVec 64} {R : SepProp}
    (hm : m ⊨ vecGhostAt A g p ∗ R) :
    g.bytes.length < 2 ^ 63 := by
  unfold vecGhostAt vecU8At at hm
  have hPull :
      (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
        ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        (if g.cap = 0 then emp
         else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
           memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))) ∗ R =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
          (if g.cap = 0 then emp
           else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
             memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗ R) := by
    sep_ac_rfl
  rw [hPull, satisfies_pure_sepConj] at hm
  omega

private def vecGhostPayload (A : RustAlloc) (g : VecGhost) : SepProp :=
  ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

private theorem vecGhostAt_eq_header_payload (A : RustAlloc) (g : VecGhost) (p : BitVec 64) :
    vecGhostAt A g p =
      (((p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length)) ∗
        vecGhostPayload A g) := by
  unfold vecGhostAt vecU8At vecHeader vecGhostPayload; sep_ac_rfl

private def vecGhostPayloadRest (A : RustAlloc) (g : VecGhost) : SepProp :=
  ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗ A.live g.ptr g.cap.toNat 1 ∗
  memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)

private theorem vecGhostPayload_nonempty_entails (A : RustAlloc) (g : VecGhost)
    (hpos : 0 < g.bytes.length) :
    vecGhostPayload A g ⊢ (g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A g := by
  unfold vecGhostPayload vecGhostPayloadRest; refine Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
  have hcapNe : g.cap ≠ 0 := by
    intro hc0; have : g.cap.toNat = 0 := by rw [hc0]; rfl
    omega
  simp only [hcapNe, ↓reduceIte]
  have hEq :
      A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) =
      (g.ptr ↦ₛ g.bytes) ∗ (A.live g.ptr g.cap.toNat 1 ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by
    sep_ac_rfl
  rw [hEq]; exact sepConj_mono_right (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.of_eq (by sep_ac_rfl)))

private theorem vecGhostPayload_nonempty_pack (A : RustAlloc) (g : VecGhost)
    (hpos : 0 < g.bytes.length) :
    ((g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A g) ⊢ vecGhostPayload A g := by
  unfold vecGhostPayloadRest vecGhostPayload
  have hPull :
      (g.ptr ↦ₛ g.bytes) ∗ (⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        A.live g.ptr g.cap.toNat 1 ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        ((g.ptr ↦ₛ g.bytes) ∗ A.live g.ptr g.cap.toNat 1 ∗
          memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by
    sep_ac_rfl
  rw [hPull]; refine Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
  have hcapNe : g.cap ≠ 0 := by
    intro hc0; have : g.cap.toNat = 0 := by rw [hc0]; rfl
    omega
  simp only [hcapNe, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.of_eq (by sep_ac_rfl))

private theorem vecU8_empty_pack (A : RustAlloc) (ret : BitVec 64) :
    ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 1#64) ∗ ((ret + 16#64) ↦₆₄ 0#64)) ⊢ vecU8 A ret [] := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  have hZero : (0#64 : BitVec 64) = 0 := rfl
  simp only [hZero, ↓reduceIte, sepConj_emp, List.length_nil]
  refine Entails.trans (Entails.pure_right
    (φ := 0 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0)
    (by decide) (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

private theorem vecU8_nonempty_pack (A : RustAlloc)
    (ret newPtr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt63 : bs.length < 2 ^ 63) (hne0 : newPtr ≠ 0#64) :
    let lenBv := BitVec.ofNat 64 bs.length
    (((ret ↦₆₄ lenBv) ∗ ((ret + 8#64) ↦₆₄ newPtr) ∗ ((ret + 16#64) ↦₆₄ lenBv)) ∗
      A.live newPtr bs.length 1 ∗ (newPtr ↦ₛ bs)) ⊢ vecU8 A ret bs := by
  intro lenBv
  have hlenNat : lenBv.toNat = bs.length := by
    dsimp only [lenBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcapNe : lenBv ≠ 0 := by
    intro h0; have := congrArg BitVec.toNat h0; rw [hlenNat] at this; change bs.length = 0 at this; omega
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right lenBv (Entails.sepExists_right newPtr ?_)
  simp only [hcapNe, ↓reduceIte, hlenNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  refine Entails.trans (Entails.pure_right (φ := bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ newPtr ≠ 0)
    ⟨Nat.le_refl _, hlt63, hne0⟩ (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

/-! ## Per-Segment Symbolic Execution -/

private abbrev savedStack48 (s0 : State) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

private abbrev vecHdrPts (p : BitVec 64) (g : VecGhost) : SepProp :=
  (p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length)

private abbrev retPts (ret r0 r1 r2 : BitVec 64) : SepProp :=
  (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2)

private abbrev csUpperPreserved (s0 sm : State) : Prop :=
  ∀ r ∈ ([.x23, .x24, .x25, .x26, .x27, .x28] : List Reg), sm.readReg64 r = s0.readReg64 r

private theorem csUpperPreserved_trans {s0 sm sf : State}
    (h1 : csUpperPreserved s0 sm) (h2 : CalleeSavedPreserved sm sf) :
    csUpperPreserved s0 sf := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h2.readReg64_x23.trans (h1 .x23 (by simp))
  · exact h2.readReg64_x24.trans (h1 .x24 (by simp))
  · exact h2.readReg64_x25.trans (h1 .x25 (by simp))
  · exact h2.readReg64_x26.trans (h1 .x26 (by simp))
  · exact h2.readReg64_x27.trans (h1 .x27 (by simp))
  · exact h2.readReg64_x28.trans (h1 .x28 (by simp))

private abbrev cloneFrame0 (s0 : State) : SepProp :=
  stackFrameAt (s0.sp - 48#64 - 4096#64) 12240

private abbrev clonePost (A : RustAlloc)
    (p ret : BitVec 64) (g : VecGhost) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ (cloneFrame0 s0 ∗ R)) →
      sf.mem ⊨ (stringCloneSpec A).post (p, ret, g) s0 sf ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev clonePanic (A : RustAlloc)
    (p ret : BitVec 64) (g : VecGhost) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ (cloneFrame0 s0 ∗ R)) →
      sf.mem ⊨ (stringCloneSpec A).onPanic (p, ret, g) s0 sf ∗ R

private abbrev cloneOom : State → SepProp :=
  fun _ => ⌜False⌝

private theorem clone_empty_epilogue (A : RustAlloc) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (p ret : BitVec 64) (g : VecGhost)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sm : State)
    (hg_empty : g.bytes = []) (hsp0 : s0.spAligned = true)
    (hpcm : sm.pc = fnAddr + 0x5c#64) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 48#64) (hx19 : sm.readReg64 .x19 = 0#64)
    (hx20 : sm.readReg64 .x20 = ret) (hcsm : csUpperPreserved s0 sm)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0) (htrm : sm.trace = s0.trace) :
    SepWPp P (s0.readReg64 .lr) sm
      (retPts ret r0 r1 r2 ∗ savedStack48 s0 ∗
        (vecHdrPts p g ∗ vecGhostPayload A g) ∗
        A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack)
      (clonePost A p ret g R s0)
      (clonePanic A p ret g R s0)
      cloneOom := by
  have hf23 := fetch_seq_at 23 hCode; have hf24 := fetch_seq_at 24 hCode
  have hf25 := fetch_seq_at 25 hCode; have hf26 := fetch_seq_at 26 hCode
  have hf27 := fetch_seq_at 27 hCode; have hf28 := fetch_seq_at 28 hCode
  have hf29 := fetch_seq_at 29 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48 : decide (sm.sp &&& 15#64 = 0#64) = true := by
    rw [hspm]; exact decide_eq_true (beq_iff_eq.mp (spAligned_sub48 hspAl0))
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  dsimp only [retPts, savedStack48, vecHdrPts]
  wp_step; wp_stp64 hf24 m1 hm1; wp_str64 hf25 m2 hm2
  wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp [arm64_norm]) (by simp [arm64_norm, hrunm])
    fun sf hsf hpcf hrunf => ?_
  have hspf : sf.sp = s0.sp := by rw [hsf]; simp [arm64_norm]
  have htrf : sf.trace = s0.trace := by rw [hsf]; simp [arm64_norm, htrm]
  have hcsf : CalleeSavedPreserved s0 sf := by
    rw [hsf]
    refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using hcsm .x23 (by simp), by simpa [arm64_norm] using hcsm .x24 (by simp),
      by simpa [arm64_norm] using hcsm .x25 (by simp), by simpa [arm64_norm] using hcsm .x26 (by simp),
      by simpa [arm64_norm] using hcsm .x27 (by simp), by simpa [arm64_norm] using hcsm .x28 (by simp),
      by simp [arm64_norm], by simpa [calleeSavedVRegs, arm64_norm] using hvm⟩
  clear hsf
  refine SepWPp.done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
  dsimp only [clonePost, cloneFrame0, stringCloneSpec] at hmf ⊢
  rw [extHookStack_split_48 s0.sp]
  have hx19' : sm.readReg64 (Reg.gpr 19#5) = 0#64 := hx19
  have hx20' : sm.readReg64 (Reg.gpr 20#5) = ret := hx20
  try simp only [hx19', hx20', BitVec.add_zero] at hmf
  have hVecEq : (vecHdrPts p g ∗ vecGhostPayload A g) = vecGhostAt A g p :=
    (vecGhostAt_eq_header_payload A g p).symm
  have hmf1 : sf.mem ⊨
      (vecGhostAt A g p ∗
        (retPts ret 0#64 1#64 0#64 ∗ A.pool ∗
          (savedStack48 s0 ∗
            (stackAt (s0.sp - 48#64) allocHookStack ∗ cloneFrame0 s0)))) ∗ R := by
    rw [← hVecEq]; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf
  rw [hg_empty]
  refine Satisfies.mono (sepConj_mono_left ?_) hmf1
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (vecU8_empty_pack A ret)
        (sepConj_mono_right (sepConj_mono_left (pack_stack48 s0.sp _ _ _ _ _ _))))) ?_
  exact Entails.pure_right htrf (Entails.of_eq (by sep_ac_rfl))

private theorem clone_panic_tail (A : RustAlloc) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hHandleErr : P.externAt? handleErrorAddr = some Rust.panicked)
    (p ret : BitVec 64) (g : VecGhost)
    (Rest R : SepProp) (s0 sf2 : State)
    (hpc2 : sf2.pc = fnAddr + 0x30#64) (hrun2 : sf2.status = .Running)
    (hx0_0 : sf2.readReg64 .x0 = 0#64) (htr2 : sf2.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp P (s0.readReg64 .lr) sf2
      Rest
      (clonePost A p ret g R s0)
      (clonePanic A p ret g R s0)
      cloneOom := by
  have hf12 := fetch_seq_at 12 hCode; have hf30 := fetch_seq_at 30 hCode
  have hf31 := fetch_seq_at 31 hCode; have hf32 := fetch_seq_at 32 hCode
  apply SepWPp.of_sepWP (mid := handleErrorAddr)
  wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun2]) fun sm_pan hsm hpc_pan hrun_pan => ?_
  have htr_pan : sm_pan.trace = s0.trace ++ [allocFailedEvent] := by
    rw [hsm]; simp [arm64_norm, htr2]
  clear hsm
  refine SepWPp.panic hrun_pan (hpc_pan ▸ hHandleErr) fun hmp => ?_
  dsimp only [clonePanic, cloneFrame0, stringCloneSpec] at hmp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨LibsignalBinary.Proofs.Common.SharedHelpers.allocFailedIn_and_prefix_of_trace_append_singleton
    (by simp [Rust.panicked, htr_pan]), ?_⟩
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _))
    (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmp)

private theorem clone_memcpy_epilogue (A : RustAlloc) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hMemcpy : subroutine_ok P memcpyAddr sessionMemcpyRegionSpec)
    (p ret newPtr : BitVec 64) (g : VecGhost)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sf2 : State)
    (hpos : 0 < g.bytes.length) (hlt63 : g.bytes.length < 2 ^ 63)
    (hsp0 : s0.spAligned = true) (hpNe0 : newPtr ≠ 0#64)
    (hpc2 : sf2.pc = fnAddr + 0x30#64) (hrun2 : sf2.status = .Running)
    (hsp2 : sf2.sp = s0.sp - 48#64) (hx0_2 : sf2.readReg64 .x0 = newPtr)
    (hx19_2 : sf2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length)
    (hx20_2 : sf2.readReg64 .x20 = ret) (hx22_2 : sf2.readReg64 .x22 = g.ptr)
    (hcs2 : csUpperPreserved s0 sf2) (hv2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (htr2 : sf2.trace = s0.trace) :
    SepWPp P (s0.readReg64 .lr) sf2
      (memRegion newPtr g.bytes.length ∗ vecGhostPayload A g ∗
        A.live newPtr g.bytes.length 1 ∗ A.pool ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗ retPts ret r0 r1 r2 ∗
        vecHdrPts p g ∗ savedStack48 s0)
      (clonePost A p ret g R s0)
      (clonePanic A p ret g R s0)
      cloneOom := by
  have hf12 := fetch_seq_at 12 hCode; have hf13 := fetch_seq_at 13 hCode
  have hf14 := fetch_seq_at 14 hCode; have hf15 := fetch_seq_at 15 hCode
  have hf16 := fetch_seq_at 16 hCode; have hf17 := fetch_seq_at 17 hCode
  have hf18 := fetch_seq_at 18 hCode; have hf19 := fetch_seq_at 19 hCode
  have hf20 := fetch_seq_at 20 hCode; have hf21 := fetch_seq_at 21 hCode
  have hf22 := fetch_seq_at 22 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (vecGhostPayload_nonempty_entails A g hpos))) ?_
  apply SepWPp.of_sepWP (mid := memcpyAddr)
  dsimp only [retPts, savedStack48, vecHdrPts]
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun2]) fun sm3 hsm hpc3 hrun3 => ?_
  have hsp3 : sm3.sp = s0.sp - 48#64 := by rw [hsm]; simp [arm64_norm, hsp2]
  have hlr3 : sm3.readReg64 .lr = fnAddr + 0x44#64 := by
    rw [hsm]; simp only [arm64_norm]; try bv_omega
  have hx0_3 : sm3.readReg64 .x0 = newPtr := by rw [hsm]; simp [arm64_norm, hx0_2]
  have hx1_3 : sm3.readReg64 .x1 = g.ptr := by rw [hsm]; simp [arm64_norm]
  have hx2_3 : (sm3.readReg64 .x2).toNat = g.bytes.length := by
    rw [hsm]; simp only [arm64_norm]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx19_3 : sm3.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm]; simp [arm64_norm, hx19_2]
  have hx20_3 : sm3.readReg64 .x20 = ret := by rw [hsm]; simp [arm64_norm, hx20_2]
  have hx21_3 : sm3.readReg64 .x21 = newPtr := by rw [hsm]; simp [arm64_norm]
  have hcs3 : csUpperPreserved s0 sm3 := by
    rw [hsm]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcs2 _ (by simp)
  have hv3 : calleeSavedVRegs sm3 = calleeSavedVRegs s0 := by
    rw [hsm]; simpa [calleeSavedVRegs, arm64_norm] using hv2
  have htr3 : sm3.trace = s0.trace := by rw [hsm]; simp [arm64_norm, htr2]
  clear hsm
  let FrameMc :=
    vecGhostPayloadRest A g ∗ A.live newPtr g.bytes.length 1 ∗
    A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
    retPts ret r0 r1 r2 ∗ vecHdrPts p g ∗ savedStack48 s0
  refine SepWPp.call_wpp (x := (newPtr, g.ptr, g.bytes)) (ret_pc := fnAddr + 0x44#64)
    (F := FrameMc) hMemcpy hpc3 hrun3
    (by simpa [State.spAligned, hsp3] using hspAl48b) hlr3 ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hp⟩ => by
      dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hp
      exact False.elim (not_satisfies_false_sepConj hp))
    ?_
    (fun _ _ _ ho => by
      dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  · intro R' hm'
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec, FrameMc]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_3, hx1_3, hx2_3⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'⟩
  · intro sf3 hpc_sf3 hrun_sf3 hsp_sf3 hcs_sf3
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec, FrameMc]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htr_mc⟩ => ?_
    have hsp3' : sf3.sp = s0.sp - 48#64 := hsp_sf3.trans hsp3
    have hspAl48 : decide (sf3.sp &&& 15#64 = 0#64) = true := by
      rw [hsp3']; exact decide_eq_true (beq_iff_eq.mp hspAl48b)
    have hx19_sf3 : sf3.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
      hcs_sf3.readReg64_x19.trans hx19_3
    have hx20_sf3 : sf3.readReg64 .x20 = ret := hcs_sf3.readReg64_x20.trans hx20_3
    have hx21_sf3 : sf3.readReg64 .x21 = newPtr := hcs_sf3.readReg64_x21.trans hx21_3
    have hcs_sf3_s0 : csUpperPreserved s0 sf3 := csUpperPreserved_trans hcs3 hcs_sf3
    have htr_sf3 : sf3.trace = s0.trace := htr_mc.trans htr3
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    dsimp only [retPts, savedStack48, vecHdrPts]
    wp_stp64 hf17 m1 hm1; wp_str64 hf18 m2 hm2
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let (by simp [arm64_norm]) (by simp [arm64_norm, hrun_sf3])
      fun sf hsf hpcf hrunf => ?_
    have hspf : sf.sp = s0.sp := by rw [hsf]; simp [arm64_norm]
    have htrf : sf.trace = s0.trace := by rw [hsf]; simp [arm64_norm, htr_sf3]
    have hcsf : CalleeSavedPreserved s0 sf := by
      rw [hsf]
      refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
        by simpa [arm64_norm] using hcs_sf3_s0 .x23 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x24 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x25 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x26 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x27 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x28 (by simp),
        by simp [arm64_norm],
        by simpa [calleeSavedVRegs, arm64_norm] using hcs_sf3.vregs.trans hv3⟩
    clear hsf
    refine SepWPp.done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
    dsimp only [clonePost, cloneFrame0, stringCloneSpec] at hmf ⊢
    rw [extHookStack_split_48 s0.sp]
    have hx19' : sf3.readReg64 (Reg.gpr 19#5) = BitVec.ofNat 64 g.bytes.length := hx19_sf3
    have hx20' : sf3.readReg64 (Reg.gpr 20#5) = ret := hx20_sf3
    have hx21' : sf3.readReg64 (Reg.gpr 21#5) = newPtr := hx21_sf3
    try simp only [hx19', hx20', hx21', BitVec.add_zero] at hmf
    let lenBv := BitVec.ofNat 64 g.bytes.length
    have hmf1 : sf.mem ⊨
        ((vecHdrPts p g ∗ ((g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A g)) ∗
          ((retPts ret lenBv newPtr lenBv ∗
            A.live newPtr g.bytes.length 1 ∗ (newPtr ↦ₛ g.bytes)) ∗
           A.pool ∗
           (savedStack48 s0 ∗
            (stackAt (s0.sp - 48#64) allocHookStack ∗ cloneFrame0 s0)))) ∗ R :=
      Satisfies.mono (Entails.of_eq (by dsimp only [lenBv]; sep_ac_rfl)) hmf
    refine Satisfies.mono (sepConj_mono_left ?_) hmf1
    have hGhostEnt :
        (vecHdrPts p g ∗ ((g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A g)) ⊢
        vecGhostAt A g p := by
      rw [vecGhostAt_eq_header_payload A g p]
      exact sepConj_mono_right (vecGhostPayload_nonempty_pack A g hpos)
    refine Entails.trans
      (sepConj_mono hGhostEnt
        (sepConj_mono (vecU8_nonempty_pack A ret newPtr g.bytes hpos hlt63 hpNe0)
          (sepConj_mono_right (sepConj_mono_left (pack_stack48 s0.sp _ _ _ _ _ _))))) ?_
    exact Entails.pure_right htrf (Entails.of_eq (by sep_ac_rfl))

private theorem clone_nonempty_branch (A : RustAlloc) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hShim : subroutine_ok P shimAddr sessionShimSpec)
    (hAlloc : subroutine_ok P allocAddr (rustAllocSpec A))
    (hMemcpy : subroutine_ok P memcpyAddr sessionMemcpyRegionSpec)
    (hHandleErr : P.externAt? handleErrorAddr = some Rust.panicked)
    (p ret : BitVec 64) (g : VecGhost)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sm0 : State)
    (hpos : 0 < g.bytes.length) (hlt63 : g.bytes.length < 2 ^ 63) (hsp0 : s0.spAligned = true)
    (hpcm0 : sm0.pc = fnAddr + 0x1c#64) (hrunm0 : sm0.status = .Running)
    (hspm0 : sm0.sp = s0.sp - 48#64) (hx0_m0 : sm0.readReg64 .x0 = p)
    (hx19_m0 : sm0.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length)
    (hx20_m0 : sm0.readReg64 .x20 = ret) (hcsm0 : csUpperPreserved s0 sm0)
    (hvm0 : calleeSavedVRegs sm0 = calleeSavedVRegs s0) (htrm0 : sm0.trace = s0.trace) :
    SepWPp P (s0.readReg64 .lr) sm0
      (vecHdrPts p g ∗ vecGhostPayload A g ∗ A.pool ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0)
      (clonePost A p ret g R s0)
      (clonePanic A p ret g R s0)
      cloneOom := by
  have hf7 := fetch_seq_at 7 hCode; have hf8 := fetch_seq_at 8 hCode
  have hf9 := fetch_seq_at 9 hCode; have hf10 := fetch_seq_at 10 hCode
  have hf11 := fetch_seq_at 11 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  apply SepWPp.of_sepWP (mid := shimAddr)
  dsimp only [retPts, savedStack48, vecHdrPts]
  wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrunm0]) fun sm1 hsm1 hpc1 hrun1 => ?_
  have hsp1 : sm1.sp = s0.sp - 48#64 := by rw [hsm1]; simp [arm64_norm, hspm0]
  have hlr1 : sm1.readReg64 .lr = fnAddr + 0x24#64 := by
    rw [hsm1]; simp only [arm64_norm]; try bv_omega
  have hx19_1 : sm1.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm1]; simp [arm64_norm, hx19_m0]
  have hx20_1 : sm1.readReg64 .x20 = ret := by rw [hsm1]; simp [arm64_norm, hx20_m0]
  have hx22_1 : sm1.readReg64 .x22 = g.ptr := by rw [hsm1]; simp [arm64_norm]
  have hcs1 : csUpperPreserved s0 sm1 := by
    rw [hsm1]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcsm0 _ (by simp)
  have hv1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := by
    rw [hsm1]; simpa [calleeSavedVRegs, arm64_norm] using hvm0
  have htr1 : sm1.trace = s0.trace := by rw [hsm1]; simp [arm64_norm, htrm0]
  clear hsm1
  let FrameShim :=
    vecHdrPts p g ∗ vecGhostPayload A g ∗ A.pool ∗
    stackAt (s0.sp - 48#64) allocHookStack ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0
  refine SepWPp.call_wpp (x := ()) (ret_pc := fnAddr + 0x24#64)
    (F := FrameShim) hShim hpc1 hrun1
    (by simpa [State.spAligned, hsp1] using hspAl48b) hlr1
    (fun _ hm' => by dsimp only [sessionShimSpec, FrameShim]; rw [emp_sepConj]; exact hm')
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hp⟩ => by
      dsimp only [sessionShimSpec] at hp; exact False.elim (not_satisfies_false_sepConj hp))
    ?_
    (fun _ _ _ ho => by
      dsimp only [sessionShimSpec] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
  dsimp only [sessionShimSpec, FrameShim]
  refine SepWPp.pure_elim fun htr_sh => ?_
  have hsp_sf1' : sf1.sp = s0.sp - 48#64 := hsp_sf1.trans hsp1
  have hx19_sf1 : sf1.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
    hcs_sf1.readReg64_x19.trans hx19_1
  have hx20_sf1 : sf1.readReg64 .x20 = ret := hcs_sf1.readReg64_x20.trans hx20_1
  have hx22_sf1 : sf1.readReg64 .x22 = g.ptr := hcs_sf1.readReg64_x22.trans hx22_1
  have hcs_sf1_s0 : csUpperPreserved s0 sf1 := csUpperPreserved_trans hcs1 hcs_sf1
  have htr_sf1 : sf1.trace = s0.trace := htr_sh.trans htr1
  apply SepWPp.of_sepWP (mid := allocAddr)
  wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun_sf1]) fun sm2 hsm2 hpc2 hrun2 => ?_
  have hsp2 : sm2.sp = s0.sp - 48#64 := by rw [hsm2]; simp [arm64_norm, hsp_sf1']
  have hlr2 : sm2.readReg64 .lr = fnAddr + 0x30#64 := by
    rw [hsm2]; simp only [arm64_norm]; try bv_omega
  have hx0_2 : sm2.readReg64 .x0 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm2]; simp [arm64_norm]
  have hx1_2 : sm2.readReg64 .x1 = 1#64 := by rw [hsm2]; simp [arm64_norm]
  have hx19_2 : sm2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm2]; simp [arm64_norm, hx19_sf1]
  have hx20_2 : sm2.readReg64 .x20 = ret := by rw [hsm2]; simp [arm64_norm, hx20_sf1]
  have hx22_2 : sm2.readReg64 .x22 = g.ptr := by rw [hsm2]; simp [arm64_norm, hx22_sf1]
  have hcs2 : csUpperPreserved s0 sm2 := by
    rw [hsm2]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcs_sf1_s0 _ (by simp)
  have hv2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := by
    rw [hsm2]; simpa [calleeSavedVRegs, arm64_norm] using hcs_sf1.vregs.trans hv1
  have htr2 : sm2.trace = s0.trace := by rw [hsm2]; simp [arm64_norm, htr_sf1]
  clear hsm2
  let FrameAl :=
    vecHdrPts p g ∗ vecGhostPayload A g ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0
  have hx0_nat : (sm2.readReg64 .x0).toNat = g.bytes.length := by
    rw [hx0_2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx1_nat : (sm2.readReg64 .x1).toNat = 1 := by rw [hx1_2]; rfl
  have hLay : LayoutOk g.bytes.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  refine SepWPp.call_wpp (x := (g.bytes.length, 1)) (ret_pc := fnAddr + 0x30#64)
    (F := FrameAl) hAlloc hpc2 hrun2
    (by simpa [State.spAligned, hsp2] using hspAl48b) hlr2 ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hp⟩ => by
      dsimp only [rustAllocSpec] at hp
      exact False.elim (not_satisfies_false_sepConj hp))
    ?_
    (fun _ _ _ ho => by
      dsimp only [rustAllocSpec] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  · intro R' hm'
    dsimp only [rustAllocSpec, FrameAl]
    rw [hsp2, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_nat, hx1_nat, hLay⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'⟩
  · intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 hcs_sf2
    dsimp only [rustAllocSpec, FrameAl]
    rw [hsp2]
    have hsp_sf2' : sf2.sp = s0.sp - 48#64 := hsp_sf2.trans hsp2
    have hx19_sf2 : sf2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
      hcs_sf2.readReg64_x19.trans hx19_2
    have hx20_sf2 : sf2.readReg64 .x20 = ret := hcs_sf2.readReg64_x20.trans hx20_2
    have hx22_sf2 : sf2.readReg64 .x22 = g.ptr := hcs_sf2.readReg64_x22.trans hx22_2
    have hcs_s0_sf2 : csUpperPreserved s0 sf2 := csUpperPreserved_trans hcs2 hcs_sf2
    have hv_s0_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 :=
      hcs_sf2.vregs.trans hv2
    by_cases hnull : sf2.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte]
      have hPullNull :
          (A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
            ⌜sf2.trace = sm2.trace ++ [allocFailedEvent]⌝) ∗ FrameAl =
          ⌜sf2.trace = sm2.trace ++ [allocFailedEvent]⌝ ∗
            (A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗ FrameAl) := by
        dsimp only [FrameAl]; sep_ac_rfl
      rw [hPullNull]
      refine SepWPp.pure_elim fun htr_al => ?_
      exact clone_panic_tail A hCode hHandleErr p ret g
        (A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗ FrameAl) R s0 sf2
        hpc_sf2 hrun_sf2 hnull (by rw [htr_al, htr2])
    · simp only [hnull, ↓reduceIte]
      let newPtr := sf2.readReg64 .x0
      have hpNe0 : newPtr ≠ 0#64 := hnull
      have hPullOk :
          (A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
            (⌜newPtr.toNat % 1 = 0 ∧ sf2.trace = sm2.trace⌝ ∗
              A.live newPtr g.bytes.length 1 ∗ memRegion newPtr g.bytes.length)) ∗ FrameAl =
          ⌜newPtr.toNat % 1 = 0 ∧ sf2.trace = sm2.trace⌝ ∗
            (memRegion newPtr g.bytes.length ∗ vecGhostPayload A g ∗
              A.live newPtr g.bytes.length 1 ∗ A.pool ∗
              stackAt (s0.sp - 48#64) allocHookStack ∗ retPts ret r0 r1 r2 ∗
              vecHdrPts p g ∗ savedStack48 s0) := by
        dsimp only [FrameAl, newPtr]; sep_ac_rfl
      rw [hPullOk]
      refine SepWPp.pure_elim fun ⟨_, htr_al⟩ => ?_
      exact clone_memcpy_epilogue A hCode hMemcpy p ret newPtr g
        r0 r1 r2 R s0 sf2 hpos hlt63 hsp0 hpNe0
        hpc_sf2 hrun_sf2 hsp_sf2' rfl hx19_sf2 hx20_sf2 hx22_sf2
        hcs_s0_sf2 hv_s0_sf2 (htr_al.trans htr2)

private theorem stringClone_fetches_ok (A : RustAlloc) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hShim : subroutine_ok P shimAddr sessionShimSpec)
    (hAlloc : subroutine_ok P allocAddr (rustAllocSpec A))
    (hMemcpy : subroutine_ok P memcpyAddr sessionMemcpyRegionSpec)
    (hHandleErr : P.externAt? handleErrorAddr = some Rust.panicked) :
    subroutine_ok P fnAddr (stringCloneSpec A) := by
  apply subroutine_ok_of_sepWPp_pure_oom (φ := fun _ _ _ => False) (by rintro ⟨_, _, _⟩ _ _; rfl)
  rintro ⟨p, ret, g⟩ R s0 hpc hrun hpre hsp0
  dsimp only [stringCloneSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hrest⟩
  have hlt63 : g.bytes.length < 2 ^ 63 := by
    refine vecGhostAt_bytes_lt_2pow63 (A := A) (m := s0.mem) (p := p)
      (R := memRegion ret 24 ∗ (A.pool ∗ (stackAt s0.sp extHookStack ∗ R))) ?_
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  let P0 :=
    stackFrameAt s0.sp 48 ∗ memRegion ret 24 ∗ vecGhostAt A g p ∗
    A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack
  have hm0 : s0.mem ⊨ P0 ∗ (cloneFrame0 s0 ∗ R) := by
    dsimp only [P0, cloneFrame0]
    rw [extHookStack_split_48 s0.sp] at hrest
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  refine ⟨P0, cloneFrame0 s0, hm0, ?_⟩
  dsimp only [P0]
  rw [stackFrameAt48_eq s0.sp, memRegion24_eq_exists_pts ret,
      vecGhostAt_eq_header_payload A g p]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 =>
    SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun st0 =>
    SepWPp.exists_elim fun st1 => SepWPp.exists_elim fun st2 =>
    SepWPp.exists_elim fun st3 => SepWPp.exists_elim fun st4 =>
    SepWPp.exists_elim fun st5 => ?_
  have hf0 := fetch_seq_at0 hCode; have hf1 := fetch_seq_at 1 hCode
  have hf2 := fetch_seq_at 2 hCode; have hf3 := fetch_seq_at 3 hCode
  have hf4 := fetch_seq_at 4 hCode; have hf5 := fetch_seq_at 5 hCode
  have hf6 := fetch_seq_at 6 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48 : decide ((s0.sp - 48#64) &&& 15#64 = 0#64) = true :=
    decide_eq_true (beq_iff_eq.mp (spAligned_sub48 hspAl0))
  by_cases hbs : g.bytes = []
  · have hlen0 : BitVec.ofNat 64 g.bytes.length = 0#64 := by simp [hbs]
    apply SepWPp.of_sepWP (mid := fnAddr + 0x5c#64)
    wp_stp64 hf0 m1 hm1; wp_stp64 hf1 m2 hm2; wp_stp64 hf2 m3 hm3
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
      (by simp [arm64_norm, hrun]) fun sm hsm hpcm hrunm => ?_
    have hspm : sm.sp = s0.sp - 48#64 := by rw [hsm]; simp [arm64_norm]
    have hx19m : sm.readReg64 .x19 = 0#64 := by rw [hsm]; simp [arm64_norm]
    have hx20m : sm.readReg64 .x20 = ret := by rw [hsm]; simp [arm64_norm]
    have hcsm : csUpperPreserved s0 sm := by
      rw [hsm]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm]
    have hvm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      rw [hsm]; simp [calleeSavedVRegs, arm64_norm]
    have htrm : sm.trace = s0.trace := by rw [hsm]; simp [arm64_norm]
    clear hsm
    refine SepWPp.weaken_pre ?_ (clone_empty_epilogue A hCode p ret g r0 r1 r2 R s0 sm
      hbs hsp0 hpcm hrunm hspm hx19m hx20m hcsm hvm htrm)
    exact Entails.of_eq (by
      dsimp only [retPts, savedStack48, vecHdrPts, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
      sep_ac_rfl)
  · have hpos : 0 < g.bytes.length := List.length_pos_iff.mpr hbs
    have hlenNe0 : BitVec.ofNat 64 g.bytes.length ≠ 0#64 := by
      intro h0; have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      change g.bytes.length = 0 at this; omega
    apply SepWPp.of_sepWP (mid := fnAddr + 0x1c#64)
    wp_stp64 hf0 m1 hm1; wp_stp64 hf1 m2 hm2; wp_stp64 hf2 m3 hm3
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let (by simp [arm64_norm, beq_false_of_ne hlenNe0]; try bv_omega)
      (by simp [arm64_norm, hrun]) fun sm0 hsm0 hpcm0 hrunm0 => ?_
    have hspm0 : sm0.sp = s0.sp - 48#64 := by rw [hsm0]; simp [arm64_norm]
    have hx0_m0 : sm0.readReg64 .x0 = p := by rw [hsm0]; simp [arm64_norm, hx0]
    have hx19_m0 : sm0.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
      rw [hsm0]; simp [arm64_norm]
    have hx20_m0 : sm0.readReg64 .x20 = ret := by rw [hsm0]; simp [arm64_norm]
    have hcsm0 : csUpperPreserved s0 sm0 := by
      rw [hsm0]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm]
    have hvm0 : calleeSavedVRegs sm0 = calleeSavedVRegs s0 := by
      rw [hsm0]; simp [calleeSavedVRegs, arm64_norm]
    have htrm0 : sm0.trace = s0.trace := by rw [hsm0]; simp [arm64_norm]
    clear hsm0
    refine SepWPp.weaken_pre ?_ (clone_nonempty_branch A hCode hShim hAlloc hMemcpy hHandleErr
      p ret g r0 r1 r2 R s0 sm0 hpos hlt63 hsp0 hpcm0 hrunm0 hspm0 hx0_m0 hx19_m0 hx20_m0
      hcsm0 hvm0 htrm0)
    exact Entails.of_eq (by
      dsimp only [retPts, savedStack48, vecHdrPts, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
      sep_ac_rfl)

/-! ## Public Subroutine Contracts -/

theorem stringClone_hasInstrs_ok (A : RustAlloc) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hShim : subroutine_ok P shimAddr sessionShimSpec)
    (hAlloc : subroutine_ok P allocAddr (rustAllocSpec A))
    (hMemcpy : subroutine_ok P memcpyAddr sessionMemcpyRegionSpec)
    (hHandleErr : P.externAt? handleErrorAddr = some Rust.panicked) :
    subroutine_ok P fnAddr (stringCloneSpec A) :=
  stringClone_fetches_ok A
    (fun i hi => hCode.fetch_off i (BitVec.ofNat 64 (4 * i)) hi rfl)
    hShim hAlloc hMemcpy hHandleErr

theorem stringCloneName_fnOff :
    libsignalSessionCode.fnOff stringCloneHookName =
      (ls_off% "<alloc::string::String as core::clone::Clone>::clone") :=
  (ls_lemma% fnOff "<alloc::string::String as core::clone::Clone>::clone")

gen_decodes libsignalSessionCode_tree scFlatDec
  [(ls_off% "<alloc::string::String as core::clone::Clone>::clone") →
   (ls_off% "<alloc::string::String as core::clone::Clone>::clone" + 128)]

section RebaseFetches

attribute [local irreducible]
  CryptoVerification.libsignalSessionCode Program.rebase
  Program.fetch Program.externAt? Program.fnAddr Program.fnOff

local macro "close_fetch " h:ident : tactic =>
  `(tactic| (dsimp only [Nat.reduceMul, List.getElem_cons_zero, List.getElem_cons_succ]; exact $h))

private theorem stringClone_rebase_fetches (b : BitVec 64) (H : String → Option (State → State)) :
    FetchSeq (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName)
      (rustStringCloneInstrs
        ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName)
        ((libsignalSessionCode.rebase b H).fnAddr shimName)
        ((libsignalSessionCode.rebase b H).fnAddr allocName)
        ((libsignalSessionCode.rebase b H).fnAddr memcpyName)
        ((libsignalSessionCode.rebase b H).fnAddr handleErrorName)) := by
  have hBlShim :
      (libsignalSessionCode.rebase b H).fnAddr shimName -
        ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName + 0x20#64) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff shimName) -
        (BitVec.ofNat 64 (libsignalSessionCode.fnOff stringCloneHookName) + 0x20#64) := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, sub_add_base_cancel]
  have hBlAlloc :
      (libsignalSessionCode.rebase b H).fnAddr allocName -
        ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName + 0x2c#64) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff allocName) -
        (BitVec.ofNat 64 (libsignalSessionCode.fnOff stringCloneHookName) + 0x2c#64) := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, sub_add_base_cancel]
  have hBlMemcpy :
      (libsignalSessionCode.rebase b H).fnAddr memcpyName -
        ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName + 0x40#64) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff memcpyName) -
        (BitVec.ofNat 64 (libsignalSessionCode.fnOff stringCloneHookName) + 0x40#64) := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, sub_add_base_cancel]
  have hBlHandle :
      (libsignalSessionCode.rebase b H).fnAddr handleErrorName -
        ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName + 0x80#64) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff handleErrorName) -
        (BitVec.ofNat 64 (libsignalSessionCode.fnOff stringCloneHookName) + 0x80#64) := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, sub_add_base_cancel]
  rw [stringCloneName_fnOff] at hBlShim hBlAlloc hBlMemcpy hBlHandle
  dsimp only [shimName] at hBlShim
  rw [(ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")] at hBlShim
  dsimp only [allocName] at hBlAlloc
  rw [(ls_stub% "__rustc::__rust_alloc")] at hBlAlloc
  dsimp only [memcpyName] at hBlMemcpy
  rw [(ls_stub% "memcpy")] at hBlMemcpy
  dsimp only [handleErrorName] at hBlHandle
  rw [(ls_stub% "alloc::raw_vec::handle_error")] at hBlHandle
  simp only [BitVec.reduceAdd, BitVec.reduceSub] at hBlShim hBlAlloc hBlMemcpy hBlHandle
  code_fetches CryptoVerification.libsignalSessionCode scFlatDec b H
    (ls_lemma% fnOff "<alloc::string::String as core::clone::Clone>::clone")
    (ls_off% "<alloc::string::String as core::clone::Clone>::clone") 132
  rename_i hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9 hf10
    hf11 hf12 hf13 hf14 hf15 hf16 hf17 hf18 hf19 hf20 hf21
    hf22 hf23 hf24 hf25 hf26 hf27 hf28 hf29 hf30 hf31 hf32
  intro i hi
  dsimp only [rustStringCloneInstrs, List.length_cons, List.length_nil] at hi
  dsimp only [rustStringCloneInstrs]
  rw [hBlShim, hBlAlloc, hBlMemcpy, hBlHandle]
  dsimp only [stringCloneHookName]
  match i, hi with
  | 0, _ =>
    rw [show BitVec.ofNat 64 (4 * 0) = 0#64 from rfl, BitVec.add_zero]
    dsimp only [List.getElem_cons_zero]
    exact hf0
  | 1, _ => close_fetch hf1
  | 2, _ => close_fetch hf2
  | 3, _ => close_fetch hf3
  | 4, _ => close_fetch hf4
  | 5, _ => close_fetch hf5
  | 6, _ => close_fetch hf6
  | 7, _ => close_fetch hf7
  | 8, _ => close_fetch hf8
  | 9, _ => close_fetch hf9
  | 10, _ => close_fetch hf10
  | 11, _ => close_fetch hf11
  | 12, _ => close_fetch hf12
  | 13, _ => close_fetch hf13
  | 14, _ => close_fetch hf14
  | 15, _ => close_fetch hf15
  | 16, _ => close_fetch hf16
  | 17, _ => close_fetch hf17
  | 18, _ => close_fetch hf18
  | 19, _ => close_fetch hf19
  | 20, _ => close_fetch hf20
  | 21, _ => close_fetch hf21
  | 22, _ => close_fetch hf22
  | 23, _ => close_fetch hf23
  | 24, _ => close_fetch hf24
  | 25, _ => close_fetch hf25
  | 26, _ => close_fetch hf26
  | 27, _ => close_fetch hf27
  | 28, _ => close_fetch hf28
  | 29, _ => close_fetch hf29
  | 30, _ => close_fetch hf30
  | 31, _ => close_fetch hf31
  | 32, _ => close_fetch hf32
  | n + 33, hi => omega

end RebaseFetches

theorem stringClone_rebase_ok (b : BitVec 64) (A : RustAlloc)
    (H : String → Option (State → State))
    (hShim : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr shimName) sessionShimSpec)
    (hAlloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr allocName) (rustAllocSpec A))
    (hMemcpy : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hHandleErr : (libsignalSessionCode.rebase b H).externAt?
      ((libsignalSessionCode.rebase b H).fnAddr handleErrorName) = some Rust.panicked) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName) (stringCloneSpec A) :=
  stringClone_fetches_ok A (stringClone_rebase_fetches b H) hShim hAlloc hMemcpy hHandleErr

theorem stringClone_rebase_hooks_ok (b : BitVec 64) (A : RustAlloc)
    (H : String → Option (State → State))
    (hShim : H shimName = some hookNoop)
    (hAlloc : HookSat H allocName (rustAllocSpec A))
    (hMemcpy : H memcpyName = some hookMemcpy)
    (hHandleErr : H handleErrorName = some Rust.panicked) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName) (stringCloneSpec A) := by
  refine stringClone_rebase_ok b A H ?_ ?_ ?_ ?_
  · have h := hook_ok_at_raw (P := libsignalSessionCode) (b := b) (H := H)
      (name := shimName) (hname := shimName) (k := 0) (spec := sessionShimSpec)
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2") (Nat.add_zero _) (by decide)
      (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
      ⟨hookNoop, hShim, sessionShim_hookOk⟩
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  · have h := hook_ok_at_raw (P := libsignalSessionCode) (b := b) (H := H)
      (name := allocName) (hname := allocName) (k := 0) (spec := rustAllocSpec A)
      (ls_stub% "__rustc::__rust_alloc") (Nat.add_zero _) (by decide)
      (ls_hook% "__rustc::__rust_alloc") hAlloc
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  · have h := hook_ok_at_raw (P := libsignalSessionCode) (b := b) (H := H)
      (name := memcpyName) (hname := memcpyName) (k := 0) (spec := sessionMemcpyRegionSpec)
      (ls_stub% "memcpy") (Nat.add_zero _) (by decide)
      (ls_hook% "memcpy")
      ⟨hookMemcpy, hMemcpy, hookMemcpy_region_trace_ok⟩
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  · rw [← BitVec.add_zero ((libsignalSessionCode.rebase b H).fnAddr handleErrorName)]
    rw [Program.externAt?_fnAddr_add
      (ls_stub% "alloc::raw_vec::handle_error") (Nat.add_zero _) (by decide),
      (ls_hook% "alloc::raw_vec::handle_error")]
    exact hHandleErr

theorem stringClone_withPanics_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hShim : ext shimName = some hookNoop)
    (hAlloc : HookSat ext allocName (rustAllocSpec A))
    (hMemcpy : ext memcpyName = some hookMemcpy) :
    subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr stringCloneHookName)
      (stringCloneSpec A) := by
  refine stringClone_rebase_hooks_ok b A (Rust.withPanics ext) ?_ ?_ ?_ ?_
  · have hnp : Rust.isPanicSymbol shimName = false := by simp [shimName, Rust.isPanicSymbol]
    simp [Rust.withPanics, hnp, hShim]
  · obtain ⟨f, hf, hok⟩ := hAlloc
    have hnp : Rust.isPanicSymbol allocName = false := by simp [allocName, Rust.isPanicSymbol]
    exact ⟨f, by simp [Rust.withPanics, hnp, hf], hok⟩
  · have hnp : Rust.isPanicSymbol memcpyName = false := by simp [memcpyName, Rust.isPanicSymbol]
    simp [Rust.withPanics, hnp, hMemcpy]
  · have hp : Rust.isPanicSymbol handleErrorName = true := by
      simp [handleErrorName, Rust.isPanicSymbol]
    simp [Rust.withPanics, hp]

theorem stringClone_trTrapProgAt_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr stringCloneHookName) (stringCloneSpec A) := by
  refine stringClone_rebase_ok b A (Rust.withPanics _) ?_ ?_ ?_ ?_
  · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      shim_ok_at_trap b C abs shimName 0 (Nat.add_zero _)
  · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      alloc_ok_at_trap b C A abs hA allocName 0 (Nat.add_zero _)
  · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      session_memcpy_region_ok_at_trap b C abs memcpyName 0 (Nat.add_zero _)
  · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      panic_at_handle_error_trap b C abs handleErrorName 0 (Nat.add_zero _)

theorem stringClone_tripleRatchetProgAt_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr stringCloneHookName) (stringCloneSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr stringCloneHookName]
  exact subroutine_ok_kit_of_trTrap (stringClone_trTrapProgAt_ok b C A abs hA)

end LibsignalBinary.Proofs.Common.StringCloneFlat
