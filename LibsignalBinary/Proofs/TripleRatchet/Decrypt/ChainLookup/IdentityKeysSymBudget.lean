/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSym
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `VmPreserved` Relocatable Step Lemmas for Segment S0 (`IdentityKeys`)

Records `VmPreserved` across all six block `130` (`try_decrypt_with_state::<HookRng>`) Segment S0
symbolic execution steps so budget callers can transport `A.pool lim st` via `A.pool_transport`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (IdentityKey PublicKey)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement lsmpl sepWP_seq_lscl withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (TryDecryptGhost logOff)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  isSameAccountSpec isSameAccountStack localIdentityKeyStack localIdentityOkAt
  remoteIdentityKeyStack remoteIdentityOkAt
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (tryDecryptSavedRegs)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (
  blkLib_eq_131 blkPC_131 blkPl_131 bytes9_64_8_eq_8_64 localGroupA localGroupA_1280_to_B
  localGroupA_401_to_B localGroupB logOff_tryDecryptDummyImg remoteGroupC remoteGroupD
  tryDecryptDummyImg words4At words8At
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  localIdentityKeyPlacedSpec remoteIdentityKeyPlacedSpec
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Lift a pure non-`svc #0` Block `130` segment with `NonSyscallPreserved` (`hooksException H`
preserves the `Program.rebase` head required by generated `pairStep` lemmas). -/
theorem sepWP_blk130_vm [LibsignalPlacement] {H : String → Option (State → State)}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_131).rebase (blkPl_131).base (hooksException H))
        mid (s.setMem m_strip) Pre (fun sm' Pm =>
          ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            SepWP ((blkPC_131).rebase (blkPl_131).base H) target (sm'.setMem m_real) Pm post)) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) target s Pre post :=
  sepWP_seg_ls_vm
    (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
    blkLib_eq_131 (mid := mid) (hseg := hseg)

/-- Pause `wp_steps` at an intermediate `mid` PC so spatial hypotheses can be rewritten before
continuing. -/
private theorem sepWP_pause {prog : Program} {mid tgt : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (h : SepWP prog mid s Pre (fun sm Pm => SepWP prog tgt sm Pm post)) :
    SepWP prog tgt s Pre post :=
  SepWP.seq h (fun _ _ _ _ hcont => hcont)

theorem identityKeys_prologue_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hlocal : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 28)
      (withLsCodeLoaded lsmpl (localIdentityKeyPlacedSpec A)))
    (x : TryDecryptGhost) (s0 : State)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 w_sp0 w_sp48 : BitVec 64)
    (h_pc : s0.pc = (blkPl_131).base) (h_run : s0.status = .Running) (h_sp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.ret) (hx1 : s0.readReg64 .x1 = x.ss) (hx2 : s0.readReg64 .x2 = x.remA)
    (hx3 : s0.readReg64 .x3 = x.locA) (hx4 : s0.readReg64 .x4 = x.msgA)
    (hx5 : (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType)
    (hdeser_loc : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 84#64) s0
      (words4At (s0.sp - 96#64) r0 r1 r2 r3 ∗ words8At (s0.sp - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
       (sp ↦₆₄ w_sp0) ∗ ((sp + 48#64) ↦₆₄ w_sp48) ∗ vecGhostAt A x.G.localIk x.ss ∗
       memRegion (sp + 400#64) 33 ∗ logOff tryDecryptDummyImg ∗ stackAt sp localIdentityKeyStack)
      (fun sf P_f =>
        VmPreserved s0 sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = x.ret ∧ sf.readReg64 .x20 = sp + 320#64 ∧
        sf.readReg64 .x21 = x.ss ∧ sf.readReg64 .x22 = x.msgA ∧
        sf.readReg64 .x23 = sp + 1280#64 ∧ (sf.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        sf.readReg64 .x25 = x.locA ∧ sf.readReg64 .x29 = s0.sp - 96#64 ∧
        (P_f ⊢ tryDecryptSavedRegs s0.sp s0 ∗ (sp ↦₆₄ 0#64) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
          vecGhostAt A x.G.localIk x.ss ∗ localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗
          logOff tryDecryptDummyImg ∗ stackAt sp localIdentityKeyStack)) := by
  dsimp only
  simp only [withLsCodeLoaded, localIdentityKeyPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Getters.localIdentityKeyPlacedSpec,
    sepConj_assoc] at hlocal
  unfold tryDecryptSavedRegs words8At words4At
  simp only [logOff_tryDecryptDummyImg, BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 28)
  apply sepWP_blk130_vm (mid := lsmpl.base 28); intro m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have hvm1 : VmPreserved s0 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_call => ?_
  wp_apply; wp_finish
  refine ⟨hvm1.trans (by assumption),
    by simp only [wp_norm, arm64_norm] at *; bv_omega,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], ?_,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], ?_⟩
  · rw [← hx5]; simp_all [wp_norm, arm64_norm]
  · have hsp_loc : s0.sp - 1104#64 = s0.sp - 1504#64 + 400#64 := by bv_omega
    have hsp_48 : s0.sp - 1456#64 = s0.sp - 1504#64 + 48#64 := by bv_omega
    rw [hsp_loc, hsp_48]; exact Entails.of_eq (by sep_ac_rfl)

theorem identityKeys_copy_local_ik_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (x : TryDecryptGhost) (s0 s : State)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (w0 w1 w2 : BitVec 64) (b31 : BitVec 8)
    (d0 d1 d2 d3 d4 d5 d6 : BitVec 8) (dw0 dw1 dw2 : BitVec 64) (db31 : BitVec 8)
    (u1104 : BitVec 64) (u1112 : BitVec 8)
    (h_pc : s.pc = (blkPl_131).base + 84#64) (h_run : s.status = .Running)
    (h_sp : s.sp = s0.sp - 1504#64) (h_sp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64) (hx21 : s.readReg64 .x21 = x.ss)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx29 : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 156#64) s
      (((sp + 400#64) ↦₈ 0#8) ∗ localGroupA (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
       localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗
       ((sp + 1104#64) ↦₆₄ u1104) ∗ ((sp + 1112#64) ↦₈ u1112))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x0 = x.ss ∧ sf.readReg64 .x8 = sp + 400#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = sp + 320#64 ∧
        sf.readReg64 .x21 = x.ss ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 1280#64 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 ∧
        (P_f ⊢ ((sp + 400#64) ↦₈ 0#8) ∗
          localGroupB (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
          localGroupB (sp + 1280#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
          ((sp + 1104#64) ↦₆₄ w2) ∗ ((sp + 1112#64) ↦₈ b31))) := by
  dsimp only; unfold localGroupA localGroupB
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 156#64); intro m_strip
  wp_steps
  rw [localGroupA_401_to_B (s0.sp - 1504#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31]; wp_steps
  rw [localGroupA_1280_to_B (s0.sp - 1504#64) b0 b1 b2 b3 d4 d5 d6 dw0 dw1 dw2 db31]; wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  refine ⟨hvm, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl)⟩

theorem identityKeys_call_remote_ik_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hrem : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 29)
      (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (x : TryDecryptGhost) (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h_pc : s.pc = (blkPl_131).base + 156#64) (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true) (hx0 : s.readReg64 .x0 = x.ss)
    (hx8 : s.readReg64 .x8 = s.sp + 400#64)
    (hdeser_rem :
      match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 160#64) s
      (vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s.sp + 400#64) 34 ∗
       logOff tryDecryptDummyImg ∗ stackAt s.sp remoteIdentityKeyStack)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = s.sp ∧ sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        (P_f ⊢ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
          remoteIdentityOkAt (s.sp + 400#64) x.st.remoteIdentity ∗
          logOff tryDecryptDummyImg ∗ stackAt s.sp remoteIdentityKeyStack)) := by
  simp only [withLsCodeLoaded, remoteIdentityKeyPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Getters.remoteIdentityKeyPlacedSpec,
    logOff_tryDecryptDummyImg, sepConj_assoc] at hrem ⊢
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 29)
  apply sepWP_blk130_vm (mid := lsmpl.base 29); intro m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have hvm1 : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_call => ?_
  wp_apply; wp_finish
  refine ⟨hvm1.trans (by assumption), by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    Entails.of_eq (by sep_ac_rfl)⟩

theorem identityKeys_remote_ik_common_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (s : State) (tag : BitVec 8)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (u352 : BitVec 64) (u360 : BitVec 8) (u976 : BitVec 32) (u980 u981 : BitVec 8)
    (h_pc : s.pc = (blkPl_131).base + 160#64) (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true) (hx20 : s.readReg64 .x20 = s.sp + 320#64) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 384#64) s
      (((s.sp + 400#64) ↦₈ 0#8) ∗ ((s.sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (s.sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
       ((s.sp + 352#64) ↦₆₄ u352) ∗ ((s.sp + 360#64) ↦₈ u360) ∗
       ((s.sp + 976#64) ↦₃₂ u976) ∗ ((s.sp + 980#64) ↦₈ u980) ∗ ((s.sp + 981#64) ↦₈ u981))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = s.sp ∧ sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∧
        sf.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21 ∧
        sf.readReg64 .x10 = BitVec.zeroExtend 64 b22 ∧
        sf.readReg64 .x11 = BitVec.zeroExtend 64 tag ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.sp + 320#64 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        (P_f ⊢ ((s.sp + 400#64) ↦₈ 0#8) ∗ ((s.sp + 401#64) ↦₈ tag) ∗
          remoteGroupC (s.sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
          ((s.sp + 352#64) ↦₆₄ w3) ∗ ((s.sp + 360#64) ↦₈ b31) ∗
          ((s.sp + 976#64) ↦₃₂ w0) ∗ ((s.sp + 980#64) ↦₈ b4) ∗ ((s.sp + 981#64) ↦₈ b5))) := by
  unfold remoteGroupC; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 384#64); intro m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  refine ⟨hvm, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], ?_⟩
  have hb4 : BitVec.zeroExtend 8 (b5 ++ b4) = b4 := by bv_kernel
  have hb5 : BitVec.extractLsb' 8 8 (BitVec.zeroExtend 32 (b5 ++ b4)) = b5 := by bv_kernel
  rw [hb4, hb5]; exact Entails.of_eq (by sep_ac_rfl)

theorem identityKeys_remote_none_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (s : State) (u1024 u1032 u1280 : BitVec 64)
    (h_pc : s.pc = (blkPl_131).base + 384#64) (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true) (hx11 : s.readReg64 .x11 = 0#64)
    (hx29 : s.readReg64 .x29 = s.sp + 1408#64) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s
      (((s.sp + 1024#64) ↦₆₄ u1024) ∗ ((s.sp + 1032#64) ↦₆₄ u1032) ∗
       ((s.sp + 1280#64) ↦₆₄ u1280) ∗ logOff tryDecryptDummyImg)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = s.sp ∧ sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (sf.readReg64 .x1).setWidth 32 = 0#32 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x29 = s.sp + 1408#64 ∧
        (P_f ⊢ memRegion (s.sp + 1024#64) 16 ∗ memRegion (s.sp + 1280#64) 8 ∗ logOff tryDecryptDummyImg)) := by
  simp only [logOff_tryDecryptDummyImg]
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 472#64); intro m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  refine ⟨hvm, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], ?_⟩
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))) ?_
  rw [show (s.sp + 1032#64) = (s.sp + 1024#64) + 8#64 by bv_omega,
      ← sepConj_assoc, ← memRegion_split (s.sp + 1024#64) 8 8 (by decide)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem identityKeys_remote_some_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hsame : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (withVmPreserved isSameAccountSpec)))
    (x : TryDecryptGhost) (remIk : IdentityKey) (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8) (u400 : BitVec 64) (u408 : BitVec 8)
    (dw0 : BitVec 32) (db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 : BitVec 8)
    (dw3 : BitVec 64) (db31 : BitVec 8)
    (h_pc : s.pc = (blkPl_131).base + 384#64) (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s.readReg64 .x11 = 1#64) (hx20 : s.readReg64 .x20 = s.sp + 320#64)
    (hx25 : s.readReg64 .x25 = x.locA) (hx29 : s.readReg64 .x29 = s.sp + 1408#64)
    (hrem_eq : ∀ a : BitVec 64, (a ↦ₛ remIk.publicKey.bytes.toList) =
      remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s
      (((s.sp + 48#64) ↦₆₄ x.remA) ∗ ((s.sp + 400#64) ↦₆₄ u400) ∗ ((s.sp + 408#64) ↦₈ u408) ∗
       ((s.sp + 352#64) ↦₆₄ w3) ∗ ((s.sp + 360#64) ↦₈ b31) ∗ ((s.sp + 976#64) ↦₃₂ w0) ∗
       ((s.sp + 980#64) ↦₈ b4) ∗ ((s.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗ stackAt s.sp isSameAccountStack)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = s.sp ∧ sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (sf.readReg64 .x1).setWidth 32 = 0#32 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.sp + 320#64 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = x.locA ∧
        sf.readReg64 .x29 = s.sp + 1408#64 ∧
        (P_f ⊢ ((s.sp + 48#64) ↦₆₄ x.remA) ∗ ((s.sp + 400#64) ↦₈ b6) ∗
          ((s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
          ((s.sp + 352#64) ↦₆₄ w3) ∗ ((s.sp + 360#64) ↦₈ b31) ∗ ((s.sp + 976#64) ↦₃₂ w0) ∗
          ((s.sp + 980#64) ↦₈ b4) ∗ ((s.sp + 981#64) ↦₈ b5) ∗
          ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗
          ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          stackAt s.sp isSameAccountStack)) := by
  simp only [withLsCodeLoaded, withVmPreserved, isSameAccountSpec, sepConj_assoc] at hsame
  unfold remoteGroupD; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 17)
  apply sepWP_blk130_vm (mid := lsmpl.base 17); intro m_strip
  apply sepWP_pause (mid := (blkPl_131).base + 404#64)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  have hb14 : BitVec.zeroExtend 8 (pack64 b14 b15 b16 b17 b18 b19 b20 b21) = b14 := by unfold pack64; bv_kernel
  have h400 :
      ((s.sp + 400#64) ↦₆₄ pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∗ (s.sp + 408#64) ↦₈ b14) =
      ((s.sp + 400#64) ↦₈ b6 ∗ (s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      bytes9_64_8_eq_8_64 (s.sp + 400#64) b6 b7 b8 b9 b10 b11 b12 b13 b14
  rw [hb14, ← sepConj_assoc ((s.sp + 400#64) ↦₆₄ _), h400, sepConj_assoc]
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have hvm1 : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_call => ?_
  have hb4 : BitVec.zeroExtend 8 (b5 ++ b4) = b4 := by bv_kernel
  have hb5 : BitVec.extractLsb' 8 8 (BitVec.zeroExtend 32 (b5 ++ b4)) = b5 := by bv_kernel
  have hb6 : BitVec.zeroExtend 8 (pack64 b6 b7 b8 b9 b10 b11 b12 b13) = b6 := by unfold pack64; bv_kernel
  have hb15_22 :
      BitVec.truncate 64 ((BitVec.zeroExtend 64 b22 ++ pack64 b14 b15 b16 b17 b18 b19 b20 b21) >>> 8) =
        pack64 b15 b16 b17 b18 b19 b20 b21 b22 := by unfold pack64; bv_kernel
  have hrem56 :
      ((s.sp + 56#64) ↦₃₂ w0 ∗ (s.sp + 60#64) ↦₈ b4 ∗ (s.sp + 61#64) ↦₈ b5 ∗
       (s.sp + 62#64) ↦₈ b6 ∗ (s.sp + 63#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14 ∗
       (s.sp + 71#64) ↦₆₄ pack64 b15 b16 b17 b18 b19 b20 b21 b22 ∗
       (s.sp + 79#64) ↦₆₄ w3 ∗ (s.sp + 87#64) ↦₈ b31) =
      ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) := by
    simpa only [remoteGroupD, BitVec.add_assoc, BitVec.reduceAdd] using (hrem_eq (s.sp + 56#64)).symm
  rw [hb4, hb5, hb6, hb15_22, hrem56]
  wp_apply
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 472#64); intro m_strip2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real2 hnsp2 => ?_
  have hvm3 : VmPreserved _ _ := hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  refine ⟨hvm1.trans ((by assumption : VmPreserved _ _).trans hvm3),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    Entails.of_eq (by sep_ac_rfl)⟩

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget
