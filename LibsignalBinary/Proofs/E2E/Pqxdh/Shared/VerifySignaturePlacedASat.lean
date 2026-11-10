/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlacedA -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain

/-!
# `HookSat`-backed `black_box` Sibling of `VerifySignaturePlacedA` (`VerifySignaturePlacedASat`)

Replaces `blackBox : H lsBlackBoxU8Sym = some blackBoxHook` in `VerifySignaturePlacedHooks` and
`VerifySignaturePlacedHooks'` (`VerifySignaturePlacedA.lean:130, 145`) with
`blackBox : HookSat H lsBlackBoxU8Sym blackBoxSpecSat`, and proves `verifySig_seg3b_placed_sat`
with a token-identical conclusion by splitting `64` B (`ctEqSliceMemSpec16`) out of
`stackAt fsp pqxdhHookStack` (`4096` B).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

open scoped CryptoVerification.E2E.Pqxdh.Shared

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlacedASat

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkPC_204 blkPC_213 blkPl_204 blkPl_213 lsBlackBoxU8Sym lsMemcpySym
   ls_blockPlacement_base ls_hook_ok_any lscall_blk lsmpl sepWP_seq_lscl withMemEq)
open CryptoVerification.E2E.Pqxdh.Shared
  (VerifySignaturePlacedHooks VerifySignaturePlacedHooks' VerifySignaturePrims
   and64_mask255_ite_1_0 bv_add_neg64 bv_sub_sub_lit bytesToBv8 compressInPlaceStubSpec
   compressInPlaceStubSpecPlaced cryptoLeafStubSpec csinc_eq_zero32_ite_1_0 dalekDoubleMulStubSpec
   dalekDoubleMulStubSpecPlaced dalekMontToEdStubSpec dalekMontToEdStubSpecPlaced
   exists_sig_capS_cells fitBv8_of_length_eq lsDalekCompressSym lsDalekDoubleMulSym lsDalekEdNegSym
   lsDalekScalarModSym lsDalekScalarWideSym lsSha512CompressSym lsVerifyMemsetSym
   lsVerifyMontToEdSym pointsToBytes_32_merge_128 pointsToBytes_entails_memRegion_n pqxdhHookStack
   readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sClamped_buf_pre
   sha512CompressOutBytes sig_split_32 sp_setMem_setPC_pre sp_setPC_pre
   truncate8_zeroExtend32_and7f x0_cteq_simplify)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec sessionMemsetSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpecSat ctEqSliceMemSpec16 ct_eq_mem_placed_ok_16_sat hookSat_blackBox_of_eq)
open SignalPqxdh (Bytes Primitives)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64

private theorem calleeSavedVRegs_setPC_pre_placed (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := calleeSavedVRegs_setPC s pc

private theorem calleeSavedVRegs_setMem_setPC_pre_placed (s : State) (m : Memory) (pc : BitVec 64) :
    calleeSavedVRegs ((s.setMem m).setPC pc) = calleeSavedVRegs s := by
  rw [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem]

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  calleeSavedVRegs_setPC_pre_placed calleeSavedVRegs_setMem_setPC_pre_placed

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  and64_mask255_ite_1_0 csinc_eq_zero32_ite_1_0

/-- `HookSat`-backed `black_box` sibling of `VerifySignaturePlacedHooks`
(`VerifySignaturePlacedA.lean:130`). -/
structure VerifySignaturePlacedHooksSat (P : Primitives) (H : LibsignalHooks) : Prop where
  memcpy         : HookSat H lsMemcpySym sessionMemcpyRegionSpec
  memset         : HookSat H lsVerifyMemsetSym (sessionMemsetSpec pqxdhHookStack)
  blackBox       : HookSat H lsBlackBoxU8Sym blackBoxSpecSat
  montToEd       : HookSat H lsVerifyMontToEdSym (dalekMontToEdStubSpec P)
  compress       : HookSat H lsDalekCompressSym (cryptoLeafStubSpec P.compress 160 32)
  edNeg          : HookSat H lsDalekEdNegSym (cryptoLeafStubSpec P.edNeg 160 160)
  sha512Compress : HookSat H lsSha512CompressSym
                     (compressInPlaceStubSpec (sha512CompressOutBytes P) 64 128)
  scalarWide     : HookSat H lsDalekScalarWideSym (cryptoLeafStubSpec P.scalarFromWide 64 32)
  scalarMod      : HookSat H lsDalekScalarModSym
                     (cryptoLeafStubSpec P.scalarFromBytesModOrder 32 32)
  doubleMul      : HookSat H lsDalekDoubleMulSym (dalekDoubleMulStubSpec P)

/-- `HookSat`-backed `black_box` sibling of `VerifySignaturePlacedHooks'`
(`VerifySignaturePlacedA.lean:145`). -/
structure VerifySignaturePlacedHooks'Sat (P : Primitives) (H : LibsignalHooks) : Prop where
  memcpy         : HookSat H lsMemcpySym sessionMemcpyRegionSpec
  memset         : HookSat H lsVerifyMemsetSym (sessionMemsetSpec pqxdhHookStack)
  blackBox       : HookSat H lsBlackBoxU8Sym blackBoxSpecSat
  montToEd       : HookSat H lsVerifyMontToEdSym (dalekMontToEdStubSpecPlaced P)
  compress       : HookSat H lsDalekCompressSym (cryptoLeafStubSpec P.compress 160 32)
  edNeg          : HookSat H lsDalekEdNegSym (cryptoLeafStubSpec P.edNeg 160 160)
  sha512Compress : HookSat H lsSha512CompressSym
                     (compressInPlaceStubSpecPlaced (sha512CompressOutBytes P) 64 128)
  scalarWide     : HookSat H lsDalekScalarWideSym (cryptoLeafStubSpec P.scalarFromWide 64 32)
  scalarMod      : HookSat H lsDalekScalarModSym
                     (cryptoLeafStubSpec P.scalarFromBytesModOrder 32 32)
  doubleMul      : HookSat H lsDalekDoubleMulSym (dalekDoubleMulStubSpecPlaced P)

/-- Exact-to-`HookSat` bridge `VerifySignaturePlacedHooks → VerifySignaturePlacedHooksSat`. -/
theorem VerifySignaturePlacedHooks.toSat {P : Primitives} {H : LibsignalHooks}
    (h : VerifySignaturePlacedHooks P H) : VerifySignaturePlacedHooksSat P H where
  memcpy         := h.memcpy
  memset         := h.memset
  blackBox       := hookSat_blackBox_of_eq h.blackBox
  montToEd       := h.montToEd
  compress       := h.compress
  edNeg          := h.edNeg
  sha512Compress := h.sha512Compress
  scalarWide     := h.scalarWide
  scalarMod      := h.scalarMod
  doubleMul      := h.doubleMul

/-- Exact-to-`HookSat` bridge `VerifySignaturePlacedHooks' → VerifySignaturePlacedHooks'Sat`. -/
theorem VerifySignaturePlacedHooks'.toSat {P : Primitives} {H : LibsignalHooks}
    (h : VerifySignaturePlacedHooks' P H) : VerifySignaturePlacedHooks'Sat P H where
  memcpy         := h.memcpy
  memset         := h.memset
  blackBox       := hookSat_blackBox_of_eq h.blackBox
  montToEd       := h.montToEd
  compress       := h.compress
  edNeg          := h.edNeg
  sha512Compress := h.sha512Compress
  scalarWide     := h.scalarWide
  scalarMod      := h.scalarMod
  doubleMul      := h.doubleMul

theorem VerifySignaturePlacedHooks'Sat.of_hooks {P : Primitives} {H : LibsignalHooks}
    (h : VerifySignaturePlacedHooksSat P H) : VerifySignaturePlacedHooks'Sat P H where
  memcpy         := h.memcpy
  memset         := h.memset
  blackBox       := h.blackBox
  montToEd       := h.montToEd
  compress       := h.compress
  edNeg          := h.edNeg
  sha512Compress := h.sha512Compress
  scalarWide     := h.scalarWide
  scalarMod      := h.scalarMod
  doubleMul      := h.doubleMul

private theorem stackAt_hook_split_64 (sp : BitVec 64) :
    stackAt sp pqxdhHookStack =
      memRegion (sp - 4096#64) 4032 ∗ memRegion (sp - 64#64) 64 := by
  simp only [stackAt, pqxdhHookStack]
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 4096) (n := 4032) (k := 64)
    (b' := sp - 64#64) rfl (by bv_omega) (by decide)

private def pqxdhCtEqMemSpec16 (m : Memory) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s0 =>
    ⌜s0.readReg64 .x0 = p1 ∧ s0.readReg64 .x1 = p2 ∧ s0.sp = sp ∧
      k1.length = 32 ∧ k2.length = 32 ∧ s0.mem = m⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ memRegion (sp - 64#64) 64
  post := ctEqSliceMemSpec16.post

private theorem pqxdhCtEq_call_ok_sat [LibsignalPlacement] {callerProg : Program}
    {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hbb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 213) (pqxdhCtEqMemSpec16 m) := by
  have hblk : subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (lsmpl.base 213)
      ctEqSliceMemSpec16 := by
    simpa only [ls_blockPlacement_base] using ct_eq_mem_placed_ok_16_sat hbb
  exact subroutine_ok_mono (lscall_blk (callerProg := callerProg) hblk hcl hi (by decide) (by decide))
    (fun ⟨p1, k1, p2, k2, sp⟩ R s0 hp => by
      dsimp only [pqxdhCtEqMemSpec16] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rcases hp with ⟨⟨hx0, hx1, hsp0, hk1, hk2, hm⟩, hspat⟩
      dsimp only [withMemEq, ctEqSliceMemSpec16]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hm, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hsp0, hk1, hk2⟩, hspat⟩)
    (fun _ _ _ _ hq => hq)

set_option maxHeartbeats 2400000 in
/-- `HookSat` `black_box` sibling of `verifySig_seg3b_placed` (`VerifySignaturePlacedA.lean:535`)
with token-identical conclusion. -/
theorem verifySig_seg3b_placed_sat [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hWF : VerifySignaturePrims P)
    (hH : VerifySignaturePlacedHooks'Sat P H) (s : State) (fsp sigPtr : BitVec 64)
    (sig minusCapA hScalar : Bytes) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsig : sig.length = 64) (hnegA : minusCapA.length = 160) (hh : hScalar.length = 32)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 992#64)
    (hsp : s.sp = fsp) (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H)
      ((blkPl_204).base + 1100#64) s
      (((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
       ((fsp + 8#64) ↦₆₄ sigPtr) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
       ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗ ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗
       cells (fsp + 800#64) 4 ∗ memRegion (fsp + 832#64) 128 ∗ memRegion (fsp + 1008#64) 32 ∗
       stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
          ((fsp + 8#64) ↦₆₄ sigPtr) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
          ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗ ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗
          memRegion (fsp + 800#64) 160 ∗ memRegion (fsp + 1008#64) 32 ∗ stackAt fsp pqxdhHookStack ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 1100#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 0#5) =
          (let sClamped := (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]
           let sScalar := P.scalarFromBytesModOrder sClamped
           let capRCheck := P.compress (P.doubleScalarMulBasepoint hScalar minusCapA sScalar)
           if (capRCheck == sig.take 32) = true then 1#64 else 0#64) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmod := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.scalarMod
  have hdmul := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.doubleMul
  have hcomp := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.compress
  have hbb := hH.blackBox
  clear hH
  apply sepWP_seq_lscl hcl (mid := (blkPl_204).base + 1072#64)
  obtain ⟨q0_lo, q0_hi, q1_lo, q1_hi, hsig_q0, hsig_q1, hbuf_q0, hbuf_q1⟩ :=
    exists_sig_capS_cells hsig
  cells_pre_unfold_fast
  wp_extract_exists
  rename_i v0 v1 v2 v3
  have hsbuf := sClamped_buf_pre (fsp + 800#64) v0 v1 v2 v3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsbuf
  apply ProofLib.SepWP.replace_pre (hPQ := hsbuf) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig_q0 sigPtr)) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq ((hsig_q0 sigPtr).symm.trans (hsig_q1 sigPtr))) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig_q1 sigPtr).symm) (by sep_frame)
  have hbuf0 := hbuf_q0 (fsp + 800#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbuf0
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf0) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  apply SepWP.exists_left; intro _
  wp_steps
  wp_simp_pre_fast [truncate8_zeroExtend32_and7f]
  have hbuf1 := hbuf_q1 (fsp + 800#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbuf1
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hbuf1) (by sep_frame)
  have hsClamped_len :
      ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]).length = 32 := by
    simp [hsig]
  wp_call hmod ⟨fsp + 800#64, (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F],
    fsp + 1008#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.scalarFromBytesModOrder_len _)]
  wp_steps
  have hsClamped_bv_len :
      (bytesToBv8 (List.take 31 (List.drop 32 sig) ++
        [(List.drop 32 sig).getD 31 0 &&& 127])).length = 32 := by
    simp [bytesToBv8, hsig]
  have hm160 := pointsToBytes_32_merge_128 (fsp + 800#64) _ hsClamped_bv_len
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm160
  apply ProofLib.SepWP.replace_pre (hPQ := hm160) (by sep_frame)
  have hsScalar_len :
      (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
        [(List.drop 32 sig).getD 31 0 &&& 127])).length = 32 :=
    hWF.scalarFromBytesModOrder_len _
  wp_call hdmul ⟨hScalar, minusCapA,
    P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
      [(List.drop 32 sig).getD 31 0 &&& 127]),
    fsp + 768#64, fsp + 400#64, fsp + 1008#64, fsp + 800#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.doubleScalarMulBasepoint_len _ _ _)]
  wp_steps
  have hsScalar_bv_len :
      (bytesToBv8 (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
        [(List.drop 32 sig).getD 31 0 &&& 127]))).length = 32 := by
    simp [bytesToBv8, hWF.scalarFromBytesModOrder_len]
  have hm32_1008 := pointsToBytes_entails_memRegion_n (fsp + 1008#64) _ hsScalar_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm32_1008) (by sep_frame)
  have hdmul_len :
      (P.doubleScalarMulBasepoint hScalar minusCapA
        (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
          [(List.drop 32 sig).getD 31 0 &&& 127]))).length = 160 :=
    hWF.doubleScalarMulBasepoint_len _ _ _
  wp_call hcomp ⟨fsp + 800#64,
    P.doubleScalarMulBasepoint hScalar minusCapA
      (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
        [(List.drop 32 sig).getD 31 0 &&& 127])),
    fsp + 1008#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.compress_len _)]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl_call
  have hcteq := pqxdhCtEq_call_ok_sat (callerProg := (blkPC_204).rebase (blkPl_204).base H)
    hbb hcl_call
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig)) (by sep_frame)
  wp_simp_pre_fast [hsp_sf_2, hsp_sf_1, hsp_sf, hsp, stackAt_hook_split_64]
  have hcapR_bv_len :
      (bytesToBv8 (P.compress (P.doubleScalarMulBasepoint hScalar minusCapA
        (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
          [(List.drop 32 sig).getD 31 0 &&& 127]))))).length = 32 := by
    simp [bytesToBv8, hWF.compress_len]
  have hsig32_bv_len : (bytesToBv8 (sig.take 32)).length = 32 := by simp [bytesToBv8, hsig]
  wp_call hcteq (fsp + 1008#64,
    bytesToBv8 (P.compress (P.doubleScalarMulBasepoint hScalar minusCapA
      (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
        [(List.drop 32 sig).getD 31 0 &&& 127])))),
    sigPtr, bytesToBv8 (sig.take 32), fsp)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig).symm)
    (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (stackAt_hook_split_64 fsp).symm)
    (by sep_frame)
  have hdmul_bv_len :
      (bytesToBv8 (P.doubleScalarMulBasepoint hScalar minusCapA
        (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
          [(List.drop 32 sig).getD 31 0 &&& 127])))).length = 160 := by
    simp [bytesToBv8, hWF.doubleScalarMulBasepoint_len]
  have hm160_800 := pointsToBytes_entails_memRegion_n (fsp + 800#64) _ hdmul_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm160_800) (by sep_frame)
  have hm32_capR := pointsToBytes_entails_memRegion_n (fsp + 1008#64) _ hcapR_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm32_capR) (by sep_frame)
  wp_simp_pre_fast [hsp_sf_3, hsp_sf_2, hsp_sf_1, hsp_sf, hsp]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by sep_ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_,
    by wp_norm_goal, by wp_norm_goal⟩
  wp_norm_goal
  exact x0_cteq_simplify _ _

end LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlacedASat
