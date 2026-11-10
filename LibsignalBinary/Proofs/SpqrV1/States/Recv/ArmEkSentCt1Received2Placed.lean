/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ekSentCt1Received` Arm, Part 2 (Relocatable)

Relocatable `[LibsignalPlacement]` post-call `.error` / `.stillReceiving` / `.done` paths,
`eq_ct2` branch, and top-level `.ekSentCt1Received` contract
`states_recv_ekSentCt1Received_placed_ok_ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs
  Recv.none2Cap_add_two_beq_zero Recv.none2Cap_add_two_bne_zero
  Recv.noneCap_add_two_beq_zero Recv.noneCap_add_two_bne_zero
  Recv.noneCap_add_one_beq_zero Recv.noneCap_add_one_bne_zero
  messagePayloadTag_ct2
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post onPanic : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog target sm P_mid post onPanic) :
    SepWPp prog target s P post onPanic :=
  SepWPp.of_sepWP (CryptoVerification.sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm hpc hrun hQ hcl'))))

private theorem sepWPp_seq_clean_lscro [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post onPanic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog target sm P_mid post onPanic) :
    SepWPp prog target s P post onPanic :=
  SepWPp.of_sepWP (sepWP_seq_lscro hcro (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcro' =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm hpc hrun hQ hcro'))))

/-! ## 1. Post-Call `.error (.err .macVerifyFailed)` Path without `hcl` (`+4384 -> s0.x30`) -/

/-- Relocatable post-call block `0x56574..0x565a4 -> 0x59fd0..0x59ff0` (`+4384 -> s0.x30`, Block `332`)
    when `recv_ct2_chunk` returns `.error (.err .macVerifyFailed)` (using `sepWP_seq_cut`). -/
theorem ekSentCt1Received_post_call_err_56574_cut_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (outA : BitVec 64)
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 4384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        ekSentCt1ReceivedRecvChunkResultAt A (F := F) ((s0.sp - 4240#64) + 976#64)
          (.error (.err .macVerifyFailed)) ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.error (.err .macVerifyFailed)) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hep := @states_recv_epilogue_59fd0_placed _ ext s0
  rw [lsmpl_base_332_eq] at hpc hep
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hep ⊢
  refine sepWP_seq_cut ((blkPl_332).base + 19324#64) ?_
  refine SepWP.fold (err_result_976_extract A (F := F) (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i w1 w2 w3
  refine SepWP.fold (memRegion_960_split_err4 outA) (by sep_focus) ?_
  wp_pull_exists; rename_i v0 v8 v16 v24
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  subst hx19
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, none2Cap, Reg.x19]
    simp only [BitVec.add_assoc, arm64_norm]
  wp_steps
  subst hsp0
  refine SepWP.done rfl hrun ?_
  let sp_err : SendEkSpills := { sp with w61 := w3 }
  have h880_976 := err_result_976_fold_880 (s0.sp - 4240#64) w1 w2 w3
  have h880_1856 :
      memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ⊢
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 := by
    rw [ProofLib.memRegion_split' (b := (s0.sp - 4240#64) + 1856#64) (n := 504) (k := 376)
      (b' := (s0.sp - 4240#64) + 2360#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hout := err4_entails_resultV1RecvAt_macVerifyFailed A (F := F) (s.readReg64 .x19) w1 w2 w3
  have hfold_all :
      (((s.readReg64 .x19) ↦₆₄ noneCap) ∗ (((s.readReg64 .x19) + 8#64) ↦₆₄ w1) ∗
       errMacVerifyTag8Split.heap (unpack64 w1) ∗
       (((s.readReg64 .x19) + 16#64) ↦₆₄ w2) ∗ (((s.readReg64 .x19) + 24#64) ↦₆₄ w3) ∗
       memRegion ((s.readReg64 .x19) + 32#64) 928) ∗
      (sendEkSpillsAt (s0.sp - 4240#64) sp_err ∗
       memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
       (((s0.sp - 4240#64 + 976#64) ↦₆₄ none2Cap) ∗
        ((s0.sp - 4240#64 + 984#64) ↦₆₄ w1) ∗
        ((s0.sp - 4240#64 + 992#64) ↦₆₄ w2) ∗
        ((s0.sp - 4240#64 + 1000#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 4240#64) + 1008#64) 472 ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
       (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
       sendEkUnusedAt (s0.sp - 4240#64)) ⊢
        resultV1RecvAt A (F := F) (s.readReg64 .x19) (.error (.err .macVerifyFailed)) ∗
        memRegion (s0.sp - 4240#64) 4144 :=
    sepConj_mono hout
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono h880_976 (sepConj_mono_left h880_1856))))
        (sendEkFrame_entails_memRegion_4144 (s0.sp - 4240#64) sp_err))
  refine SepWP.fold
    (F := P_rest ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      statesRecvSavedCells s0)
    hfold_all ?_ ?_
  · dsimp only [sendEkSpillsAt, sp_err, none2Cap, noneCap, Reg.x19]
    simp only [BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (resultV1RecvAt A (F := F) (s.readReg64 .x19) (.error (.err .macVerifyFailed)) ∗
          memRegion (s0.sp - 4240#64) 4144) ∗
        (P_rest ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          statesRecvSavedCells s0) =
        (P_rest ∗ resultV1RecvAt A (F := F) (s.readReg64 .x19) (.error (.err .macVerifyFailed))) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hep _ (P_rest ∗ resultV1RecvAt A (F := F) (s.readReg64 .x19) (.error (.err .macVerifyFailed)))
        rfl hrun hsp hsp_align htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

/-! ## 2. Post-Call `.ok (.stillReceiving outSt)` Path (`0x56574..0x5658c -> 0x58598..0x5883c -> 0x59e88..0x59ff0`) -/

set_option maxHeartbeats 1200000 in
/-- Relocatable post-call block `0x56574..0x5658c -> 0x58598..0x5883c -> 0x59e88..0x59ff0`
    (`+4384 -> s0.x30`, Block `332`) when `recv_ct2_chunk` returns `.ok (.stillReceiving outSt)`. -/
theorem ekSentCt1Received_post_call_still_56574_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 4384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        ekSentCt1ReceivedRecvChunkResultAt A (F := F) ((s0.sp - 4240#64) + 976#64)
          (.ok (.stillReceiving outSt)) ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received outSt }) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwb := @states_recv_writeback_59e88_sat _ ext hmemcpy_sat (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine sepWP_seq_cut ((blkPl_332).base + 18996#64) ?_
  refine SepWP.fold (stillReceiving_result_976_extract A ((s0.sp - 4240#64) + 976#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out
  refine SepWP.pure_elim fun ⟨hcap, _⟩ => ?_
  refine SepWP.fold (sendEkUnusedAt_split_ab0_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i qab0 qac0
  have hcond1 := cap_add_two_bne_zero_true hcap
  have hcond2 := Recv.cap_add_two_beq_zero_false hcap
  have hcond3 := cap_add_one_beq_zero_false_recv hcap
  have hcond4 := cap_add_one_bne_zero_true_recv hcap
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  subst hsp0
  refine SepWP.done rfl hrun ?_
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, w_out.b3.w2, w_out.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6,
             sp.b0.w7, w_out.b3.w5, w_out.b3.w4⟩
      b1 := ⟨w_out.b5.w7, sp.b1.w1, sp.b1.w2, w_out.b3.w6, sp.b1.w4, sp.b1.w5, w_out.b0.w1,
             w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨sp.b2.w0, sp.b2.w1, w_out.b4.w9, sp.b2.w3, w_out.b4.w5, w_out.b0.w1, w_out.b4.w8,
             6#64, noneCap, sp.b2.w9⟩
      b3 := ⟨w_out.b5.w8, w_out.w62, w_out.b1.w8, w_out.b2.w1, w_out.b2.w7, w_out.b0.w7,
             w_out.b1.w3, w_out.b2.w5, w_out.b3.w0, w_out.b2.w8⟩
      b4 := ⟨w_out.b2.w6, w_out.b1.w2, w_out.b1.w9, w_out.b1.w0, w_out.b2.w2, w_out.b0.w5,
             w_out.b0.w4, w_out.b1.w1, w_out.b2.w0, w_out.b2.w3⟩
      b5 := ⟨w_out.b0.w9, w_out.b4.w4, w_out.b1.w4, w_out.b0.w8, w_out.b1.w7, w_out.b5.w0,
             w_out.b0.w3, w_out.b2.w4, w_out.b4.w6, w_out.b5.w4⟩
      w60 := w_out.b5.w6
      w61 := w_out.b0.w2
      w62 := w_out.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := w_out.q60 }
  have h880_1856 :
      memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ⊢
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 := by
    rw [ProofLib.memRegion_split' (b := (s0.sp - 4240#64) + 1856#64) (n := 504) (k := 376)
      (b' := (s0.sp - 4240#64) + 2360#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hfold_unused := sendEkUnusedAt_rejoin_ab0_ac0 (s0.sp - 4240#64) w_out.q60 qac0
  have hfold_sp1 :
      (words63At ((s0.sp - 4240#64) + 976#64) w_out ∗
       memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
      (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
       memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
      (((s0.sp - 4240#64 + 2736#64) ↦₁₂₈ w_out.q60) ∗
       ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ qac0) ∗
       memRegion (s0.sp - 4240#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono
      (words63At_376_entails_memRegion_880
        ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) w_out (by bv_omega))
      (sepConj_mono h880_1856 (sepConj_mono_left hfold_unused))
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      statesRecvSavedCells s0)
    hfold_sp1 ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1, noneCap]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out))) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗ relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)))
        rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ekSentCt1Received_entails_resultV1RecvAt A (F := F) outA outSt w_out
      w_out.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    rcases w_out with ⟨⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
      ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
      ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩, _, _⟩
    dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm]
    ac_rfl

/-! ## 3. Post-Call `.ok (.done (nhr, sec))` Path (`0x56574..0x5658c -> 0x58598..0x586f4 -> 0x59950..0x599c8 -> 0x59a7c..0x59b34 -> 0x59e88..0x59ff0`) -/

set_option maxHeartbeats 1600000 in
/-- Relocatable post-call block `0x56574..0x5658c -> 0x58598..0x586f4 -> 0x59950..0x599c8 -> 0x59a7c..0x59b34 -> 0x59e88..0x59ff0`
    (`+4384 -> s0.x30`, Block `332`) when `recv_ct2_chunk` returns `.ok (.done (nhr, sec))`. -/
theorem ekSentCt1Received_post_call_done_56574_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA : BitVec 64)
    (nhr : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (sec : EpochSecret)
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 4384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        ekSentCt1ReceivedRecvChunkResultAt A (F := F) ((s0.sp - 4240#64) + 976#64)
          (.ok (.done (nhr, sec))) ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := some sec, state := .noHeaderReceived nhr }) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwb := @states_recv_writeback_59e88_sat _ ext hmemcpy_sat (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine sepWP_seq_cut ((blkPl_332).base + 18996#64) ?_
  refine SepWP.fold (done_result_976_extract A ((s0.sp - 4240#64) + 976#64) nhr sec)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g p v_sec w_pad
  refine SepWP.fold (sendEkUnusedAt_split_ab0_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i qab0 qac0
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let w_out := mkWords63_done g nhr.uc.epoch p v_sec sec.epoch w_pad
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At, mkWords63_done, noneCap, lsLogFilterAddr, lsρ]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  subst hsp0
  refine SepWP.done rfl hrun ?_
  let sp1 : SendEkSpills :=
    { b0 := ⟨p.b4.w5, p.b2.w8, w_out.b3.w2, w_out.b3.w0, sp.b0.w4, p.b3.w4, sp.b0.w6,
             p.b3.w1, w_out.b3.w5, w_out.b3.w4⟩
      b1 := ⟨w_out.b5.w7, p.b4.w8, p.b3.w2, w_out.b3.w7, p.b4.w6, p.b3.w0, w_out.b0.w1,
             w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨p.b4.w0, p.b4.w4, w_out.b5.w0, p.b3.w6, w_out.b4.w6, w_out.b0.w2, w_out.b4.w9,
             7#64, w_out.b5.w8, w_out.b4.w3⟩
      b3 := ⟨sp.b3.w0, sp.b3.w1, w_out.b1.w9, w_out.b2.w2, w_out.b2.w8, w_out.b0.w8,
             w_out.b1.w4, w_out.b2.w6, w_out.b3.w1, w_out.b2.w9⟩
      b4 := ⟨w_out.b2.w7, w_out.b1.w3, w_out.b2.w0, w_out.b1.w1, w_out.b2.w3, w_out.b0.w6,
             w_out.b0.w5, w_out.b1.w2, w_out.b2.w1, w_out.b2.w4⟩
      b5 := ⟨w_out.b1.w0, w_out.b4.w5, w_out.b1.w5, w_out.b0.w9, w_out.b1.w8, w_out.b5.w1,
             w_out.b0.w4, w_out.b2.w5, w_out.b4.w7, w_out.b5.w5⟩
      w60 := w_out.b5.w7
      w61 := w_out.b0.w3
      w62 := w_out.b0.w7
      q200 := w_out.q60
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := sp.q3c0 }
  have h880_1856 :
      memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ⊢
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 := by
    rw [ProofLib.memRegion_split' (b := (s0.sp - 4240#64) + 1856#64) (n := 504) (k := 376)
      (b' := (s0.sp - 4240#64) + 2360#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hfold_unused := sendEkUnusedAt_rejoin_ab0_ac0 (s0.sp - 4240#64) w_out.q60 w_out.q60
  have hfold_sp1 :
      (words63At ((s0.sp - 4240#64) + 976#64) w_out ∗
       memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
      (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
       memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
      (((s0.sp - 4240#64 + 2736#64) ↦₁₂₈ w_out.q60) ∗
       ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w_out.q60) ∗
       memRegion (s0.sp - 4240#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono
      (words63At_376_entails_memRegion_880
        ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) w_out (by bv_omega))
      (sepConj_mono h880_1856 (sepConj_mono_left hfold_unused))
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
        (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
      relocatedHeap (fun dst => vecU8 A dst sec.secret)
        (wordsBytes (vecWordsList v_sec)) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      statesRecvSavedCells s0)
    hfold_sp1 ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1, w_out, mkWords63_done, noneCap, lsLogFilterAddr, lsρ]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
            (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
          relocatedHeap (fun dst => vecU8 A dst sec.secret)
            (wordsBytes (vecWordsList v_sec)) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
            (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
          relocatedHeap (fun dst => vecU8 A dst sec.secret)
            (wordsBytes (vecWordsList v_sec))) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
            (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
          relocatedHeap (fun dst => vecU8 A dst sec.secret)
            (wordsBytes (vecWordsList v_sec)))
        rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_noHeaderReceived_some_entails_resultV1RecvAt A (F := F) outA nhr sec g p v_sec
      p.b2.w5 sp.b3.w0 w_out.b5.w9 sp.q3c0 sp.b3.w1
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, sp1, w_out, mkWords63_done, mkWords63_nhr_tail,
      Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm]
    ac_rfl

/-! ## 4. `eq_ct2` Arm and Complete `.ekSentCt1Received` Arm -/

set_option maxHeartbeats 1600000 in
/-- Relocatable `.ekSentCt1Received` arm when `msg.epoch = st.uc.epoch` and `msg.payload = .ct2 chunk`
    (`+228 -> s0.x30`, `0x55538..0x5565c -> 0x56544..0x56574 -> 0x56574..0x59ff0`, Block `332`). -/
theorem ekSentCt1Received_arm_eq_ct2_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 350)
      (withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F A)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (P_rest R : SepProp)
    {Q_post Q_panic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : statesRecvPreInv (.ekSentCt1Received st))
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ct2 chunk)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0)
    (hdone : ∀ (sf : State) (Pf : SepProp), sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
      (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (States.recv K (.ekSentCt1Received st) msg) ∗
        memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace → Q_post sf Pf)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜((st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) → Q_panic sf P_f) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 350) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sm Pm =>
        SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sm Pm Q_post Q_panic) := by
  have hcond_eq := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (sessionMemcpySpec 4096) := spqr_hook_ok_of_mem hmemcpy_sat
  have hpost_err := @ekSentCt1Received_post_call_err_56574_cut_placed _ A F ext s0
  have hpost_still := @ekSentCt1Received_post_call_still_56574_placed _ A F ext hmemcpy_sat s0
  have hpost_done := @ekSentCt1Received_post_call_done_56574_placed _ A F ext hmemcpy_sat s0
  refine sepWP_seq_lscro hcro (mid := lsmpl.base 350) ?_
  rw [lsmpl_base_332_eq] at hpc hpost_err hpost_still hpost_done
  dsimp only [lsProg_332, lsρ, memcpyName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy hcall hpost_err hpost_still hpost_done hdone ⊢
  rcases hinv with ⟨hsort, hroot⟩
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw12, heq, hpay, messagePayloadAt_ct2 msgA chunk]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 120
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7, sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9, w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, sp.b2.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7, sp.b2.w8, sp.b2.w9⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5, sp.b3.w8, w.b2.w8⟩
      b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, sp.b4.w5, w.b0.w4, w.b1.w1, w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, sp.b5.w5, w.b0.w3, w.b2.w4, w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := sp.q3c0 }
  have hfold_pre_memcpy :
      (words63At (selfA + 8#64) w ∗
       relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w))) ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        chunkedEkSentCt1ReceivedAt A (selfA + 8#64) st ∗
        (memRegion ((s0.sp - 4240#64) + 976#64) 504 ∗
         memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
        (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
         memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono (recompose63 (selfA + 8#64) w)
      (sepConj_mono
        (Entails.of_eq (memRegion_880_split_504_376_ct2
          ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) (by bv_omega)))
        (sepConj_mono_left
          (Entails.of_eq (memRegion_880_split_504_376_ct2
            ((s0.sp - 4240#64) + 1856#64) ((s0.sp - 4240#64) + 2360#64) (by bv_omega)))))
  refine SepWP.fold
    (F := P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 6#64) ∗ memRegion (selfA + 512#64) 416 ∗
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
        chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
    hfold_pre_memcpy ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw12, heq]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
    dsimp only [allocHookStack]
    refine call_memcpy_relocate_cs_sat (ret_pc := (blkPl_332).base + 4364#64)
      hmemcpy (Recv.Relocatable.of_chunkedEkSentCt1ReceivedAt A st)
      ((s0.sp - 4240#64) + 1856#64) (selfA + 8#64)
      rfl hrun hsp hfsp_align rfl htr
      (by simp only [Reg.x0, arm64_norm, hsp])
      (by simp only [Reg.x1, arm64_norm, hx1])
      (by simp only [Reg.x2, arm64_norm]) (by sep_focus) ?_
    intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
    have hx19_1 : sf1.readReg64 .x19 = outA :=
      hcs1.1.trans (by simp only [Reg.x19, arm64_norm, hx19])
    have hx24_1 : sf1.readReg64 .x24 = msgA :=
      hcs1.2.2.2.2.2.1.trans (by simp only [Reg.x24, arm64_norm, hx24])
    have hx25_1 : sf1.readReg64 .x25 = st.uc.epoch :=
      hcs1.2.2.2.2.2.2.1.trans (by simp only [Reg.x25, arm64_norm])
    have hfold_callee :
        memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗ stackAt (s0.sp - 4240#64) 4096 ⊢
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX :=
      Entails.of_eq (stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)).symm
    refine SepWP.focus_weaken hfold_callee (by sep_focus) ?_
    have hfold_self :
        chunkedEkSentCt1ReceivedAt A ((s0.sp - 4240#64) + 1856#64) st ∗
        ((selfA ↦₆₄ 6#64) ∗ memRegion (selfA + 8#64) 504 ∗ memRegion (selfA + 512#64) 416) ⊢
          (ekSentCt1ReceivedUcAt A ((s0.sp - 4240#64) + 1856#64) st.uc ∗
           polyDecoderAt A ((s0.sp - 4240#64) + 1960#64) st.receiving_ct2) ∗
          memRegion selfA chunkedStatesSize := by
      unfold chunkedEkSentCt1ReceivedAt unchunkedEkSentCt1ReceivedAt
      rw [show ((s0.sp - 4240#64) + 1856#64) + 104#64 = (s0.sp - 4240#64) + 1960#64 by bv_omega]
      exact sepConj_mono_right (self_504_416_entails_memRegion_928 selfA 6#64)
    refine SepWP.focus_weaken hfold_self (by sep_focus) ?_
    generalize hsp0 : s0.sp = sp0 at hsp1 hfsp_align ⊢
    wp_steps 10
    subst hsp0
    refine SepWP.done rfl hrun1 (fun hcl_m => ?_)
    refine call_ekSentCt1ReceivedRecvCt2Chunk_placed hcall
      ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1856#64) (msgA + 10#64)
      st chunk hsort hroot
      (s0 := s0) (sp_call := s0.sp - 4240#64) (ret_pc := (blkPl_332).base + 4384#64) (R := R)
      (Frame :=
        P_rest ∗ memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
          memRegion (msgA + 44#64) 4) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion outA v1RecvSize ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        statesRecvSavedCells s0)
      hcl_m rfl hrun1 hsp1 hfsp_align (by simp only [Reg.lr, arm64_norm]) htr1
      (by simp only [Reg.x0, arm64_norm, hsp1]) (by simp only [Reg.x1, arm64_norm, hsp1])
      (by simp only [Reg.x2, arm64_norm, hx25_1]) (by simp only [Reg.x3, arm64_norm, hx24_1])
      (by
        dsimp only [chunkedEkSentCt1ReceivedSize, ekSentCt1ReceivedAt,
          statesRecvCalleeStackX, BitVec.ofNat_eq_ofNat]
        simp only [arm64_norm]; ac_rfl)
      hpanic ?_
    intro sf2 hpc2 hrun2 hsp2 hcs2 htr2
    have hmsg_eq :
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
         chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) =
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) := by
      rw [hpay, messagePayloadAt_ct2 msgA chunk]
    have hx19_2 : sf2.readReg64 .x19 = outA :=
      hcs2.1.trans (by simp only [Reg.x19, arm64_norm, hx19_1])
    cases hres : st.recv_ct2_chunk K st.uc.epoch chunk with
    | error err =>
      cases err with
      | panic p =>
        dsimp only [ekSentCt1ReceivedRecvChunkResultAt]; rw [sepConj_assoc]
        exact SepWP.pure_elim (fun hfalse => False.elim hfalse)
      | err e =>
        have he := recv_ct2_chunk_err_eq_macVerifyFailed st st.uc.epoch chunk e hres
        subst he
        have hmodel := states_recv_ekSentCt1Received_eq_ct2_err K st msg chunk .macVerifyFailed heq hpay hres
        refine SepWP.weaken_pre (Entails.of_eq ?_)
          (SepWP.mono
            (hpost_err sf2 outA sp1
              (P_rest ∗ memRegion selfA chunkedStatesSize ∗
               ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
               (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
              hpc2 hrun2 hsp2 hsp_align hx19_2 htr2)
            (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              hdone sf Pf hpc_f hrun_f
                ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)),
                 hsp_sf, hcs_sf, htr_sf⟩))
        rw [← hmsg_eq]
        dsimp only [chunkedEkSentCt1ReceivedSize, statesRecvCalleeStackX]
        simp only [arm64_norm]; ac_rfl
    | ok outRes =>
      cases outRes with
      | stillReceiving outSt =>
        have hmodel := states_recv_ekSentCt1Received_eq_ct2_still K st msg chunk outSt heq hpay hres
        refine SepWP.weaken_pre (Entails.of_eq ?_)
          (SepWP.mono
            (hpost_still sf2 outA outSt sp1
              (P_rest ∗ memRegion selfA chunkedStatesSize ∗
               ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
               (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
              hpc2 hrun2 hsp2 hsp_align hx19_2 htr2)
            (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              hdone sf Pf hpc_f hrun_f
                ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)),
                 hsp_sf, hcs_sf, htr_sf⟩))
        rw [← hmsg_eq]
        dsimp only [chunkedEkSentCt1ReceivedSize, statesRecvCalleeStackX]
        simp only [arm64_norm]; ac_rfl
      | done pair =>
        rcases pair with ⟨nhr, sec⟩
        have hmodel := states_recv_ekSentCt1Received_eq_ct2_done K st msg chunk nhr sec heq hpay hres
        refine SepWP.weaken_pre (Entails.of_eq ?_)
          (SepWP.mono
            (hpost_done sf2 outA nhr sec sp1
              (P_rest ∗ memRegion selfA chunkedStatesSize ∗
               ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
               tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
              hpc2 hrun2 hsp2 hsp_align hx19_2 htr2)
            (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              hdone sf Pf hpc_f hrun_f
                ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)),
                 hsp_sf, hcs_sf, htr_sf⟩))
        rw [← hmsg_eq]
        dsimp only [chunkedEkSentCt1ReceivedSize, statesRecvCalleeStackX]
        simp only [arm64_norm]; ac_rfl

/-- Complete relocatable `.ekSentCt1Received` arm of `<States>::recv` (`+228 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_ekSentCt1Received_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 350)
      (withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F A)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : statesRecvPreInv (.ekSentCt1Received st))
    (hpc : s.pc = lsmpl.base 332 + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantPlacedSpec A F K (.ekSentCt1Received st) msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantPlacedSpec A F K (.ekSentCt1Received st) msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)) := by
  have hpre_comm :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
      statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ekSentCt1Received st) ∗ messageAt spqrPolyApi msgA msg ∗
        A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 := by ac_rfl
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit_placed s0 s outA selfA msgA (.ekSentCt1Received st) msg _ R ?_
    rw [states_recv_ekSentCt1Received_gt K st msg hgt, hpre_comm]
    refine SepWP.mono
      (ekSentCt1Received_arm_gt_placed hdealloc s0 s outA selfA msgA st msg statesRecvRoPlacedAt
        hgt hcro.1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit_placed s0 s outA selfA msgA (.ekSentCt1Received st) msg _ R ?_
      rw [states_recv_ekSentCt1Received_lt K st msg hlt, hpre_comm]
      refine SepWP.mono
        (ekSentCt1Received_arm_lt_placed hmemcpy_sat s0 s outA selfA msgA st msg statesRecvRoPlacedAt
          hlt hcro.1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch := by
        have h1 : ¬ (st.uc.epoch < msg.epoch) := hgt
        have h2 : ¬ (msg.epoch < st.uc.epoch) := hlt
        exact BitVec.le_antisymm (BitVec.not_lt.mp h1) (BitVec.not_lt.mp h2)
      cases hpay : msg.payload with
      | ct2 chunk =>
        dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]
        rw [show memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗
              (statesRecvJumpTablePlacedAt ∗
                ((lsLogFilterAddr ↦₆₄ 0#64) ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) ∗
                tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗
              A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
            (statesRecvJumpTablePlacedAt ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) ∗
              memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 by ac_rfl]
        refine SepWPp.of_sepWP
          (ekSentCt1Received_arm_eq_ct2_placed (K := K) hcall hmemcpy_sat s0 s outA selfA msgA st msg chunk
            (statesRecvJumpTablePlacedAt ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) R
            hcro hinv heq hpay hpc hrun hsp hsp_align hx1 hx19 hx24 htr
            (fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ?_)
            (fun sf Pf hpan hmem_f => ?_))
        · refine ⟨fun hmem_f => ?_, hspf, hcs⟩
          dsimp only [statesRecvVariantPlacedSpec]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨htrf, Satisfies.mono (sepConj_mono_left ?_) hmem_f⟩
          refine Entails.trans hPf (Entails.of_eq ?_)
          dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]; ac_rfl
        · have hpan' := hpan hmem_f
          dsimp only [statesRecvVariantPlacedSpec, statesRecvOnPanic]
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpan' ⊢
          refine ⟨⟨?_, hpan'.1.2⟩, hpan'.2⟩
          cases hpan'.1.1 with
          | inl hp => exact Or.inl (states_recv_ekSentCt1Received_eq_ct2_panic K st msg chunk heq hpay hp)
          | inr haf => exact Or.inr haf
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1 _ | ct1Ack _ =>
        have hct2 : ∀ c, msg.payload ≠ .ct2 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit_placed s0 s outA selfA msgA (.ekSentCt1Received st) msg _ R ?_
        rw [states_recv_ekSentCt1Received_eq_other K st msg heq hct2, hpre_comm]
        refine SepWP.mono
          (ekSentCt1Received_arm_eq_other_placed hmemcpy_sat s0 s outA selfA msgA st msg statesRecvRoPlacedAt
            heq hct2 hcro.1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

/-- Top-level relocatable `subroutine_ok` theorem for `<States>::recv` (Block `332`)
    on the `.ekSentCt1Received` variant (`tag = 6#64`). -/
theorem states_recv_ekSentCt1Received_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : StatesRecvPlacedContracts A F K ext)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl (statesRecvVariantPlacedSpec A F K (.ekSentCt1Received st) msg)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcro0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [statesRecvVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_recv_prologue_placed (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean_lscro hcro0 hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩ hcro1
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch_placed (ext := ext) s1 (s0.sp - 4240#64) selfA 6#64
    (chunkedEkSentCt1ReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_clean_lscro hcro1 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩ hcro2
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have hpre2 :
      (selfA ↦₆₄ 6#64) ∗ statesRecvRoPlacedAt ∗
      (chunkedEkSentCt1ReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0) ⊢
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 := by
    dsimp only [chunkedStatesAt]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre2 ?_
  exact states_recv_arm_ekSentCt1Received_placed (K := K) hC.hdealloc_sat hC.ekSentCt1ReceivedRecvCt2Chunk_ok
    hC.hmemcpy_sat s0 s2 outA selfA msgA st msg R hcro2 hinv hpc2 hrun2 hsp2 hsp0_align
    hx1_2 hx19_2 hx24_2 (htr2.trans htr1)

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  ekSentCt1Received_post_call_err_56574_cut_placed
  ekSentCt1Received_post_call_still_56574_placed
  ekSentCt1Received_post_call_done_56574_placed
  ekSentCt1Received_arm_eq_ct2_placed
  states_recv_arm_ekSentCt1Received_placed
  states_recv_ekSentCt1Received_placed_ok_ext
)

end CryptoVerification.SpqrV1.States.Recv
