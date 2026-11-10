/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Acknowledged` Arm, Part 3 (Relocatable)

Relocatable `[LibsignalPlacement]` `.done` path, Branch C composition, and top-level
`.ct1Acknowledged` contract `states_recv_ct1Acknowledged_placed_ok_ext`.
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
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  Recv.sp_sub_96_add_16 Recv.sp_sub_96_add_32 Recv.sp_sub_96_add_48 Recv.sp_sub_96_add_64 Recv.sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

/-! ## 1. `.done` Path (`+4468 -> +13292 -> +18148 -> +19360 -> +4924 -> s0.x30`) -/

private theorem sepWPp_seq_clean_lscro [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post onPanic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog target sm P_mid post onPanic) :
    SepWPp prog target s P post onPanic :=
  SepWPp.of_sepWP (sepWP_seq_lscro hcro (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcro' =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm hpc hrun hQ hcro'))))

set_option maxHeartbeats 2400000 in
theorem ct1Ack_step_4468_done_4924_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp d58 d59 dw62 dw65 we50 : BitVec 64)
    (dq60 dq63 qe40 qe60 : BitVec 128)
    (w : Words57) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 4468#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = fsp + 1856#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 4924#64) s
      (((fsp + 1856#64) ↦₆₄ noneCap) ∗ words57At (fsp + 1864#64) w ∗
       ((fsp + 2320#64) ↦₆₄ d58) ∗ ((fsp + 2328#64) ↦₆₄ d59) ∗
       ((fsp + 2336#64) ↦₁₂₈ dq60) ∗ ((fsp + 2352#64) ↦₆₄ dw62) ∗
       ((fsp + 2360#64) ↦₁₂₈ dq63) ∗ ((fsp + 2376#64) ↦₆₄ dw65) ∗
       sendEkSpillsAt fsp sp ∗
       ((fsp + 3648#64) ↦₁₂₈ qe40) ∗ ((fsp + 3664#64) ↦₆₄ we50) ∗ ((fsp + 3680#64) ↦₁₂₈ qe60) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1856#64) ↦₆₄ noneCap) ∗ words57At (fsp + 1864#64) w ∗
          ((fsp + 2320#64) ↦₆₄ d58) ∗ ((fsp + 2328#64) ↦₆₄ d59) ∗
          ((fsp + 2336#64) ↦₁₂₈ dq60) ∗ ((fsp + 2352#64) ↦₆₄ dw62) ∗
          ((fsp + 2360#64) ↦₁₂₈ dq63) ∗ ((fsp + 2376#64) ↦₆₄ dw65) ∗
          sendEkSpillsAt fsp (ct1AckSpillsDone4924 sp w d58 d59 dw62) ∗
          ((fsp + 3648#64) ↦₁₂₈ dq63) ∗ ((fsp + 3664#64) ↦₆₄ dw65) ∗ ((fsp + 3680#64) ↦₁₂₈ dq60) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = w.w55 ∧ sm.readReg64 .x1 = w.b0.w0 ∧
        sm.readReg64 .x2 = w.b1.w2 ∧ sm.readReg64 .x3 = w.b2.w9 ∧
        sm.readReg64 .x4 = w.b4.w9 ∧ sm.readReg64 .x5 = w.b4.w8 ∧
        sm.readReg64 .x6 = w.w50 ∧ sm.readReg64 .x7 = w.b1.w9 ∧
        sm.readReg64 .x10 = w.b1.w6 ∧ sm.readReg64 .x11 = w.w54 ∧
        sm.readReg64 .x12 = w.b4.w0 ∧ sm.readReg64 .x13 = w.w51 ∧
        sm.readReg64 .x15 = w.b2.w7 ∧ sm.readReg64 .x16 = w.b4.w7 ∧
        sm.readReg64 .x17 = w.b4.w5 ∧ sm.readReg64 .x18 = w.w53 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x22 = w.w52 ∧
        sm.readReg64 .x24 = w.b3.w1 ∧ sm.readReg64 .x25 = w.b3.w9 ∧
        sm.readReg64 .x26 = w.b0.w5 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = w.b3.w8 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  states_recv_fetches_range (blkPl_332).base (Rust.withPanics ext) 4468 28
  states_recv_fetches_range (blkPl_332).base (Rust.withPanics ext) 13292 372
  states_recv_fetches_range (blkPl_332).base (Rust.withPanics ext) 18148 4
  states_recv_fetches_range (blkPl_332).base (Rust.withPanics ext) 18160 64
  states_recv_fetches_range (blkPl_332).base (Rust.withPanics ext) 19360 156
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [words57At, sendEkSpillsAt, ct1AckSpillsDone4924, words10At, pointsTo128, noneCap,
    bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps 256
  simp only [words57At, sendEkSpillsAt, ct1AckSpillsDone4924, words10At, pointsTo128, noneCap,
    bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

theorem ct1Ack_done_4468_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s1 : State) (outA selfA : BitVec 64)
    (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = lsmpl.base 332 + 4468#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (hx20 : s1.readReg64 .x20 = (s0.sp - 4240#64) + 1856#64)
    (htr : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      ((P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        ct1AcknowledgedRecvEkChunkResAt A (F := F) ((s0.sp - 4240#64) + 1856#64) (.ok (.done outSt)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 2384#64) 352 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ (P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct2Sampled outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine SepWP.fold (ct1Ack_done_1856_split (A := A) (F := F) fsp outSt) (by sep_focus) ?_
  wp_pull_exists; rename_i w d58 d59 dq60 dw62 dq63 dw65
  refine SepWP.fold (sendEkUnusedAt_split_e40 fsp) (by sep_focus) ?_
  wp_pull_exists; rename_i qe40 we50 qe60
  set sp1 := ct1AckSpillsDone4924 sp w d58 d59 dw62
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := lsmpl.base 332 + 4924#64)
    (P_mid := (P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x0 = w.w55 ∧ s2.readReg64 .x1 = w.b0.w0 ∧
      s2.readReg64 .x2 = w.b1.w2 ∧ s2.readReg64 .x3 = w.b2.w9 ∧
      s2.readReg64 .x4 = w.b4.w9 ∧ s2.readReg64 .x5 = w.b4.w8 ∧
      s2.readReg64 .x6 = w.w50 ∧ s2.readReg64 .x7 = w.b1.w9 ∧
      s2.readReg64 .x10 = w.b1.w6 ∧ s2.readReg64 .x11 = w.w54 ∧
      s2.readReg64 .x12 = w.b4.w0 ∧ s2.readReg64 .x13 = w.w51 ∧
      s2.readReg64 .x15 = w.b2.w7 ∧ s2.readReg64 .x16 = w.b4.w7 ∧
      s2.readReg64 .x17 = w.b4.w5 ∧ s2.readReg64 .x18 = w.w53 ∧
      s2.readReg64 .x19 = outA ∧ s2.readReg64 .x22 = w.w52 ∧
      s2.readReg64 .x24 = w.b3.w1 ∧ s2.readReg64 .x25 = w.b3.w9 ∧
      s2.readReg64 .x26 = w.b0.w5 ∧ s2.readReg64 .x30 = w.b3.w8 ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · have hstep1 := ct1Ack_step_4468_done_4924_placed (ext := ext) s1 fsp d58 d59 dw62 dw65 we50
      dq60 dq63 qe40 qe60 w sp
      (P_rest ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
       memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
       ct1AckUnusedRestAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp hx20
    refine SepWP.weaken_pre (Entails.of_eq ?_) (SepWP.mono hstep1 ?_)
    · dsimp only [unchunkedSendCt2PlacedRoAt]; ac_rfl
    · intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
        h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
        h2_24, h2_25, h2_26, _, h2_30, htr2⟩
      refine ⟨Entails.trans hPm ?_, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
        h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19.trans hx19, h2_22,
        h2_24, h2_25, h2_26, h2_30, htr2.trans htr⟩
      have h880 := ct1Ack_done_1856_rejoin_880 fsp d58 d59 dw62 dw65 dq60 dq63 w
      have hunused := ct1AckUnusedRest_entails_sendEkUnusedAt fsp dq63 dw65 dq60
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1856#64) ↦₆₄ noneCap) ∗ words57At (fsp + 1864#64) w ∗
         ((fsp + 2320#64) ↦₆₄ d58) ∗ ((fsp + 2328#64) ↦₆₄ d59) ∗
         ((fsp + 2336#64) ↦₁₂₈ dq60) ∗ ((fsp + 2352#64) ↦₆₄ dw62) ∗
         ((fsp + 2360#64) ↦₁₂₈ dq63) ∗ ((fsp + 2376#64) ↦₆₄ dw65) ∗ memRegion (fsp + 2384#64) 352) ∗
        (((fsp + 3648#64) ↦₁₂₈ dq63) ∗ ((fsp + 3664#64) ↦₆₄ dw65) ∗
         ((fsp + 3680#64) ↦₁₂₈ dq60) ∗ ct1AckUnusedRestAt fsp) ∗
        ((P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
         memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗ statesRecvSavedCells s0) by
          dsimp only [unchunkedSendCt2PlacedRoAt]; ac_rfl)) ?_
      exact Entails.trans (sepConj_mono h880 (sepConj_mono_left hunused))
        (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 ⟨hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
      h2_24, h2_25, h2_26, h2_30, htr2⟩
    set sp2 := ct1AckSpills4924 s2 sp1
    refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := lsmpl.base 332 + 18996#64)
      (P_mid := ((P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w))) ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp2 ∗
        memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
        memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = outA ∧
        writebackWords63 s3 sp2 =
          { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4,
            b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, w.b1.w2, d58, w.b3.w8⟩,
            q60 := sp.q3c0, w62 := dw62 } ∧ TraceCalleeSaved s3 s0)
      ?_ ?_
    · have hstep2 := ct1Ack_step_4924_18996_placed (ext := ext) s2 fsp sp1
        ((P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
        hfsp_align hpc2 hrun2 hsp2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep2 ?_)
      intro s3 Pm _ _ ⟨hPm, hsp3, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7,
        h3_8, h3_9, h3_10, h3_11, h3_12, h3_13, h3_14, h3_15, h3_16, h3_17, h3_19,
        h3_20, h3_21, h3_22, h3_23, h3_24, h3_25, h3_26, h3_27, h3_28, _, h3_30, htr3⟩
      have hwb := writebackWords63_ct1Ack_done s2 s3 sp w d58 d59 dw62
        h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_10 h2_11 h2_12 h2_13
        h2_15 h2_16 h2_17 h2_18 h2_22 h2_24 h2_25 h2_26 h2_30
        h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 h3_8 h3_9 h3_10 h3_11 h3_12
        h3_13 h3_14 h3_15 h3_16 h3_17 h3_20 h3_21 h3_22 h3_23 h3_24 h3_25
        h3_26 h3_27 h3_28 h3_30
      refine ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hsp3, h3_19.trans h2_19, hwb, htr3.trans htr2⟩
    · intro s3 hpc3 hrun3 ⟨hsp3, h3_19, hwb, htr3⟩
      have hwrite := states_recv_writeback_59e88_sat_placed hmemcpy_sat (Relocatable.of_memRegion 376)
        s0 s3 outA sp2
        ((P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)))
        hpc3 hrun3 hsp3 hsp0_align h3_19 htr3
      refine SepWP.mono hwrite ?_
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      have htag : sp2.b2.w7 = 12#64 := rfl
      have hnone : sp2.b2.w8 = noneCap := rfl
      rw [htag, hnone, hwb]
      have hout := ek_ack_out_entails_resultV1RecvAt A (F := F) outA outSt w
        w.b1.w2 d58 w.b3.w8 sp.q3c0 dw62 (s3.readReg64 .x20) sp2.q200
      refine Entails.trans (Entails.of_eq (show _ =
        (P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ ((outA ↦₆₄ 12#64) ∗
         words63At (outA + 8#64)
           { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4,
             b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, w.b1.w2, d58, w.b3.w8⟩,
             q60 := sp.q3c0, w62 := dw62 } ∗
         memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
         ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s3.readReg64 .x20) ∗
         ((outA + 944#64) ↦₁₂₈ sp2.q200) ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w))) ∗
        memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_right (sepConj_mono_left hout)) (Entails.of_eq (by ac_rfl))

/-! ## 2. Branch C Composition and Top-Level `.ct1Acknowledged` Theorem -/

theorem ct1Ack_step_608_632_words66_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA msg_ep : BitVec 64) (w : Words66) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 632#64) s
      (words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg_ep) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg_ep) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x9 = w.b1.w5 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep w.b1.w5)) ∧
        sm.pstate.z = (ekCmpW8 (subsPState64 msg_ep w.b1.w5) == 0#32) ∧
        TraceCalleeSaved sm s) := by
  have h1056 : (fsp + 976#64) + 80#64 = fsp + 1056#64 := by bv_omega
  have hstep := ct1Ack_step_608_632_placed (ext := ext) s fsp out selfA msgA msg_ep w.b1
    (words10At (fsp + 976#64) w.b0 ∗
     words10At ((fsp + 976#64) + 160#64) w.b2 ∗
     words10At ((fsp + 976#64) + 240#64) w.b3 ∗
     words10At ((fsp + 976#64) + 320#64) w.b4 ∗
     words10At ((fsp + 976#64) + 400#64) w.b5 ∗
     (((fsp + 976#64) + 480#64) ↦₁₂₈ w.q60) ∗
     (((fsp + 976#64) + 496#64) ↦₆₄ w.w62) ∗
     (((fsp + 976#64) + 504#64) ↦₁₂₈ w.q63) ∗
     (((fsp + 976#64) + 520#64) ↦₆₄ w.w65) ∗
     Frame)
    hfsp_align hpc hrun hsp hx19 hx20 hx24
  refine SepWP.weaken_pre ?_ (SepWP.mono hstep ?_)
  · dsimp only [words66At]; rw [h1056]; exact Entails.of_eq (by ac_rfl)
  · intro sm Pm _ _ ⟨hPm, hrest⟩
    refine ⟨Entails.trans hPm ?_, hrest⟩
    dsimp only [words66At]; rw [h1056]; exact Entails.of_eq (by ac_rfl)

theorem ct1Ack_ek_4448_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 349)
      (withLsCodeRoLoaded lsmpl (ct1AcknowledgedRecvEkChunkPlacedSpec A F K)))
    (s0 s4 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (w : Words66) (sp : SendEkSpills) (P_msg_rest R : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s4.mem)
    (hlen : st.receiving_ek.pts.length = 16)
    (hinv : statesRecvPreInv (F := F) (.ct1Acknowledged st))
    (hrecv_eq : ∀ res, st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res →
      States.recv K (.ct1Acknowledged st) msg = ct1AckRecvChunkToStatesResult res)
    (hmsg_recomp : chunkAt (msgA + 10#64) chunk ∗ P_msg_rest ⊢ messageAt spqrPolyApi msgA msg)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc4 : s4.pc = lsmpl.base 332 + 4448#64)
    (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = s0.sp - 4240#64)
    (hx2_4 : s4.readReg64 .x2 = st.uc.epoch)
    (hx19_4 : s4.readReg64 .x19 = outA)
    (hx20_4 : s4.readReg64 .x20 = selfA)
    (hx24_4 : s4.readReg64 .x24 = msgA)
    (htr4 : TraceCalleeSaved s4 s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s4
      (chunkAt (msgA + 10#64) chunk ∗ P_msg_rest ∗
       (selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
       memRegion (selfA + 536#64) 392 ∗
       words66At ((s0.sp - 4240#64) + 976#64) w ∗ memRegion ((s0.sp - 4240#64) + 1504#64) 352 ∗
       statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
       sendEkSpillsAt (s0.sp - 4240#64) sp ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
       memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
       statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (withLsCodeRoLoaded lsmpl (statesRecvVariantPlacedSpec A F K (.ct1Acknowledged st) msg)).post
            (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (statesRecvVariantPlacedSpec A F K (.ct1Acknowledged st) msg)).onPanic
            (outA, selfA, msgA) s0 sf ∗ R)) := by
  set fsp := s0.sp - 4240#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  obtain ⟨res, hrecv, herr⟩ :=
    ct1Acknowledged_recv_ek_chunk_cases_of_preInv K st chunk hlen hinv
  have hres_eq : States.recv K (.ct1Acknowledged st) msg = ct1AckRecvChunkToStatesResult res :=
    hrecv_eq res hrecv
  refine sepWPp_seq_clean_lscro hcro
    (ct1Ack_step_4448_call_placed (ext := ext) s4 fsp selfA msgA st.uc.epoch _ hpc4 hrun4 hsp4 hx2_4 hx20_4 hx24_4) ?_
  intro s5 hpc5 hrun5 ⟨hsp5, hx0_5, hx1_5, hx2_5, hx3_5, hx19_5, hx20_5, _, _, hx30_5, htr5⟩ hcro5
  have hx19_5' : s5.readReg64 .x19 = outA := hx19_5.trans hx19_4
  have htr5' : TraceCalleeSaved s5 s0 := htr5.trans htr4
  have hpre_call :
      chunkAt (msgA + 10#64) chunk ∗ P_msg_rest ∗
      (selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗
      relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
      memRegion (selfA + 536#64) 392 ∗
      words66At (fsp + 976#64) w ∗ memRegion (fsp + 1504#64) 352 ∗
      statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
      stackAt fsp statesRecvCalleeStackX ∗
      sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗
      statesRecvSavedCells s0 ⊢
      (memRegion (fsp + 1856#64) 528 ∗
       chunkedCt1AcknowledgedAt A (selfA + 8#64) st ∗ chunkAt (msgA + 10#64) chunk ∗
       unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       A.pool ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack) ∗
      (P_msg_rest ∗ statesRecvJumpTablePlacedAt ∗
       memRegion outA v1RecvSize ∗
       (selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion (fsp - 19552#64) 336 ∗
       sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) := by
    have hrecomp := recompose66_ct1Acknowledged A (selfA + 8#64) w st
    have h976 := words66At_976_352_entails_memRegion_880 fsp w
    dsimp only [statesRecvRoPlacedAt]
    rw [stackAt_statesRecvCallee_eq_ct1AcknowledgedRecvEkChunk fsp,
        memRegion_880_split_528_352 fsp]
    refine Entails.trans (Entails.of_eq (show _ =
      ((words66At (selfA + 8#64) w ∗
        relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w))) ∗
       (words66At (fsp + 976#64) w ∗ memRegion (fsp + 1504#64) 352)) ∗
      (memRegion (fsp + 1856#64) 528 ∗ chunkAt (msgA + 10#64) chunk ∗
       unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       A.pool ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack ∗
       P_msg_rest ∗ statesRecvJumpTablePlacedAt ∗
       memRegion outA v1RecvSize ∗
       (selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion (fsp - 19552#64) 336 ∗
       sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 2384#64) 352 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left (sepConj_mono hrecomp h976)) (Entails.of_eq (by ac_rfl))
  refine SepWPp.weaken_pre hpre_call ?_
  apply SepWPp.of_sepWP
  refine call_ct1AcknowledgedRecvEkChunk_placed (R := R) hcall
    (fsp + 1856#64) (selfA + 8#64) (msgA + 10#64) st chunk res
    hinv.1 hrecv hcro5 hpc5 hrun5 hsp5 hfsp_align hx30_5 htr5' hx0_5 hx1_5 hx2_5 hx3_5 rfl
    (fun sf Pf h hmem => by
      have h1 := h hmem
      dsimp only [withLsCodeRoLoaded, statesRecvVariantPlacedSpec, statesRecvOnPanic]
      rw [sepConj_assoc, satisfies_pure_sepConj] at h1 ⊢
      exact ⟨⟨Or.inr h1.1.1, h1.1.2⟩, h1.2⟩) ?_
  intro s6 hpc6 hrun6 hsp6 hcs6 htr6
  have hx19_6 : s6.readReg64 .x19 = outA := hcs6.1.trans hx19_5'
  have hx20_6 : s6.readReg64 .x20 = fsp + 1856#64 := hcs6.2.1.trans hx20_5
  have hself := selfA_11_528_392_entails_memRegion selfA
  cases res with
  | error err =>
    have he : err = .erroneousDataReceived := herr err rfl
    subst he
    have hret := ct1Ack_err_4468_ret_placed (A := A) (F := F) (ext := ext) s0 s6 outA selfA .erroneousDataReceived sp
      (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
      hsp0_align hpc6 hrun6 hsp6 hx19_6 htr6
    refine SepWP.weaken_pre ?_ (SepWP.mono hret ?_)
    · refine Entails.trans (Entails.of_eq (show _ =
        ((selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392) ∗
        (chunkAt (msgA + 10#64) chunk ∗ P_msg_rest) ∗
        ((statesRecvJumpTablePlacedAt ∗ unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗
         A.pool ∗ memRegion outA v1RecvSize ∗
         ct1AcknowledgedRecvEkChunkResAt A (F := F) (fsp + 1856#64) (.error .erroneousDataReceived) ∗
         (memRegion (fsp - 19552#64) 336 ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack) ∗
         sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hself (sepConj_mono_left hmsg_recomp))
        (Entails.of_eq (by
          rw [stackAt_statesRecvCallee_eq_ct1AcknowledgedRecvEkChunk (s0.sp - 4240#64)]
          dsimp only [statesRecvRoPlacedAt, fsp]; ac_rfl))
    · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨fun hmem_f => ?_, hsp_sf, hcs_sf⟩
      dsimp only [withLsCodeRoLoaded, statesRecvVariantPlacedSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htr_sf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) ?_) hmem_f⟩
      rw [hres_eq]; dsimp only [ct1AckRecvChunkToStatesResult]
      exact Entails.of_eq (by ac_rfl)
  | ok chunkRes =>
    cases chunkRes with
    | stillReceiving outSt =>
      have hret := ct1Ack_still_4468_ret_placed (A := A) (F := F) hmemcpy_sat s0 s6 outA selfA outSt sp
        (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
        hsp0_align hpc6 hrun6 hsp6 hx19_6 hx20_6 htr6
      refine SepWP.weaken_pre ?_ (SepWP.mono hret ?_)
      · refine Entails.trans (Entails.of_eq (show _ =
          ((selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392) ∗
          (chunkAt (msgA + 10#64) chunk ∗ P_msg_rest) ∗
          ((statesRecvJumpTablePlacedAt ∗ unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗
           A.pool ∗ memRegion outA v1RecvSize ∗
           ct1AcknowledgedRecvEkChunkResAt A (F := F) (fsp + 1856#64) (.ok (.stillReceiving outSt)) ∗
           (memRegion (fsp - 19552#64) 336 ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack) ∗
           sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
           memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
           sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hself (sepConj_mono_left hmsg_recomp))
          (Entails.of_eq (by
            rw [stackAt_statesRecvCallee_eq_ct1AcknowledgedRecvEkChunk (s0.sp - 4240#64)]
            dsimp only [statesRecvRoPlacedAt, fsp]; ac_rfl))
      · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨fun hmem_f => ?_, hsp_sf, hcs_sf⟩
        dsimp only [withLsCodeRoLoaded, statesRecvVariantPlacedSpec]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨htr_sf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) ?_) hmem_f⟩
        rw [hres_eq]; dsimp only [ct1AckRecvChunkToStatesResult]
        exact Entails.of_eq (by ac_rfl)
    | done outSt =>
      have hret := ct1Ack_done_4468_ret_placed (A := A) (F := F) hmemcpy_sat s0 s6 outA selfA outSt sp
        (messageAt spqrPolyApi msgA msg ∗ statesRecvJumpTablePlacedAt ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
        hsp0_align hpc6 hrun6 hsp6 hx19_6 hx20_6 htr6
      refine SepWP.weaken_pre ?_ (SepWP.mono hret ?_)
      · refine Entails.trans (Entails.of_eq (show _ =
          ((selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392) ∗
          (chunkAt (msgA + 10#64) chunk ∗ P_msg_rest) ∗
          ((statesRecvJumpTablePlacedAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool) ∗
           unchunkedSendCt2PlacedRoAt ∗
           memRegion outA v1RecvSize ∗
           ct1AcknowledgedRecvEkChunkResAt A (F := F) (fsp + 1856#64) (.ok (.done outSt)) ∗
           (memRegion (fsp - 19552#64) 336 ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack) ∗
           sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
           memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
           sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hself (sepConj_mono_left hmsg_recomp))
          (Entails.of_eq (by
            rw [stackAt_statesRecvCallee_eq_ct1AcknowledgedRecvEkChunk (s0.sp - 4240#64)]
            dsimp only [fsp]; ac_rfl))
      · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨fun hmem_f => ?_, hsp_sf, hcs_sf⟩
        dsimp only [withLsCodeRoLoaded, statesRecvVariantPlacedSpec, statesRecvRoPlacedAt]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨htr_sf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) ?_) hmem_f⟩
        rw [hres_eq]; dsimp only [ct1AckRecvChunkToStatesResult]
        exact Entails.of_eq (by ac_rfl)

theorem states_recv_ct1Acknowledged_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : StatesRecvPlacedContracts A F K ext)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl (statesRecvVariantPlacedSpec A F K (.ct1Acknowledged st) msg)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcro0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [statesRecvVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.ct1Acknowledged st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  have hpro := states_recv_prologue_placed (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Acknowledged st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean_lscro hcro0 hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩ hcro1
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch_ct1Acknowledged_placed (ext := ext) s1 fsp selfA
    (chunkedCt1AcknowledgedAt A (selfA + 8#64) st ∗ memRegion (selfA + 536#64) 392 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗
     statesRecvSavedCells s0)
    hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_clean_lscro hcro1 (SepWP.weaken_pre (Entails.of_eq (by dsimp only [fsp]; ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩ hcro2
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  have hpre_split :
      (selfA ↦₆₄ 11#64) ∗ statesRecvRoPlacedAt ∗
      (chunkedCt1AcknowledgedAt A (selfA + 8#64) st ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0) ⊢
      (∃∗ w : Words66, ∃∗ sp : SendEkSpills,
        ⌜st.receiving_ek.pts.length = 16 ∧ (w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w5 = st.uc.epoch)⌝ ∗
        (memRegion (fsp + 976#64) 528 ∗ words66At (selfA + 8#64) w ∗
         stackAt fsp statesRecvCalleeStackX ∗
         ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
          ct1AckPayloadTailAt msgA msg.payload ∗
          (selfA ↦₆₄ 11#64) ∗
          relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
          memRegion (selfA + 536#64) 392 ∗
          statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
          sendEkSpillsAt fsp sp ∗
          memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
          memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0))) := by
    rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg]
    have hex66 : chunkedCt1AcknowledgedAt A (selfA + 8#64) st ⊢
        ∃∗ w : Words66,
          ⌜st.receiving_ek.pts.length = 16 ∧ (w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w5 = st.uc.epoch)⌝ ∗
          words66At (selfA + 8#64) w ∗
          relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) := by
      refine Entails.trans (chunkedCt1AcknowledgedAt_entails_pts_length_16 A (selfA + 8#64) st) ?_
      apply Entails.pure_left; intro hlen
      refine Entails.trans (chunkedCt1AcknowledgedAt_extract66 A (selfA + 8#64) st) ?_
      apply Entails.sepExists_elim; intro w
      apply Entails.pure_left; intro hw
      exact Entails.sepExists_right w (Entails.pure_right ⟨hlen, hw⟩ (Entails.refl _))
    have hstk : memRegion fsp 4144 ⊢
        ∃∗ sp : SendEkSpills,
          sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 976#64) 528 ∗ memRegion (fsp + 1504#64) 352 ∗
          memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp := by
      refine Entails.trans (memRegion_4144_entails_sendEkFrame fsp) ?_
      apply Entails.sepExists_elim; intro sp
      rw [memRegion_976_880_split_528_352 fsp]
      exact Entails.sepExists_right sp (Entails.of_eq (by ac_rfl))
    refine Entails.trans (Entails.of_eq (show _ =
      chunkedCt1AcknowledgedAt A (selfA + 8#64) st ∗ memRegion fsp 4144 ∗
      ((selfA ↦₆₄ 11#64) ∗ statesRecvRoPlacedAt ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion outA v1RecvSize ∗
       ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
        ct1AckPayloadTailAt msgA msg.payload) ∗
       A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hex66 (sepConj_mono_left hstk)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro sp
    apply Entails.sepExists_elim; intro w
    exact Entails.sepExists_right w (Entails.sepExists_right sp (Entails.of_eq (by ac_rfl)))
  refine SepWPp.weaken_pre hpre_split ?_
  apply ct1Ack_sepWPp_intro_ex hrun2; intro w
  apply ct1Ack_sepWPp_intro_ex hrun2; intro sp
  apply SepWPp.pure_left; rintro ⟨hlen, _, hep⟩
  refine sepWPp_seq_clean_lscro hcro2 (ct1Ack_step_588_608_placed hC.hmemcpy_sat s2 fsp outA selfA msgA w
    ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
     ct1AckPayloadTailAt msgA msg.payload ∗
     (selfA ↦₆₄ 11#64) ∗
     relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
     memRegion (selfA + 536#64) 392 ∗
     statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
     sendEkSpillsAt fsp sp ∗
     memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
     memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    hfsp_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx24_2) ?_
  intro s2b hpc2b hrun2b ⟨hsp2b, hx19_2b, hx20_2b, hx24_2b, _, htr2b⟩ hcro2b
  have htr2b0 : TraceCalleeSaved s2b s0 := htr2b.trans htr20
  refine sepWPp_seq_clean_lscro hcro2b (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (ct1Ack_step_608_632_words66_placed (ext := ext) s2b fsp outA selfA msgA msg.epoch w
      (words66At (selfA + 8#64) w ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
       ct1AckPayloadTailAt msgA msg.payload ∗
       (selfA ↦₆₄ 11#64) ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
       memRegion (selfA + 536#64) 392 ∗
       statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
       memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc2b hrun2b hsp2b hx19_2b hx20_2b hx24_2b)) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, hx2_3, hx9_3, hx19_3, hx20_3, hx24_3, _, hx8_3, hz_3, htr3⟩ hcro3
  have htr30 : TraceCalleeSaved s3 s0 := htr3.trans htr2b0
  rw [hep] at hx9_3 hx8_3 hz_3
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_seq_clean_lscl hcro3.1
      (ct1Ack_step_632_644_gt_placed (ext := ext) s3 fsp outA selfA msgA msg.epoch st.uc.epoch _
        hgt hpc3 hrun3 hsp3 hx2_3 hx9_3 hx19_3 hx20_3 hx24_3 hx8_3 hz_3) ?_
    intro s4 hpc4 hrun4 ⟨hsp4, hx2_4, _, hx19_4, _, _, _, htr4⟩ hcl4
    have hrecv := states_recv_ct1Acknowledged_gt K st msg hgt
    have hexit := ct1Ack_gt_644_ret_placed hC.hdealloc_sat s0 s4 outA selfA msg.epoch st
      (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
      hcl4 hsp0_align hpc4 hrun4 hsp4 hx2_4 hx19_4 (htr4.trans htr30)
    refine sepWPp_of_statesRecv_exit_placed s0 s4 outA selfA msgA (.ct1Acknowledged st) msg _ R ?_
    refine SepWP.weaken_pre ?_ (SepWP.mono hexit ?_)
    · rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg]
      have hself_mem := selfA_ct1Acknowledged_entails_memRegion selfA w
      have hrecomp := recompose66_ct1Acknowledged A (fsp + 976#64) w st
      have hstk := sendEkFrame_entails_976_2288 fsp sp
      refine Entails.trans (Entails.of_eq (show _ =
        ((selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗ memRegion (selfA + 536#64) 392) ∗
        (words66At (fsp + 976#64) w ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w))) ∗
        (sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
         memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp) ∗
        (((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
          ct1AckPayloadTailAt msgA msg.payload) ∗
         statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
         memRegion (fsp + 1504#64) 352 ∗ A.pool ∗
         stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
      exact Entails.trans
        (sepConj_mono hself_mem (sepConj_mono hrecomp (sepConj_mono_left hstk)))
        (Entails.of_eq (by dsimp only [fsp]; ac_rfl))
    · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv]; exact Entails.of_eq (by ac_rfl)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_seq_clean_lscl hcro3.1
        (ct1Ack_step_632_4516_lt_placed (ext := ext) s3 fsp outA selfA msgA msg.epoch st.uc.epoch _
          hlt hpc3 hrun3 hsp3 hx2_3 hx9_3 hx19_3 hx20_3 hx24_3 hx8_3 hz_3) ?_
      intro s4 hpc4 hrun4 ⟨hsp4, _, hx9_4, hx19_4, hx20_4, _, _, htr4⟩ _
      have hrecv := states_recv_ct1Acknowledged_lt K st msg hlt
      rw [← hep] at hx9_4
      have hexit := ct1Ack_noop_4516_ret_placed (A := A) (F := F) hC.hmemcpy_sat s0 s4 outA selfA st w sp
        (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
        hsp0_align hpc4 hrun4 hsp4 hx9_4 hx19_4 hx20_4 (htr4.trans htr30)
      refine sepWPp_of_statesRecv_exit_placed s0 s4 outA selfA msgA (.ct1Acknowledged st) msg _ R ?_
      refine SepWP.weaken_pre
        (Entails.of_eq (by rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg]; dsimp only [fsp]; ac_rfl))
        (SepWP.mono hexit ?_)
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv]; exact Entails.of_eq (by ac_rfl)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      refine sepWPp_seq_clean_lscro hcro3
        (ct1Ack_step_632_4432_eq_placed (ext := ext) s3 fsp outA selfA msgA msg.epoch st.uc.epoch _
          heq hpc3 hrun3 hsp3 hx2_3 hx9_3 hx19_3 hx20_3 hx24_3 hx8_3 hz_3) ?_
      intro s4 hpc4 hrun4 ⟨hsp4, hx2_4, hx9_4, hx19_4, hx20_4, hx24_4, _, htr4⟩ hcro4
      have htr40 : TraceCalleeSaved s4 s0 := htr4.trans htr30
      rw [heq] at hx2_4
      cases hpay : msg.payload with
      | ek chunk =>
        have hcond : (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag msg.payload) &&& 25769803782#64) != 2#32) = false := by
          rw [hpay]; exact messagePayloadTag_and6_bne_2_of_ek chunk
        refine sepWPp_seq_clean_lscro hcro4
          (SepWP.weaken_pre (Entails.of_eq (by rw [hpay]; ac_rfl))
            (ct1Ack_step_4432_4448_ek_placed (ext := ext) s4 fsp outA selfA msgA st.uc.epoch msg.payload
              (words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
               words66At (selfA + 8#64) w ∗ ct1AckPayloadTailAt msgA msg.payload ∗
               (selfA ↦₆₄ 11#64) ∗
               relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
               memRegion (selfA + 536#64) 392 ∗
               statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
               stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗
               memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
               memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
              hcond hpc4 hrun4 hsp4 hx2_4 hx9_4 hx19_4 hx20_4 hx24_4)) ?_
        intro s5 hpc5 hrun5 ⟨hsp5, hx2_5, _, hx19_5, hx20_5, hx24_5, _, htr5⟩ hcro5
        have hmsg_recomp :
            chunkAt (msgA + 10#64) chunk ∗
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
             memRegion (msgA + 0x09#64) 1 ∗ memRegion (msgA + 0x2c#64) 4) ⊢
            messageAt spqrPolyApi msgA msg := by
          rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg, hpay]
          dsimp only [ct1AckPayloadTailAt]
          exact Entails.of_eq (by ac_rfl)
        refine SepWPp.weaken_pre
          (Entails.of_eq (by rw [hpay]; dsimp only [ct1AckPayloadTailAt, fsp]; ac_rfl))
          (ct1Ack_ek_4448_ret_placed hC.hmemcpy_sat hC.ct1AcknowledgedRecvEkChunk_ok s0 s5 outA selfA msgA st msg chunk w sp
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag (.ek chunk)) ∗
             memRegion (msgA + 0x09#64) 1 ∗ memRegion (msgA + 0x2c#64) 4)
            R hcro5 hlen hinv
            (fun res hrecv => states_recv_ct1Acknowledged_eq_ek_res K st msg chunk res heq hpay hrecv)
            (by rw [← hpay]; exact hmsg_recomp)
            hsp0_align hpc5 hrun5 hsp5 hx2_5 hx19_5 hx20_5 hx24_5 (htr5.trans htr40))
      | ekCt1Ack chunk =>
        have hcond : (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag msg.payload) &&& 25769803782#64) != 2#32) = false := by
          rw [hpay]; exact messagePayloadTag_and6_bne_2_of_ekCt1Ack chunk
        refine sepWPp_seq_clean_lscro hcro4
          (SepWP.weaken_pre (Entails.of_eq (by rw [hpay]; ac_rfl))
            (ct1Ack_step_4432_4448_ek_placed (ext := ext) s4 fsp outA selfA msgA st.uc.epoch msg.payload
              (words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
               words66At (selfA + 8#64) w ∗ ct1AckPayloadTailAt msgA msg.payload ∗
               (selfA ↦₆₄ 11#64) ∗
               relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
               memRegion (selfA + 536#64) 392 ∗
               statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
               stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗
               memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
               memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
              hcond hpc4 hrun4 hsp4 hx2_4 hx9_4 hx19_4 hx20_4 hx24_4)) ?_
        intro s5 hpc5 hrun5 ⟨hsp5, hx2_5, _, hx19_5, hx20_5, hx24_5, _, htr5⟩ hcro5
        have hmsg_recomp :
            chunkAt (msgA + 10#64) chunk ∗
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
             memRegion (msgA + 0x09#64) 1 ∗ memRegion (msgA + 0x2c#64) 4) ⊢
            messageAt spqrPolyApi msgA msg := by
          rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg, hpay]
          dsimp only [ct1AckPayloadTailAt]
          exact Entails.of_eq (by ac_rfl)
        refine SepWPp.weaken_pre
          (Entails.of_eq (by rw [hpay]; dsimp only [ct1AckPayloadTailAt, fsp]; ac_rfl))
          (ct1Ack_ek_4448_ret_placed hC.hmemcpy_sat hC.ct1AcknowledgedRecvEkChunk_ok s0 s5 outA selfA msgA st msg chunk w sp
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag (.ekCt1Ack chunk)) ∗
             memRegion (msgA + 0x09#64) 1 ∗ memRegion (msgA + 0x2c#64) 4)
            R hcro5 hlen hinv
            (fun res hrecv => states_recv_ct1Acknowledged_eq_ekCt1Ack_res K st msg chunk res heq hpay hrecv)
            (by rw [← hpay]; exact hmsg_recomp)
            hsp0_align hpc5 hrun5 hsp5 hx2_5 hx19_5 hx20_5 hx24_5 (htr5.trans htr40))
      | _ =>
        have hek : ∀ c, msg.payload ≠ .ek c := by intro c h; rw [hpay] at h; cases h
        have hekAck : ∀ c, msg.payload ≠ .ekCt1Ack c := by intro c h; rw [hpay] at h; cases h
        have hrecv := states_recv_ct1Acknowledged_eq_other K st msg heq hek hekAck
        refine sepWPp_seq_clean_lscl hcro4.1
          (SepWP.weaken_pre (Entails.of_eq (by rw [hpay]; ac_rfl))
            (ct1Ack_step_4432_4516_not_ek_placed (ext := ext) s4 fsp outA selfA msgA st.uc.epoch msg.payload
              (words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
               words66At (selfA + 8#64) w ∗ ct1AckPayloadTailAt msgA msg.payload ∗
               (selfA ↦₆₄ 11#64) ∗
               relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
               memRegion (selfA + 536#64) 392 ∗
               statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
               stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗
               memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
               memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
              hek hekAck hpc4 hrun4 hsp4 hx9_4 hx19_4 hx20_4 hx24_4)) ?_
        intro s5 hpc5 hrun5 ⟨hsp5, hx9_5, hx19_5, hx20_5, _, _, htr5⟩ _
        rw [← hep] at hx9_5
        have hexit := ct1Ack_noop_4516_ret_placed (A := A) (F := F) hC.hmemcpy_sat s0 s5 outA selfA st w sp
          (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
          hsp0_align hpc5 hrun5 hsp5 hx9_5 hx19_5 hx20_5 (htr5.trans htr40)
        refine sepWPp_of_statesRecv_exit_placed s0 s5 outA selfA msgA (.ct1Acknowledged st) msg _ R ?_
        refine SepWP.weaken_pre
          (Entails.of_eq (by rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg]; dsimp only [fsp]; ac_rfl))
          (SepWP.mono hexit ?_)
        intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
        rw [hrecv]; exact Entails.of_eq (by ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

alias ct1Ack_step_4468_done_4924_placed :=
  LibsignalBinary.Proofs.SpqrV1.States.Recv.ct1Ack_step_4468_done_4924_placed
alias ct1Ack_done_4468_ret_placed :=
  LibsignalBinary.Proofs.SpqrV1.States.Recv.ct1Ack_done_4468_ret_placed
alias ct1Ack_step_608_632_words66_placed :=
  LibsignalBinary.Proofs.SpqrV1.States.Recv.ct1Ack_step_608_632_words66_placed
alias ct1Ack_ek_4448_ret_placed :=
  LibsignalBinary.Proofs.SpqrV1.States.Recv.ct1Ack_ek_4448_ret_placed
alias states_recv_ct1Acknowledged_placed_ok_ext :=
  LibsignalBinary.Proofs.SpqrV1.States.Recv.states_recv_ct1Acknowledged_placed_ok_ext

end CryptoVerification.SpqrV1.States.Recv
