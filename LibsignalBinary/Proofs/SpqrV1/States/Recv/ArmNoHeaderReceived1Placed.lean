/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceived1
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.noHeaderReceived` Arm, Part 1 (Relocatable)

Relocatable `[LibsignalPlacement]` branch assembly lemmas (`>`, `<`, and `= ∧ ¬ .hdr`) for
`.noHeaderReceived` (`lsmpl.base 332 + 2132#64`, tag `7#64`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

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
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.Recv

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  Recv.sp_sub_96_add_16 Recv.sp_sub_96_add_32 Recv.sp_sub_96_add_48 Recv.sp_sub_96_add_64 Recv.sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

theorem nhr_8984_ret_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s1 : State) (outA : BitVec 64) (sp1 : SendEkSpills) (w63 : Words63)
    (P_rest Q_out : SepProp) (hsp0_align : s0.spAligned = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 8984#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (htr1 : TraceCalleeSaved s1 s0)
    (hw63 : writebackAt8984 s1 sp1 = w63)
    (hout : ∀ (w936 : BitVec 64) (q944 : BitVec 128),
      P_rest ∗ (outA ↦₆₄ sp1.b2.w7) ∗ words63At (outA + 8#64) w63 ∗
        memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
        ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944) ∗
        stackAt s0.sp statesRecvStackX ⊢ Q_out) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (P_rest ∗ memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ Q_out) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := lsmpl.base 332 + 18996#64)
    (P_mid := P_rest ∗ memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
      sendEkSpillsAt fsp (nhrSpills8984 s1 sp1) ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x19 = outA ∧
      writebackWords63 s2 (nhrSpills8984 s1 sp1) = w63 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · have hstep := nhr_step_8984_18996_placed (ext := ext) s1 fsp sp1
      (P_rest ∗ memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc1 hrun1 hsp1
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
    intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7, h2_8, h2_9,
      h2_10, h2_11, h2_12, h2_13, h2_14, h2_15, h2_16, h2_17, h2_19, h2_20, h2_21, h2_22,
      h2_23, h2_24, h2_25, h2_26, h2_27, h2_28, _, h2_30, htr2⟩
    have hwb := (writebackWords63_at_8984 s1 s2 sp1
      h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_8 h2_9 h2_10 h2_11 h2_12 h2_13 h2_14 h2_15 h2_16 h2_17
      h2_20 h2_21 h2_22 h2_23 h2_24 h2_25 h2_26 h2_27 h2_28 h2_30).trans hw63
    exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hsp2, h2_19.trans hx19, hwb, htr2.trans htr1⟩
  · intro s2 hpc2 hrun2 ⟨hsp2, h2_19, hwb, htr2⟩
    have hwrite := states_recv_writeback_59e88_sat_placed hmemcpy_sat (Relocatable.of_memRegion 376)
      s0 s2 outA (nhrSpills8984 s1 sp1) P_rest
      hpc2 hrun2 hsp2 hsp0_align h2_19 htr2
    refine SepWP.mono hwrite ?_
    intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
    refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
    have htag : (nhrSpills8984 s1 sp1).b2.w7 = sp1.b2.w7 := rfl
    have hnone : (nhrSpills8984 s1 sp1).b2.w8 = noneCap := rfl
    rw [htag, hnone, hwb]
    exact hout (s2.readReg64 .x20) (nhrSpills8984 s1 sp1).q200

theorem nhr_noop_8664_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA selfA : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (w : Words57) (sp : SendEkSpills) (P_rest : SepProp)
    (hsp0_align : s0.spAligned = true) (hw62 : sp.w62 = w.b0.w6)
    (hpc : s.pc = lsmpl.base 332 + 8664#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64)
    (hx19 : s.readReg64 .x19 = outA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        words57At ((s0.sp - 4240#64) + 2752#64) w ∗
        nhrUnusedRestAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .noHeaderReceived st }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := lsmpl.base 332 + 8984#64)
    (P_mid := (P_rest ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w))) ∗
      memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
      sendEkSpillsAt fsp (nhrSpills8664 sp w) ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s1 =>
      s1.sp = fsp ∧ s1.readReg64 .x19 = outA ∧
      writebackAt8984 s1 (nhrSpills8664 sp w) =
        { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4
          b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56,
                 sp.b1.w0, sp.b3.w0, sp.b1.w7⟩
          q60 := sp.q3c0, w62 := sp.b3.w1 } ∧
      TraceCalleeSaved s1 s0)
    ?_ ?_
  · have hstep1 := nhr_step_8664_8984_placed (ext := ext) s fsp w sp
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
       nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep1 ?_)
    intro s1 Pm _ _ ⟨hPm, hsp1, h1_0, h1_1, h1_2, h1_3, h1_4, h1_5, h1_6, h1_7,
      h1_9, h1_10, h1_11, h1_12, h1_13, h1_14, h1_15, h1_16, h1_17, h1_18, h1_19,
      h1_20, h1_22, h1_23, h1_24, h1_25, h1_26, h1_27, h1_28, _, h1_30, htr1⟩
    have hwb := writebackAt8984_nhr_noop s1 sp w hw62
      h1_0 h1_1 h1_2 h1_3 h1_4 h1_5 h1_6 h1_7 h1_9 h1_10 h1_11 h1_12 h1_13 h1_14 h1_15 h1_16 h1_17 h1_18
      h1_20 h1_22 h1_23 h1_24 h1_25 h1_26 h1_27 h1_28 h1_30
    refine ⟨Entails.trans hPm ?_, hsp1, h1_19.trans hx19, hwb, htr1.trans htr⟩
    have hunused := words57At_nhrUnusedRest_entails_sendEkUnusedAt fsp w
    refine Entails.trans (Entails.of_eq (show _ =
      (words57At (fsp + 2752#64) w ∗ nhrUnusedRestAt fsp) ∗
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (nhrSpills8664 sp w) ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       memRegion (fsp + 1856#64) 880 ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hunused) (Entails.of_eq (by ac_rfl))
  · intro s1 hpc1 hrun1 ⟨hsp1, h1_19, hwb, htr1⟩
    refine nhr_8984_ret_placed hmemcpy_sat s0 s1 outA (nhrSpills8664 sp w) _
      (P_rest ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)))
      _ hsp0_align hpc1 hrun1 hsp1 h1_19 htr1 hwb ?_
    intro w936 q944
    have htag : (nhrSpills8664 sp w).b2.w7 = 7#64 := rfl
    rw [htag]
    have hout := nhr_stillReceiving_out_entails_resultV1RecvAt A (F := F) outA st w
      sp.b1.w0 sp.b3.w0 sp.b1.w7 sp.q3c0 sp.b3.w1 w936 q944
    refine Entails.trans (Entails.of_eq (show _ =
      P_rest ∗
      ((outA ↦₆₄ 7#64) ∗
       words63At (outA + 8#64)
         { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4
           b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56,
                  sp.b1.w0, sp.b3.w0, sp.b1.w7⟩
           q60 := sp.q3c0, w62 := sp.b3.w1 } ∗
       memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
       ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944) ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w))) ∗
      memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left hout)

theorem nhr_still_15296_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s1 : State) (outA selfA : BitVec 64)
    (outSt : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (w_out : Words57) (sp sp1 : SendEkSpills) (P_rest : SepProp)
    (hsp0_align : s0.spAligned = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 15296#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA)
    (hps1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (hwb1 : writebackStillAt15296 s1 sp1 =
      { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4
        b5 := ⟨w_out.w50, w_out.w51, w_out.w52, w_out.w53, w_out.w54, w_out.w55, w_out.w56,
               sp.b1.w0, sp.b3.w0, sp.b1.w7⟩
        q60 := sp.q3c0, w62 := sp.b3.w1 }) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .noHeaderReceived outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := lsmpl.base 332 + 8984#64)
    (P_mid := (P_rest ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out))) ∗
      memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
      sendEkSpillsAt fsp (nhrSpillsStill8984 s1 sp1) ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = outA ∧
      writebackAt8984 s2 (nhrSpillsStill8984 s1 sp1) =
        { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4
          b5 := ⟨w_out.w50, w_out.w51, w_out.w52, w_out.w53, w_out.w54, w_out.w55, w_out.w56,
                 sp.b1.w0, sp.b3.w0, sp.b1.w7⟩, q60 := sp.q3c0, w62 := sp.b3.w1 } ∧ TraceCalleeSaved s2 s0) ?_ ?_
  · have hstep2 := nhr_step_15296_still_8984_placed (ext := ext) s1 fsp sp1
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc1 hrun1 hsp1 hps1
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep2 ?_)
    intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_8, h2_9, h2_10, h2_11, h2_12, h2_13, h2_14, h2_15, h2_16, h2_17, h2_18, h2_19,
      h2_20, h2_21, h2_22, h2_23, h2_24, h2_25, h2_26, h2_27, h2_28, _, h2_30, htr2⟩
    have hwb := (writebackAt8984_of_still15296 s1 s2 sp1
      h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_8 h2_9 h2_10 h2_11 h2_12 h2_13 h2_14 h2_15 h2_16 h2_17 h2_18
      h2_20 h2_21 h2_22 h2_23 h2_24 h2_25 h2_26 h2_27 h2_28 h2_30).trans hwb1
    exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hsp2, h2_19.trans hx19, hwb, htr2.trans htr1⟩
  · intro s2 hpc2 hrun2 ⟨hsp2, h2_19, hwb, htr2⟩
    refine nhr_8984_ret_placed hmemcpy_sat s0 s2 outA (nhrSpillsStill8984 s1 sp1) _
      (P_rest ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)))
      _ hsp0_align hpc2 hrun2 hsp2 h2_19 htr2 hwb (fun w936 q944 => ?_)
    have htag : (nhrSpillsStill8984 s1 sp1).b2.w7 = 7#64 := rfl
    rw [htag]
    have hout := nhr_stillReceiving_out_entails_resultV1RecvAt A (F := F) outA outSt w_out
      sp.b1.w0 sp.b3.w0 sp.b1.w7 sp.q3c0 sp.b3.w1 w936 q944
    refine Entails.trans (Entails.of_eq (show _ = P_rest ∗
      ((outA ↦₆₄ 7#64) ∗ words63At (outA + 8#64)
         { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4
           b5 := ⟨w_out.w50, w_out.w51, w_out.w52, w_out.w53, w_out.w54, w_out.w55, w_out.w56,
                  sp.b1.w0, sp.b3.w0, sp.b1.w7⟩, q60 := sp.q3c0, w62 := sp.b3.w1 } ∗
       memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
       ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944) ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out))) ∗
      memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left hout)

theorem nhr_still_8616_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA selfA w58 w59 : BitVec 64)
    (outSt : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (w_out : Words57) (sp : SendEkSpills) (P_rest : SepProp)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = lsmpl.base 332 + 8616#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64)
    (hx19 : s.readReg64 .x19 = outA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        words60At ((s0.sp - 4240#64) + 1856#64) (mkWords60_still w_out w58 w59) ∗
        memRegion ((s0.sp - 4240#64) + 2336#64) 400 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .noHeaderReceived outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  set w60 := mkWords60_still w_out w58 w59
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := lsmpl.base 332 + 15296#64)
    (P_mid := P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (nhrSpills15296 sp w60) ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = outA ∧ s1.pstate = addsPState64 noneCap 1#64 ∧
      writebackStillAt15296 s1 (nhrSpills15296 sp w60) =
        { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4
          b5 := ⟨w_out.w50, w_out.w51, w_out.w52, w_out.w53, w_out.w54, w_out.w55, w_out.w56,
                 sp.b1.w0, sp.b3.w0, sp.b1.w7⟩, q60 := sp.q3c0, w62 := sp.b3.w1 } ∧ TraceCalleeSaved s1 s0) ?_ ?_
  · have hstep1 := nhr_step_8616_ok_15296_placed (ext := ext) s fsp w60 sp
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2336#64) 400 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align (show noneCap ≠ 0xfffffffffffffffe#64 by decide) hpc hrun hsp
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep1 ?_)
    intro s1 Pm _ _ ⟨hPm, hsp1, h1_0, h1_1, h1_2, h1_4, h1_5, h1_6, h1_7, h1_8,
      h1_9, h1_10, h1_11, h1_12, h1_13, h1_14, h1_15, h1_16, h1_17, h1_18, h1_19,
      h1_20, h1_21, h1_22, h1_23, _, _, h1_26, h1_27, _, _, h1_30, hps1, htr1⟩
    have hwb1 := writebackStillAt15296_of_8616 s1 sp w_out w58 w59
      h1_0 h1_1 h1_2 h1_4 h1_5 h1_6 h1_7 h1_8 h1_9 h1_10 h1_11 h1_12 h1_13 h1_14 h1_15 h1_16 h1_17 h1_18
      h1_20 h1_21 h1_22 h1_23 h1_26 h1_27 h1_30
    refine ⟨Entails.trans hPm ?_, hsp1, h1_19.trans hx19, hps1, hwb1, htr1.trans htr⟩
    have h880 := words60At_1856_400_entails_memRegion_880 fsp w60
    refine Entails.trans (Entails.of_eq (show _ =
      (words60At (fsp + 1856#64) w60 ∗ memRegion (fsp + 2336#64) 400) ∗
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (nhrSpills15296 sp w60) ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h880) (Entails.of_eq (by ac_rfl))
  · intro s1 hpc1 hrun1 ⟨hsp1, h1_19, hps1, hwb1, htr1⟩
    exact nhr_still_15296_ret_placed hmemcpy_sat s0 s1 outA selfA outSt w_out sp (nhrSpills15296 sp w60) P_rest
      hsp0_align hpc1 hrun1 hsp1 h1_19 hps1 htr1 hwb1

theorem nhr_done_15296_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s1 : State) (outA selfA : BitVec 64)
    (outSt : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (w_out : Words60) (sp sp1 : SendEkSpills) (P_rest : SepProp)
    (hsp0_align : s0.spAligned = true) (hw0_ne_none : w_out.b0.w0 ≠ noneCap)
    (hpc1 : s1.pc = lsmpl.base 332 + 15296#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (hps1 : s1.pstate = addsPState64 w_out.b0.w0 1#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (hwb1 : writebackDoneAt15296 s1 sp1 w_out.b5.w8 w_out.b5.w9 =
      { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4, b5 := w_out.b5,
        q60 := sp.q3c0, w62 := sp.b3.w1 }) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      ((lsLogFilterAddr ↦₆₄ 0#64) ∗ P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        (((s0.sp - 4240#64) + 2320#64) ↦₆₄ w_out.b5.w8) ∗ (((s0.sp - 4240#64) + 2328#64) ↦₆₄ w_out.b5.w9) ∗
        nhrRest1856At (s0.sp - 4240#64) w_out ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ (lsLogFilterAddr ↦₆₄ 0#64) ∗ P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerReceived outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := lsmpl.base 332 + 8984#64)
    (P_mid := ((lsLogFilterAddr ↦₆₄ 0#64) ∗ P_rest ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out))) ∗
      memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
      sendEkSpillsAt fsp (nhrSpillsDone8984 s1 sp1 w_out.b5.w8 w_out.b5.w9) ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = outA ∧
      writebackAt8984 s2 (nhrSpillsDone8984 s1 sp1 w_out.b5.w8 w_out.b5.w9) =
        { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4, b5 := w_out.b5,
          q60 := sp.q3c0, w62 := sp.b3.w1 } ∧ TraceCalleeSaved s2 s0) ?_ ?_
  · have hstep2 := nhr_step_15296_done_8984_placed (ext := ext) s1 fsp w_out.b0.w0 w_out.b5.w8 w_out.b5.w9 sp1
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       nhrRest1856At fsp w_out ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hw0_ne_none hpc1 hrun1 hsp1 hps1
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep2 ?_)
    intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_8, h2_9, h2_10, h2_11, h2_12, h2_13, h2_14, h2_15, h2_16, h2_17, h2_18, h2_19,
      h2_20, h2_21, h2_22, h2_23, h2_24, h2_25, h2_26, h2_27, h2_28, _, h2_30, htr2⟩
    have hwb := (writebackAt8984_of_done15296 s1 s2 sp1 w_out.b5.w8 w_out.b5.w9
      h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_8 h2_9 h2_10 h2_11 h2_12 h2_13 h2_14 h2_15 h2_16 h2_17 h2_18
      h2_20 h2_21 h2_22 h2_23 h2_24 h2_25 h2_26 h2_27 h2_28 h2_30).trans hwb1
    refine ⟨Entails.trans hPm ?_, hsp2, h2_19.trans hx19, hwb, htr2.trans htr1⟩
    have h880 := nhrRest1856At_rejoin_880 fsp w_out
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 2320#64) ↦₆₄ w_out.b5.w8) ∗ ((fsp + 2328#64) ↦₆₄ w_out.b5.w9) ∗ nhrRest1856At fsp w_out) ∗
      ((lsLogFilterAddr ↦₆₄ 0#64) ∗ P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (nhrSpillsDone8984 s1 sp1 w_out.b5.w8 w_out.b5.w9) ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h880) (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 ⟨hsp2, h2_19, hwb, htr2⟩
    refine nhr_8984_ret_placed hmemcpy_sat s0 s2 outA (nhrSpillsDone8984 s1 sp1 w_out.b5.w8 w_out.b5.w9) _
      ((lsLogFilterAddr ↦₆₄ 0#64) ∗ P_rest ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)))
      _ hsp0_align hpc2 hrun2 hsp2 h2_19 htr2 hwb (fun w936 q944 => ?_)
    have htag : (nhrSpillsDone8984 s1 sp1 w_out.b5.w8 w_out.b5.w9).b2.w7 = 8#64 := rfl
    rw [htag]
    have hout := nhr_done_out_entails_resultV1RecvAt A (F := F) outA outSt w_out
      sp.q3c0 sp.b3.w1 w936 q944
    refine Entails.trans (Entails.of_eq (show _ = (lsLogFilterAddr ↦₆₄ 0#64) ∗ P_rest ∗
      ((outA ↦₆₄ 8#64) ∗ words63At (outA + 8#64)
         { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4, b5 := w_out.b5,
           q60 := sp.q3c0, w62 := sp.b3.w1 } ∗
       memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
       ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944) ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out))) ∗
      memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hout))

theorem nhr_done_8616_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA selfA : BitVec 64)
    (outSt : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (w_out : Words60) (sp : SendEkSpills) (P_rest : SepProp)
    (hsp0_align : s0.spAligned = true)
    (hw0_ne_err : w_out.b0.w0 ≠ 0xfffffffffffffffe#64) (hw0_ne_none : w_out.b0.w0 ≠ noneCap)
    (hpc : s.pc = lsmpl.base 332 + 8616#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64)
    (hx19 : s.readReg64 .x19 = outA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      ((lsLogFilterAddr ↦₆₄ 0#64) ∗ P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        words60At ((s0.sp - 4240#64) + 1856#64) w_out ∗ memRegion ((s0.sp - 4240#64) + 2336#64) 400 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ (lsLogFilterAddr ↦₆₄ 0#64) ∗ P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerReceived outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := lsmpl.base 332 + 15296#64)
    (P_mid := (lsLogFilterAddr ↦₆₄ 0#64) ∗ P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (nhrSpills15296 sp w_out) ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      ((fsp + 2320#64) ↦₆₄ w_out.b5.w8) ∗ ((fsp + 2328#64) ↦₆₄ w_out.b5.w9) ∗
      nhrRest1856At fsp w_out ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = outA ∧ s1.pstate = addsPState64 w_out.b0.w0 1#64 ∧
      writebackDoneAt15296 s1 (nhrSpills15296 sp w_out) w_out.b5.w8 w_out.b5.w9 =
        { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4, b5 := w_out.b5,
          q60 := sp.q3c0, w62 := sp.b3.w1 } ∧ TraceCalleeSaved s1 s0) ?_ ?_
  · have hstep1 := nhr_step_8616_ok_15296_placed (ext := ext) s fsp w_out sp
      ((lsLogFilterAddr ↦₆₄ 0#64) ∗ P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2336#64) 400 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hw0_ne_err hpc hrun hsp
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep1 ?_)
    intro s1 Pm _ _ ⟨hPm, hsp1, h1_0, h1_1, h1_2, h1_4, h1_5, h1_6, h1_7, h1_8,
      h1_9, h1_10, h1_11, h1_12, h1_13, h1_14, h1_15, h1_16, h1_17, h1_18, h1_19,
      h1_20, h1_21, h1_22, h1_23, _, _, h1_26, h1_27, _, _, h1_30, hps1, htr1⟩
    have hwb1 := writebackDoneAt15296_of_8616 s1 sp w_out
      h1_0 h1_1 h1_2 h1_4 h1_5 h1_6 h1_7 h1_8 h1_9 h1_10 h1_11 h1_12 h1_13 h1_14 h1_15 h1_16 h1_17 h1_18
      h1_20 h1_21 h1_22 h1_23 h1_26 h1_27 h1_30
    refine ⟨Entails.trans hPm ?_, hsp1, h1_19.trans hx19, hps1, hwb1, htr1.trans htr⟩
    have hsplit := words60At_1856_400_split fsp w_out
    refine Entails.trans (Entails.of_eq (show _ =
      (words60At (fsp + 1856#64) w_out ∗ memRegion (fsp + 2336#64) 400) ∗
      ((lsLogFilterAddr ↦₆₄ 0#64) ∗ P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (nhrSpills15296 sp w_out) ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hsplit) (Entails.of_eq (by ac_rfl))
  · intro s1 hpc1 hrun1 ⟨hsp1, h1_19, hps1, hwb1, htr1⟩
    exact nhr_done_15296_ret_placed hmemcpy_sat s0 s1 outA selfA outSt w_out sp (nhrSpills15296 sp w_out) P_rest
      hsp0_align hw0_ne_none hpc1 hrun1 hsp1 h1_19 hps1 htr1 hwb1

theorem nhr_gt_2180_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s0 s : State) (outA selfA msg_ep : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = lsmpl.base 332 + 2180#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64)
    (hz : s.pstate.z = false) (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 1#32)
    (hx19 : s.readReg64 .x19 = outA) (hx20 : s.readReg64 .x20 = msg_ep) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        chunkedNoHeaderReceivedAt A ((s0.sp - 4240#64) + 2752#64) st ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ nhrUnusedRestAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          memRegion selfA chunkedStatesSize ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  rw [memRegion_out_960_split_err outA, stackAt_statesRecvCallee_eq_dropStack32 fsp]
  wp_pull_exists; rename_i u16 u8 u0
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := lsmpl.base 332 + 19324#64)
    (P_mid := stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
       memRegion selfA chunkedStatesSize ∗ A.pool))
    (Q := fun sm => sm.sp = fsp ∧ TraceCalleeSaved sm s0) ?_ ?_
  · have hstep := nhr_step_2180_gt_19324_placed hdealloc s fsp outA msg_ep u0 u16 u8 st
      (P_rest ∗ memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
       memRegion selfA chunkedStatesSize ∗ memRegion (fsp - 19552#64) 15424 ∗
       sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
       nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0)
      hcl hfsp_align hpc hrun hsp hz hx8 hx19 hx20
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
    intro sm Pm _ _ ⟨hPm, hsp_m, _, htr_m⟩
    refine ⟨Entails.trans hPm ?_, hsp_m, htr_m.trans htr⟩
    have herr := err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA msg_ep
    have hunused := memRegion_nhrUnusedRest_entails_sendEkUnusedAt fsp
    have h4144 := sendEkFrame_entails_memRegion_4144 fsp sp
    rw [stackAt_statesRecvCallee_eq_dropStack32 fsp]
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (fsp + 2752#64) 456 ∗ nhrUnusedRestAt fsp) ∗
      (sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880) ∗
      (memRegion (fsp - 19552#64) 15424 ∗ stackAt fsp dropStack32) ∗ statesRecvSavedCells s0 ∗
      (P_rest ∗ ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_ep) ∗
        memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936) ∗
       memRegion selfA chunkedStatesSize ∗ A.pool) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hunused) ?_
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (fsp - 19552#64) 15424 ∗ stackAt fsp dropStack32) ∗
      (sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp) ∗
      statesRecvSavedCells s0 ∗
      (P_rest ∗ ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_ep) ∗
        memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936) ∗
       memRegion selfA chunkedStatesSize ∗ A.pool) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono h4144 (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left herr))))
  · intro sm hpcm hrunm ⟨hsp_m, htr_m⟩
    refine SepWP.mono
      (states_recv_epilogue_19324_placed s0 sm
        (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
         memRegion selfA chunkedStatesSize ∗ A.pool)
        hsp0_align hpcm hrunm hsp_m htr_m)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

theorem nhr_err_8616_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA : BitVec 64) (err : Error)
    (sp : SendEkSpills) (P_rest : SepProp) (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = lsmpl.base 332 + 8616#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64)
    (hx19 : s.readReg64 .x19 = outA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        noHeaderReceivedRecvChunkResultAt A (F := F) ((s0.sp - 4240#64) + 1856#64) (.error (.err err)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 2336#64) 400 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err err)) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono (memRegion_out_960_split_4words outA)
    (sepConj_mono_right (sepConj_mono_left (nhr_err_1856_split (A := A) (F := F) fsp err))))) ?_
  wp_pull_exists; rename_i w1 w2 w3 o0 o1 o2 o3
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜∃ bs : List (BitVec 8), bs.length = 7 ∧ spqrErrorByte err :: bs = unpack64 w1⌝ ∗
    (P_rest ∗ ((outA ↦₆₄ o0) ∗ ((outA + 8#64) ↦₆₄ o1) ∗ ((outA + 16#64) ↦₆₄ o2) ∗ ((outA + 24#64) ↦₆₄ o3) ∗
      memRegion (outA + 32#64) 928) ∗ memRegion selfA chunkedStatesSize ∗
     (((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
      ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗ memRegion (fsp + 1888#64) 448) ∗
     stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
     memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2336#64) 400 ∗ sendEkUnusedAt fsp ∗
     statesRecvSavedCells s0) by ac_rfl)) ?_
  refine SepWP.pure_elim fun hw1 => ?_
  rw [sendEkSpillsAt_split_w61 fsp sp]
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := lsmpl.base 332 + 19324#64)
    (P_mid := stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err err)) ∗ memRegion selfA chunkedStatesSize))
    (Q := fun sm => sm.sp = fsp ∧ TraceCalleeSaved sm s0) ?_ ?_
  · have hstep := nhr_step_8616_err_19324_placed (ext := ext) s fsp outA w1 w2 w3 sp.w61 o0 o1 o2 o3
      (P_rest ∗ memRegion (outA + 32#64) 928 ∗ memRegion selfA chunkedStatesSize ∗
       memRegion (fsp + 1888#64) 448 ∗ stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsRestAt fsp sp ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       memRegion (fsp + 2336#64) 400 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp hx19
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
    intro sm Pm _ _ ⟨hPm, hsp_m, _, htr_m⟩
    refine ⟨Entails.trans hPm ?_, hsp_m, htr_m.trans htr⟩
    have hout := nhr_err_out_recompose A (F := F) outA err w1 w2 w3 hw1
    have h880 := nhr_err_1856_rejoin_880 fsp 0xfffffffffffffffe#64 w1 w2 w3
    have h4144 := sendEkFrame_entails_memRegion_4144 fsp { sp with w61 := w3 }
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 496#64) ↦₆₄ w3) ∗ sendEkSpillsRestAt fsp sp) ∗
      (((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
       ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗
       memRegion (fsp + 1888#64) 448 ∗ memRegion (fsp + 2336#64) 400) ∗
      (memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗ sendEkUnusedAt fsp) ∗
      stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
      (P_rest ∗ ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₆₄ w1) ∗ ((outA + 16#64) ↦₆₄ w2) ∗ ((outA + 24#64) ↦₆₄ w3) ∗
        memRegion (outA + 32#64) 928) ∗ memRegion selfA chunkedStatesSize) by ac_rfl)) ?_
    rw [sendEkSpillsAt_rejoin_w61 fsp sp w3]
    refine Entails.trans (sepConj_mono_right (sepConj_mono h880 (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hout))))))) ?_
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt fsp statesRecvCalleeStackX ∗
      (sendEkSpillsAt fsp { sp with w61 := w3 } ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp) ∗
      statesRecvSavedCells s0 ∗
      (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err err)) ∗ memRegion selfA chunkedStatesSize) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left h4144)
  · intro sm hpcm hrunm ⟨hsp_m, htr_m⟩
    refine SepWP.mono
      (states_recv_epilogue_19324_placed s0 sm
        (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err err)) ∗ memRegion selfA chunkedStatesSize)
        hsp0_align hpcm hrunm hsp_m htr_m)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

end CryptoVerification.SpqrV1.States.Recv
