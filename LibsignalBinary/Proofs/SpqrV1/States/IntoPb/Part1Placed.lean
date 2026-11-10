/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 1 Placed: Arm 0 (`States.keysUnsampled`) & Call Helpers

Relocatable (`[LibsignalPlacement]`) proof of Arm 0 (`States.keysUnsampled`) and `SepWPp` call
helpers for `<PolyEncoder>::into_pb` (Block `375`) and `<PolyDecoder>::into_pb` (Block `377`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States.IntoPb.Placed

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
attribute [local arm64_norm, local wp_norm]
  sp_sub_96_sub_208 sp_sub_96_sub_192 sp_sub_96_sub_176 sp_sub_96_sub_168 sp_sub_480_add_200

/-! ## 1. Arm 0: `States.keysUnsampled` (`+0 -> +60 -> +100 -> +1544 -> ret`) -/

theorem states_into_pb_keysUnsampled_arm_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out stA : BitVec 64)
    (s : Chunked.SendEk.KeysUnsampled (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (blkPl_334).base + 60#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1520#64)
    (hx29 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s1.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s1.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s1.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s1.readReg64 .x20 = stA)
    (hx19 : s1.readReg64 .x19 = out)
    (hx8 : s1.readReg64 .x8 = 2#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1512#64) 1416 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 2#64) ∗
       ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion (stA + 64#64) 864 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt ∗
       A.pool)
      (fun sf Pf =>
        (Pf ⊢
          optProtoInnerStateAt A out (States.keysUnsampled (P := spqrPolyApi) s).into_pb.innerState ∗
          memRegion stA chunkedStatesSize ∗
          statesIntoPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt s0.sp statesIntoPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htr1 with ⟨htr1, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have h1416 : memRegion (s0.sp - 1512#64) 1416 =
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      cells (s0.sp - 304#64) 6 ∗
      memRegion (s0.sp - 256#64) 160 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1512#64) (n := 152) (k := 1264)
          (b' := s0.sp - 1360#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 880) (k := 384)
          (b' := s0.sp - 480#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 176) (k := 208)
          (b' := s0.sp - 304#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 304#64) (n := 48) (k := 160)
          (b' := s0.sp - 256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1512#64) 19 (by decide),
        ProofLib.memRegion_cells (s0.sp - 304#64) 6 (by decide)]
  rw [h1416]
  cells_unfold
  wp_pull_exists
  rename_i u0 u1 u2 u3 u4 u5
    w200 w208 w216 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
  have hstep1 : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 1544#64) s1
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 1512#64) ↦₆₄ w200) ∗ ((s0.sp - 1504#64) ↦₆₄ w208) ∗
       ((s0.sp - 1496#64) ↦₆₄ w216) ∗ ((s0.sp - 1488#64) ↦₆₄ w64) ∗
       ((s0.sp - 1480#64) ↦₆₄ w72) ∗ ((s0.sp - 1472#64) ↦₆₄ w80) ∗
       ((s0.sp - 1464#64) ↦₆₄ w88) ∗ ((s0.sp - 1456#64) ↦₆₄ w96) ∗
       ((s0.sp - 1448#64) ↦₆₄ w104) ∗ ((s0.sp - 1440#64) ↦₆₄ w112) ∗
       ((s0.sp - 1432#64) ↦₆₄ w120) ∗ ((s0.sp - 1424#64) ↦₆₄ w128) ∗
       ((s0.sp - 1416#64) ↦₆₄ w136) ∗ ((s0.sp - 1408#64) ↦₆₄ w144) ∗
       ((s0.sp - 1400#64) ↦₆₄ w152) ∗ ((s0.sp - 1392#64) ↦₆₄ w160) ∗
       ((s0.sp - 1384#64) ↦₆₄ w168) ∗ ((s0.sp - 1376#64) ↦₆₄ w176) ∗
       ((s0.sp - 1368#64) ↦₆₄ w184) ∗
       memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       ((s0.sp - 304#64) ↦₆₄ u0) ∗ ((s0.sp - 296#64) ↦₆₄ u1) ∗
       ((s0.sp - 288#64) ↦₆₄ u2) ∗ ((s0.sp - 280#64) ↦₆₄ u3) ∗
       ((s0.sp - 272#64) ↦₆₄ u4) ∗ ((s0.sp - 264#64) ↦₆₄ u5) ∗
       memRegion (s0.sp - 256#64) 160 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 2#64) ∗
       ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion (stA + 64#64) 864 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt ∗
       A.pool)
      (fun s2 P2 =>
        (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          epilogueStagingCells s0.sp
            a0 a1 a2 a3 a4 a5
            w64 w72 w80 w88 w96 w104 w112 w120
            w128 w136 w144 w152 w160 w168 w176 w184
            0#64 w200 w208 w216 ∗
          memRegion (s0.sp - 1360#64) 880 ∗
          memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗
          statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗
          (authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           ((stA ↦₆₄ 2#64) ∗
            ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
            ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
            ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
            ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
            memRegion (stA + 64#64) 864) ∗
           statesIntoPbJumpTablePlacedAt ∗ A.pool)) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = 0x8000000000000000#64 ∧
        s2.readReg64 .x21 = s.uc.epoch ∧
        TraceCalleeSaved s2 s0) := by
    dsimp only [statesIntoPbJumpTablePlacedAt, statesIntoPbJumpTableBytes,
      epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    wp_steps
    refine Drop.align_pre (by ac_rfl) ?_
    wp_done
  refine Drop.seq_clean hstep1 fun s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx22_2, hx21_2, htr2⟩ => ?_
  have hep := states_into_pb_epilogue_placed (ext := ext) s0 s2 out
    a0 a1 a2 a3 a4 a5
    w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184
    0#64 w200 w208 w216
    (authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     ((stA ↦₆₄ 2#64) ∗
      ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (stA + 64#64) 864) ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool)
    hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
  rw [hx22_2, hx21_2] at hep
  refine SepWP.strengthen_entails_const ?_ hep
  have hout := outWords28_entails_keysUnsampled A out a0 a1 a2 a3 a4 a5
    w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184
    0#64 w200 w208 w216 s
  have hstA := stA_words8_and_864_entails_928 stA 2#64 a0 a1 a2 a3 a4 a5 s.uc.epoch
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
      0x8000000000000000#64
      a0 a1 a2 a3 a4 a5
      s.uc.epoch
      w64 w72 w80 w88 w96 w104 w112 w120
      w128 w136 w144 w152 w160 w168 w176 w184
      0#64 w200 w208 w216 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
    ((stA ↦₆₄ 2#64) ∗
     ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
     ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
     ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (stA + 64#64) 864) ∗
    statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack by ac_rfl)) ?_
  exact sepConj_mono hout (sepConj_mono_left hstA)

theorem states_into_pb_keysUnsampled_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpec A F (.keysUnsampled s)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.keysUnsampled s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_placed s0 s0 out stA (.keysUnsampled s) _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (chunkedKeysUnsampled_expose A stA s))) ?_
  wp_pull_exists
  rename_i a0 a1 a2 a3 a4 a5
  have hpro := states_into_pb_prologue_60_placed (ext := ext) s0 out stA 2#64
    (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
     ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
     ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 64#64) 864 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (Drop.seq_clean hpro fun s1 hpc1 hrun1
      ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩ => ?_)
  exact states_into_pb_keysUnsampled_arm_placed s0 s1 out stA s a0 a1 a2 a3 a4 a5
    hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1

/-! ## 2. Shared `SepWPp` Sequencing and `encoderIntoPb` / `decoderIntoPb` Call Helpers -/

/-- Return postcondition of `<States>::into_pb` (Block `334`) for `SepWPp`. -/
def StatesIntoPbPlacedPost [LibsignalPlacement] (A : RustAlloc) {F : ShaCompress}
    (s0 : State) (out stA : BitVec 64)
    (st : States spqrPolyApi (spqrAuthApi F)) : State → SepProp → Prop :=
  fun sf Pf =>
    (Pf ⊢
      optProtoInnerStateAt A out st.into_pb.innerState ∗
      memRegion stA chunkedStatesSize ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStack) ∧
    sf.sp = s0.sp ∧
    CalleeSavedPreserved s0 sf ∧
    sf.trace = s0.trace

abbrev StatesIntoPbPostPlaced [LibsignalPlacement] (A : RustAlloc) {F : ShaCompress}
    (s0 : State) (out stA : BitVec 64)
    (st : States spqrPolyApi (spqrAuthApi F)) : State → SepProp → Prop :=
  StatesIntoPbPlacedPost A s0 out stA st

abbrev statesIntoPb_seq_sepWP_placed := @statesIntoPb_seq_sepWP

/-- Bridge from `SepWPp` with `StatesIntoPbPlacedPost` / `StatesIntoPbPanic` to the `subroutine_ok_of_sepWPp`
    goal for `statesIntoPbVariantPlacedSpec`. -/
theorem sepWPp_of_states_into_pb_wpp_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64)
    (st : States spqrPolyApi (spqrAuthApi F))
    (P R : SepProp)
    (hwpp : SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (StatesIntoPbPlacedPost A s0 out stA st)
      (StatesIntoPbPanic s0 R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantPlacedSpec A F st).post ⟨out, stA⟩ s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantPlacedSpec A F st).onPanic ⟨out, stA⟩ s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hent, hspf, hcsf, htrf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR
    dsimp only [statesIntoPbVariantPlacedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrf, ?_⟩
    have hm' := Satisfies.mono (sepConj_mono_left hent) hmR
    simpa [sepConj_assoc] using hm'
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, ?_⟩)⟩
    intro hmR
    dsimp only [statesIntoPbVariantPlacedSpec, statesIntoPbOnPanic]
    simpa [sepConj_assoc] using hqp hmR
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- Call `<PolyEncoder>::into_pb` (Block `375`, `lsmpl.base 375`) inside `SepWPp`, automatically exposing the
    resulting `protoPolynomialEncoderAt A outEncA enc.intoPb` into 7 words `e0..e6` and
    `protoPolynomialEncoderHeap`. -/
theorem call_encoderIntoPb_expose_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375)
      (encoderIntoPbSpec A))
    (outEncA encA : BitVec 64) (enc : PolyEncoder)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 375)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outEncA)
    (hx1 : s.readReg64 .x1 = encA)
    (hsplit : P = (memRegion outEncA protoPolynomialEncoderSize ∗
      polyEncoderAt A encA enc ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
          ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
          ((outEncA + 48#64) ↦₆₄ e6) ∗
          protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      Q (StatesIntoPbPanic s0 R) := by
  refine SepWPp.call henc_raw (x := ⟨outEncA, encA, enc⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [encoderIntoPbSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1⟩, hm⟩
  · change (sf.mem ⊨ ((encoderIntoPbSpec A).onPanic ⟨outEncA, encA, enc⟩ s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem
    dsimp only [encoderIntoPbSpec] at hmem
    rw [← sepConj_assoc]
    have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by
        unfold allocFailedIn at haf ⊢
        rw [htrace.1] at haf htr_sub
        exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [encoderIntoPbSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hexp :
        (protoPolynomialEncoderAt A outEncA enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame ⊢
        ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64, ∃∗ e6 : BitVec 64,
          (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
            ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
            ((outEncA + 48#64) ↦₆₄ e6) ∗
            protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
            memRegion encA polyEncoderSize ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame) := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_left (protoPolynomialEncoder_expose A outEncA enc.intoPb))) ?_
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro e0
      apply Entails.sepExists_elim; intro e1
      apply Entails.sepExists_elim; intro e2
      apply Entails.sepExists_elim; intro e3
      apply Entails.sepExists_elim; intro e4
      apply Entails.sepExists_elim; intro e5
      apply Entails.sepExists_elim; intro e6
      refine Entails.sepExists_right e0 (Entails.sepExists_right e1
        (Entails.sepExists_right e2 (Entails.sepExists_right e3
          (Entails.sepExists_right e4 (Entails.sepExists_right e5
            (Entails.sepExists_right e6 ?_))))))
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hexp ?_
    refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 =>
      SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
      SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 =>
      SepWPp.exists_elim fun e6 => ?_
    exact hnext sf e0 e1 e2 e3 e4 e5 e6 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

/-- Call `<PolyDecoder>::into_pb` (Block `377`, `lsmpl.base 377`) inside `SepWPp`, automatically splitting/restoring
    `stackAt (s0.sp - 1520#64) encoderIntoPbStack` and exposing the resulting
    `protoPolynomialDecoderAt A outDecA dec.intoPb` into 5 words `d0..d4` and
    `protoPolynomialDecoderHeap`. -/
theorem call_decoderIntoPb_expose_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377)
      (decoderIntoPbSpec A))
    (outDecA decA : BitVec 64) (dec : PolyDecoder)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 377)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outDecA)
    (hx1 : s.readReg64 .x1 = decA)
    (hsplit : P = (memRegion outDecA protoPolynomialDecoderSize ∗
      polyDecoderAt A decA dec ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (d0 d1 d2 d3 d4 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
          ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
          protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      Q (StatesIntoPbPanic s0 R) := by
  refine SepWPp.call hdec_raw (x := ⟨outDecA, decA, dec⟩)
    (F := memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit, stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)] at hm
    dsimp only [decoderIntoPbSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    refine ⟨⟨hx0, hx1⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · change (sf.mem ⊨ ((decoderIntoPbSpec A).onPanic ⟨outDecA, decA, dec⟩ s sf ∗
      (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem
    dsimp only [decoderIntoPbSpec] at hmem
    rw [← sepConj_assoc]
    have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by
        unfold allocFailedIn at haf ⊢
        rw [htrace.1] at haf htr_sub
        exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [decoderIntoPbSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hexp :
        (protoPolynomialDecoderAt A outDecA dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool ∗ stackAt (s0.sp - 1520#64) decoderIntoPbStack) ∗
          (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame) ⊢
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64,
          (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
            ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
            protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 dec.intoPb ∗
            memRegion decA polyDecoderSize ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame) := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_left (protoPolynomialDecoder_expose A outDecA dec.intoPb))) ?_
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro d0
      apply Entails.sepExists_elim; intro d1
      apply Entails.sepExists_elim; intro d2
      apply Entails.sepExists_elim; intro d3
      apply Entails.sepExists_elim; intro d4
      refine Entails.sepExists_right d0 (Entails.sepExists_right d1
        (Entails.sepExists_right d2 (Entails.sepExists_right d3
          (Entails.sepExists_right d4 ?_))))
      rw [stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)]
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hexp ?_
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
      SepWPp.exists_elim fun d4 => ?_
    exact hnext sf d0 d1 d2 d3 d4 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

end CryptoVerification.SpqrV1.States.IntoPb
