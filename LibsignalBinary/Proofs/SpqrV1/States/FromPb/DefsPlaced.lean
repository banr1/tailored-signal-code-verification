/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DecodesPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb` (Block `333`): Relocatable Specifications & Prologue/Epilogue

Defines `[LibsignalPlacement]` specifications (`statesFromPbPlacedSpec*`, `StatesFromPbPlacedOk*`)
and proves the relocatable Block `333` prologue (`+0 -> +36`), epilogue (`+64 -> s0.lr`), and
`None`-variant error path.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_333
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Relocatable `[LibsignalPlacement]` Specifications for `<States>::from_pb` (Block `333`) -/

/-- `<PolyDecoder>::from_pb` (Block `376`) meets `withLsCodeLoaded lsmpl (decoderFromPbSpec A)` on `lsProg_333 (Rust.withPanics ext)`. -/
def DecoderFromPbPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_333 (Rust.withPanics ext))
    (lsmpl.base 376)
    (withLsCodeLoaded lsmpl (decoderFromPbSpec A))

/-- Relocatable specification of `<spqr::v1::chunked::states::States>::from_pb` (Block `333`, 2,911 insns). -/
def statesFromPbPlacedSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) : Spec StatesFromPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbA ∧ v1StatePtsBound x.pb⌝ ∗
      memRegion x.out chunkedStatesSize ∗
      optProtoInnerStateAt A x.pbA x.pb.innerState ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp statesFromPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultChunkedStatesAt A (F := F) x.out (States.from_pb spqrPolyApi (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA optProtoInnerStateSize ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp statesFromPbStack
  onPanic := fun _ s0 sf => statesFromPbOnPanic s0 sf

/-- Per-variant relocatable specification of `<States>::from_pb` (Block `333`) for a fixed `pb : V1State`. -/
def statesFromPbVariantPlacedSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (pb : V1State) : Spec (BitVec 64 × BitVec 64) where
  pre := fun ⟨out, pbA⟩ s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = pbA ∧ v1StatePtsBound pb⌝ ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A pbA pb.innerState ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp statesFromPbStack
  post := fun ⟨out, pbA⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultChunkedStatesAt A (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
      memRegion pbA optProtoInnerStateSize ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp statesFromPbStack
  onPanic := fun _ s0 sf => statesFromPbOnPanic s0 sf

/-- Extended-stack relocatable variant of `statesFromPbPlacedSpec`. -/
def statesFromPbPlacedSpecX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) : Spec StatesFromPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbA ∧ v1StatePtsBound x.pb⌝ ∗
      memRegion x.out chunkedStatesSize ∗
      optProtoInnerStateAt A x.pbA x.pb.innerState ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp statesFromPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultChunkedStatesAt A (F := F) x.out (States.from_pb spqrPolyApi (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA optProtoInnerStateSize ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp statesFromPbStackX
  onPanic := fun _ s0 sf => statesFromPbOnPanic s0 sf

/-- `<States>::from_pb` (Block `333`) meets `withLsCodeLoaded lsmpl (statesFromPbPlacedSpec A F)` on `lsProg_333 (Rust.withPanics ext)`. -/
def StatesFromPbPlacedOk [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_333 (Rust.withPanics ext))
    (lsmpl.base 333)
    (withLsCodeLoaded lsmpl (statesFromPbPlacedSpec A F))

/-- `<States>::from_pb` (Block `333`) meets `withLsCodeLoaded lsmpl (statesFromPbPlacedSpecX A F)` on `lsProg_333 (Rust.withPanics ext)`. -/
def StatesFromPbPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_333 (Rust.withPanics ext))
    (lsmpl.base 333)
    (withLsCodeLoaded lsmpl (statesFromPbPlacedSpecX A F))

/-- `<States>::from_pb` (Block `333`) meets `withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX A F)` on
    `libsignalSessionLib.blockProgram lsmpl 333 (Rust.withPanics ext)`. -/
def StatesFromPbPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 333 (Rust.withPanics ext))
    (lsmpl.base 333)
    (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX A F))

/-! ## 2. Relocatable Prologue (`+0 -> +36`), Epilogue (`+64 -> +92`), and `None` Path (Block `333`) -/

/-- Relocatable prologue (`+0 -> +36` in Block `333`):
    saves `x19..x30` at `s0.sp - 96`, sets `x29 = s0.sp - 96` and `sp = s0.sp - 2400`,
    and stores `0#64` at `[sp, #0]`. -/
theorem states_from_pb_prologue_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 : State) (out pbA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = lsmpl.base 333)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = out)
    (hx0 : s0.readReg64 .x0 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 36#64) s0
      (stackAt s0.sp statesFromPbStack ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
          memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
          statesFromPbSavedCells s0 ∗ Rest) ∧
        s1.sp = s0.sp - 2400#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x8 = out ∧
        s1.readReg64 .x0 = pbA ∧
        TraceCalleeSaved s1 s0) := by
  change s0.pc = (blkPl_333).base at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 36#64) s0 _ _
  rw [stackAt_statesFromPb_split_96 s0.sp, stackAt_statesFromPb_split_fsp s0.sp,
      memRegion_2304_split_cell0 (s0.sp - 2400#64)]
  cells_unfold
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w0
  apply ProofLib.SepWP.exists_left; intro w1
  apply ProofLib.SepWP.exists_left; intro w2
  apply ProofLib.SepWP.exists_left; intro w3
  apply ProofLib.SepWP.exists_left; intro w4
  apply ProofLib.SepWP.exists_left; intro w5
  apply ProofLib.SepWP.exists_left; intro w6
  apply ProofLib.SepWP.exists_left; intro w7
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w9
  apply ProofLib.SepWP.exists_left; intro w10
  apply ProofLib.SepWP.exists_left; intro w11
  apply ProofLib.SepWP.exists_left; intro v_fsp0
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · unfold statesFromPbSavedCells
    exact Entails.of_eq (by ac_rfl)
  · wp_done

/-- Relocatable epilogue (`+64 -> s0.lr` in Block `333`):
    adds `2304` to `sp`, restores `x19..x30` from `s0.sp - 96`, and executes `ret`. -/
theorem states_from_pb_epilogue_64_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp statesFromPbStack ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  change s.pc = (blkPl_333).base + 64#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) (s0.readReg64 .x30) s _ _
  unfold statesFromPbSavedCells
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hrest := stack_restore_statesFromPb s0
    unfold statesFromPbSavedCells at hrest
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 2304 ∗
         (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗ Rest by ac_rfl))
      (sepConj_mono_left hrest)
  · wp_done

/-- Relocatable `None` error path (`+36 -> s0.lr` in Block `333`):
    when `pb.innerState = none`, `[pbA] = none2Cap` (`-2`), so `cmn x9, #2` is equal and
    `+52..+60` writes `Err(Error::StateDecode)` (`noneCap` at `[out]`, `0#8` at `[out + 8]`)
    and returns via `+64..+92`. -/
theorem states_from_pb_none_step_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htrace1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA none ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := none }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htrace1 with ⟨htrace1, hvregs1⟩
  have hnone_pb : optProtoInnerStateAt A pbA none =
      ((pbA ↦₆₄ none2Cap) ∗ memRegion (pbA + 8#64) 216) := rfl
  rw [hnone_pb, memRegion_out_928_split_err out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro b_out8
  apply ProofLib.SepWP.exists_left; intro v_out0
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 64#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (resultChunkedStatesAt A (F := F) out
        (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := none }) ∗
       memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool))
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s1.pc = (blkPl_333).base + 36#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 64#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [States.from_pb, resultChunkedStatesAt, spqrErrorByte, optProtoInnerStateSize]
      have hpb : (pbA ↦₆₄ none2Cap) ∗ memRegion (pbA + 8#64) 216 ⊢ memRegion pbA 224 := by
        rw [ProofLib.memRegion_split pbA 8 216 (by decide)]
        exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion pbA none2Cap)
      have hfsp := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
          ((pbA ↦₆₄ none2Cap) ∗ memRegion (pbA + 8#64) 216) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ 18446744073709551615#64) ∗
           ((out + 8#64) ↦₈ 0#8) ∗
           memRegion (out + 9#64) 919 ∗
           statesFromPbJumpTablePlacedAt ∗
           A.pool) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hfsp (sepConj_mono_left hpb)) ?_
      unfold noneCap
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, htr2⟩
    have hep := states_from_pb_epilogue_64_placed (ext := ext) s0 s2
      (resultChunkedStatesAt A (F := F) out
        (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := none }) ∗
       memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool)
      hsp0_align hpc2 hrun2 hsp2 htr2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-- Convert a clean exit `SepWP` to `s0.readReg64 .x30` into a `SepWPp` for `statesFromPbVariantPlacedSpec`. -/
theorem sepWPp_of_states_exit_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 s : State) (out pbA : BitVec 64) (pb : V1State)
    (P R : SepProp)
    (h : SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesFromPbVariantPlacedSpec A F pb).post (out, pbA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesFromPbVariantPlacedSpec A F pb).onPanic (out, pbA) s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨hPf, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [statesFromPbVariantPlacedSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨htrf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by ac_rfl))) hmem_f⟩

/-- Convert a clean exit `SepWP` to `s0.readReg64 .x30` into a `SepWPp` for `withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F pb)`. -/
theorem sepWPp_of_states_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 s : State) (out pbA : BitVec 64) (pb : V1State)
    (P R : SepProp)
    (h : SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F pb)).post (out, pbA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F pb)).onPanic (out, pbA) s0 sf ∗ R)) :=
  sepWPp_of_states_exit_placed s0 s out pbA pb P R h

/-- `subroutine_ok` for the `None` variant (`pb = { innerState := none }`) with `statesFromPbVariantPlacedSpec`. -/
theorem states_from_pb_none_placed_ok_raw [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (statesFromPbVariantPlacedSpec A F { innerState := none }) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [statesFromPbVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, _⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A pbA none ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_from_pb_prologue_placed (ext := ext) s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A pbA none ∗
     statesFromPbJumpTablePlacedAt ∗
     A.pool)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWPp_seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, _, hx8_1, hx0_1, htr1⟩
  have hnone := states_from_pb_none_step_placed (A := A) (F := F) (ext := ext) s0 s1 out pbA
    hsp0_align hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  exact sepWPp_of_states_exit_placed s0 s1 out pbA { innerState := none } _ R hnone

/-- `subroutine_ok` for the `None` variant (`pb = { innerState := none }`) with `withLsCodeLoaded`. -/
theorem states_from_pb_none_placed_ok_ext [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F { innerState := none })) :=
  subroutine_ok_withLsCodeLoaded_of_plain states_from_pb_none_placed_ok_raw

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  DecoderFromPbPlacedOkExt
  statesFromPbPlacedSpec
  statesFromPbVariantPlacedSpec
  statesFromPbPlacedSpecX
  StatesFromPbPlacedOk
  StatesFromPbPlacedOkExt
  StatesFromPbPlacedOkX
  states_from_pb_prologue_placed
  states_from_pb_epilogue_64_placed
  states_from_pb_none_step_placed
  sepWPp_of_states_exit_placed
  sepWPp_of_states_exit_cl_placed
  states_from_pb_none_placed_ok_raw
  states_from_pb_none_placed_ok_ext
)
end CryptoVerification.SpqrV1.States.FromPb
