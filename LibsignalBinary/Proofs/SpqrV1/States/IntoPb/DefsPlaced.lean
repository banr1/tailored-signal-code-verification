/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.IntoPbCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`): Relocatable Specifications, Prologue, and Epilogue

Relocatable (`[LibsignalPlacement]`) `.rodata` jump-table assertion, subroutine specifications, and
shared prologue (`+0 -> +44 -> +60`) and epilogue (`+1544 -> ret`) for Block `334`.
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

/-! ## 1. `.rodata` Jump Table and Relocatable `[LibsignalPlacement]` Specifications -/

/-- Read-only separation-logic assertion for the 22-byte jump table of `<States>::into_pb` (Block `334`). -/
def statesIntoPbJumpTablePlacedAt [LibsignalPlacement] : SepProp :=
  (lsρ "spqr:.rodata.<spqr::v1::chunked::states::States>::into_pb") ↦ᵣ statesIntoPbJumpTableBytes

theorem lsro_statesIntoPbJumpTablePlacedAt [LibsignalPlacement] {s : State}
    (hro : LibsignalRoLoaded lsmpl s.mem) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesIntoPbJumpTablePlacedAt ∗ P :=
  lsro_intro_chk hro (by decide +kernel) hP

/-- Relocatable specification of `<spqr::v1::chunked::states::States>::into_pb` (Block `334`)
    carrying `statesIntoPbJumpTablePlacedAt` explicitly. -/
def statesIntoPbPlacedSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      chunkedStatesAt A x.stA x.st ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp statesIntoPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      optProtoInnerStateAt A x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStack
  onPanic := fun _ s0 sf => statesIntoPbOnPanic s0 sf

/-- Per-variant relocatable specification of `<States>::into_pb` (Block `334`) for a fixed `st : States`. -/
def statesIntoPbVariantPlacedSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (st : States spqrPolyApi (spqrAuthApi F)) : Spec (BitVec 64 × BitVec 64) where
  pre := fun ⟨out, stA⟩ s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = stA⌝ ∗
      memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA st ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp statesIntoPbStack
  post := fun ⟨out, stA⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      optProtoInnerStateAt A out st.into_pb.innerState ∗
      memRegion stA chunkedStatesSize ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStack
  onPanic := fun _ s0 sf => statesIntoPbOnPanic s0 sf

/-- Extended-stack variant of `statesIntoPbPlacedSpec` (with explicit `statesIntoPbJumpTablePlacedAt`). -/
def statesIntoPbPlacedRoSpecX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      chunkedStatesAt A x.stA x.st ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp statesIntoPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      optProtoInnerStateAt A x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStackX
  onPanic := fun _ s0 sf => statesIntoPbOnPanic s0 sf

/-- Extended-stack relocatable specification of `<States>::into_pb` (Block `334`) where `.rodata`
    is discharged from `LibsignalRoLoaded lsmpl s.mem`. -/
def statesIntoPbPlacedSpecX (A : RustAlloc) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      chunkedStatesAt A x.stA x.st ∗
      A.pool ∗ stackAt s.sp statesIntoPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      optProtoInnerStateAt A x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStackX
  onPanic := fun _ s0 sf => statesIntoPbOnPanic s0 sf

abbrev statesIntoPbPlacedInnerSpecX (A : RustAlloc) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F) :=
  statesIntoPbPlacedSpecX A F

/-- `<States>::into_pb` (Block `334`) meets `statesIntoPbPlacedSpec A F` on
    `(blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)`. -/
def StatesIntoPbPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
    (blkPl_334).base
    (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec A F))

/-- `<States>::into_pb` (Block `334`) meets
    `withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX A F)` on
    `(blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)`. -/
def StatesIntoPbPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
    (blkPl_334).base
    (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX A F))

private theorem satisfies_anyHeap_frame_placed {m : Memory} {P Fr R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ Fr ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ Fr ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (Fr ∗ R), ← sepConj_assoc anyHeap Fr R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ Fr)))
  exact Satisfies.mono h1 h

/-- `statesIntoPbPlacedSpec A F` entails `statesIntoPbPlacedRoSpecX A F` by framing the unused bottom stack region. -/
theorem statesIntoPbPlacedRoSpecX_of_statesIntoPbPlacedSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    (h : subroutine_ok P addr (statesIntoPbPlacedSpec A F)) :
    subroutine_ok P addr (statesIntoPbPlacedRoSpecX A F) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hle : statesIntoPbStack ≤ statesIntoPbStackX := by decide
  have hsplit : stackAt s0.sp statesIntoPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 statesIntoPbStackX)
        (statesIntoPbStackX - statesIntoPbStack) ∗
        stackAt s0.sp statesIntoPbStack := by
    have h1 := stackAt_split_bottom s0.sp statesIntoPbStack
      (statesIntoPbStackX - statesIntoPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 statesIntoPbStackX)
      (statesIntoPbStackX - statesIntoPbStack) ∗ R
  have hpre' : s0.mem ⊨ (statesIntoPbPlacedSpec A F).pre x s0 ∗ R' := by
    dsimp only [statesIntoPbPlacedRoSpecX, statesIntoPbPlacedSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [statesIntoPbPlacedRoSpecX, statesIntoPbPlacedSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame_placed hpost⟩)
  · dsimp only [statesIntoPbPlacedSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-! ## 2. Prologue (`+0 -> +44`), Exit Helper, Extended Prologue (`+0 -> +60`), and Common Epilogue (`+1544 -> ret`) -/

/-- Relocatable prologue (`+0 -> +44` in Block `334`). -/
theorem states_into_pb_prologue_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 : State) (out stA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (blkPl_334).base)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = out)
    (hx0 : s0.readReg64 .x0 = stA) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 44#64) s0
      (stackAt s0.sp statesIntoPbStack ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗ Rest) ∧
        s1.sp = s0.sp - 1520#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x28 = s0.sp - 256#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x0 = stA ∧
        s1.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsplit_1424 : memRegion (s0.sp - 1520#64) 1424 =
      cells (s0.sp - 1520#64) 1 ∗
      memRegion (s0.sp - 1512#64) 1416 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1520#64) (n := 8) (k := 1416)
          (b' := s0.sp - 1512#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1520#64) 1 (by decide)]
  rw [stackAt_statesIntoPb_split_96 s0.sp, stackAt_statesIntoPb_split_fsp s0.sp]
  nth_rw 1 [hsplit_1424]
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre ?_ ?_
  · unfold statesIntoPbSavedCells
    ac_rfl
  · wp_done

/-- Convert a clean exit `SepWP` to `s0.readReg64 .x30` into a `SepWPp` for `statesIntoPbVariantPlacedSpec`. -/
theorem sepWPp_of_states_into_pb_exit_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64) (st : States spqrPolyApi (spqrAuthApi F))
    (P R : SepProp)
    (h : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          optProtoInnerStateAt A out st.into_pb.innerState ∗
          memRegion stA chunkedStatesSize ∗
          statesIntoPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt s0.sp statesIntoPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesIntoPbVariantPlacedSpec A F st).post (out, stA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantPlacedSpec A F st).onPanic (out, stA) s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨hPf, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [statesIntoPbVariantPlacedSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨htrf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by ac_rfl))) hmem_f⟩

/-- Relocatable extended prologue (`+0 -> +60` in Block `334`). -/
theorem states_into_pb_prologue_60_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 : State) (out stA tag : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (blkPl_334).base)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = out)
    (hx0 : s0.readReg64 .x0 = stA) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 60#64) s0
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ tag) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ tag) ∗ Rest) ∧
        s1.sp = s0.sp - 1520#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x28 = s0.sp - 256#64 ∧
        s1.readReg64 .x27 = s0.sp - 1360#64 ∧
        s1.readReg64 .x26 = s0.sp - 480#64 ∧
        s1.readReg64 .x20 = stA ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x8 = tag ∧
        TraceCalleeSaved s1 s0) := by
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsplit_1424 : memRegion (s0.sp - 1520#64) 1424 =
      cells (s0.sp - 1520#64) 1 ∗
      memRegion (s0.sp - 1512#64) 1416 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1520#64) (n := 8) (k := 1416)
          (b' := s0.sp - 1512#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1520#64) 1 (by decide)]
  rw [stackAt_statesIntoPb_split_96 s0.sp, stackAt_statesIntoPb_split_fsp s0.sp]
  nth_rw 1 [hsplit_1424]
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre ?_ ?_
  · unfold statesIntoPbSavedCells
    ac_rfl
  · wp_done

/-- Relocatable common epilogue (`+1544 -> s0.readReg64 .x30` in Block `334`). -/
theorem states_into_pb_epilogue_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64)
    (w8 w16 w24 w32 w40 w48
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 1544#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (htr : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48
         w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184
         w192 w200 w208 w216 ∗
       memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       memRegion (s0.sp - 256#64) 160 ∗
       statesIntoPbSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗
       Rest)
      (fun sf Pf =>
        (Pf ⊢
          outWords28 out
            (s.readReg64 .x22) w8 w16 w24 w32 w40 w48 (s.readReg64 .x21)
            w64 w72 w80 w88 w96 w104 w112 w120
            w128 w136 w144 w152 w160 w168 w176 w184
            w192 w200 w208 w216 ∗
          stackAt s0.sp statesIntoPbStack ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htr with ⟨htr, hvregs⟩
  have hrestore :
      outWords28 out
        (s.readReg64 .x22) w8 w16 w24 w32 w40 w48 (s.readReg64 .x21)
        w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184
        w192 w200 w208 w216 ∗
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       (epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48
          w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184
          w192 w200 w208 w216 ∗
        memRegion (s0.sp - 1360#64) 880 ∗
        memRegion (s0.sp - 480#64) 176 ∗
        memRegion (s0.sp - 256#64) 160) ∗
       statesIntoPbSavedCells s0) ∗
      Rest ⊢
      outWords28 out
        (s.readReg64 .x22) w8 w16 w24 w32 w40 w48 (s.readReg64 .x21)
        w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184
        w192 w200 w208 w216 ∗
      stackAt s0.sp statesIntoPbStack ∗
      Rest := by
    refine sepConj_mono_right (sepConj_mono_left ?_)
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (epilogueStagingCells_entails_memRegion s0.sp
        w8 w16 w24 w32 w40 w48
        w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184
        w192 w200 w208 w216))) ?_
    exact stack_restore_statesIntoPb s0
  refine SepWP.strengthen_entails_const hrestore ?_
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  rw [memRegion_out_224_eq out]
  wp_pull_exists
  dsimp only [outWords28, epilogueStagingCells, statesIntoPbSavedCells]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

end CryptoVerification.SpqrV1.States.IntoPb
