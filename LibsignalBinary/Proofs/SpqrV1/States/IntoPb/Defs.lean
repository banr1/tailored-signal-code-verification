/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Drop.StatesRepr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb`: Specifications, Prologue, and Epilogue

**Checked by Lean.**

Defines the `.rodata` jump-table assertion `statesIntoPbJumpTableAt`, the top-level and per-variant
specifications (`statesIntoPbSpec`, `statesIntoPbVariantSpec`) for
`<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20..0x5d7bc`), and the shared 1520-byte stack
frame prologue (`+0 -> +44 -> +60`) and 224-byte output epilogue (`+1544 -> +1640`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Stack Budgets and Top-Level Specifications (`0x5ce20`) -/

/-- Own stack frame of `<States>::into_pb` (`96 + 1424 = 1520` bytes = `0x5f0`). -/
abbrev statesIntoPbFrame : Nat := 1520

/-- Stack budget of `<States>::into_pb` (`1520 + encoderIntoPbStack = 1776 + allocHookStack`). -/
abbrev statesIntoPbStack : Nat := statesIntoPbFrame + encoderIntoPbStack

/-- Extended-stack budget of `<States>::into_pb` (`1520 + extHookStack`). -/
abbrev statesIntoPbStackX : Nat := statesIntoPbFrame + extHookStack

/-- Ghost arguments of `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20`). -/
structure StatesIntoPbGhost (F : ShaCompress) where
  /-- Indirect return pointer (`x8`, 224-byte `V1State` output). -/
  out : BitVec 64
  /-- Pointer to consumed 928-byte `States` (`x0`). -/
  stA : BitVec 64
  /-- Logical `States` value at `stA`. -/
  st : States spqrPolyApi (spqrAuthApi F)

/-- Panic postcondition of `<States>::into_pb`: heap allocation failure (`allocFailedIn`). -/
def statesIntoPbOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Specification of `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20..0x5d7bc`, 615 insns):
    * Registers: `x8 = out` (224-byte `V1State` indirect result), `x0 = stA` (928-byte `States`).
    * Consumes `chunkedStatesAt A stA st` (leaving `memRegion stA 928`) and writes
      `optProtoInnerStateAt A out st.into_pb.innerState` at `out`,
      or panics with `allocFailedEvent` on heap allocation failure. -/
def statesIntoPbSpec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec (StatesIntoPbGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA ∧
      b &&& 0xfff#64 = 0#64⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      chunkedStatesAt A x.stA x.st ∗
      statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s.sp statesIntoPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      optProtoInnerStateAt A x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStack
  onPanic := fun _ s0 sf => statesIntoPbOnPanic s0 sf

/-- Per-variant specification of `0x5ce20` (`States::into_pb`) for a fixed `st : States`. -/
def statesIntoPbVariantSpec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64)
    (st : States spqrPolyApi (spqrAuthApi F)) : Spec (BitVec 64 × BitVec 64) where
  pre := fun ⟨out, stA⟩ s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = stA ∧
      b &&& 0xfff#64 = 0#64⌝ ∗
      memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA st ∗
      statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s.sp statesIntoPbStack
  post := fun ⟨out, stA⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      optProtoInnerStateAt A out st.into_pb.innerState ∗
      memRegion stA chunkedStatesSize ∗
      statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStack
  onPanic := fun _ s0 sf => statesIntoPbOnPanic s0 sf

/-- Extended-stack variant of `statesIntoPbSpec`. -/
def statesIntoPbSpecX (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec (StatesIntoPbGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA ∧
      b &&& 0xfff#64 = 0#64⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      chunkedStatesAt A x.stA x.st ∗
      statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s.sp statesIntoPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      optProtoInnerStateAt A x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStackX
  onPanic := fun _ s0 sf => statesIntoPbOnPanic s0 sf

/-- `<States>::into_pb` meets `statesIntoPbSpec A F b` on `tripleRatchetProgAtExt b ext`. -/
def StatesIntoPbOkExt (b : BitVec 64) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
    (statesIntoPbSpec A F b)

/-- `<States>::into_pb` meets `(statesIntoPbSpecX A F img.base).inImage img` on
    `tripleRatchetProgAtExt img.base ext`. -/
def StatesIntoPbOkX (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr statesIntoPbName)
    ((statesIntoPbSpecX A F img.base).inImage img)

private theorem satisfies_anyHeap_frame {m : Memory} {P Fr R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ Fr ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ Fr ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (Fr ∗ R), ← sepConj_assoc anyHeap Fr R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ Fr)))
  exact Satisfies.mono h1 h

/-- `statesIntoPbSpec A F b` entails `statesIntoPbSpecX A F b` by framing the unused bottom stack region. -/
theorem statesIntoPbSpecX_of_statesIntoPbSpec {P : Program} {addr b : BitVec 64}
    {A : RustAlloc} {F : ShaCompress}
    (h : subroutine_ok P addr (statesIntoPbSpec A F b)) :
    subroutine_ok P addr (statesIntoPbSpecX A F b) := by
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
  have hpre' : s0.mem ⊨ (statesIntoPbSpec A F b).pre x s0 ∗ R' := by
    dsimp only [statesIntoPbSpecX, statesIntoPbSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [statesIntoPbSpecX, statesIntoPbSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [statesIntoPbSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-! ## 2. Pure Reduction Lemmas for `States.into_pb` and `PolyApi` / `AuthApi` -/

@[simp]
theorem pbToProtoPolyEncoder_encoder_into_pb (enc : PolyEncoder) :
    pbToProtoPolyEncoder (spqrPolyApi.encoder_into_pb enc) = enc.intoPb := rfl

@[simp]
theorem pbToProtoPolyDecoder_decoder_into_pb (dec : PolyDecoder) :
    pbToProtoPolyDecoder (spqrPolyApi.decoder_into_pb dec) = dec.intoPb := rfl

@[simp]
theorem optProtoAuthenticatorAt_some_into_pb (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (auth : (spqrAuthApi F).Authenticator) :
    optProtoAuthenticatorAt A a (some ((spqrAuthApi F).into_pb auth)) =
      authenticatorAt A a auth := rfl

/-! ## 3. Stack Frame and Saved-Register Helpers (`1520`B frame) -/

/-- Saved callee-saved registers at `[s0.sp - 96 .. s0.sp)` (`12` words = `96` bytes):
    `fp, lr, x28, x27, x26, x25, x24, x23, x22, x21, x20, x19`. -/
def statesIntoPbSavedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
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
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem stackAt_statesIntoPb_split_96 (sp : BitVec 64) :
    stackAt sp statesIntoPbStack =
      stackAt (sp - 96#64) (encoderIntoPbStack + 1424) ∗ cells (sp - 96#64) 12 :=
  ProofLib.stackAt_split_cells sp (encoderIntoPbStack + 1424) 12 (by decide)

theorem stackAt_statesIntoPb_split_fsp (sp : BitVec 64) :
    stackAt (sp - 96#64) (encoderIntoPbStack + 1424) =
      stackAt (sp - 1520#64) encoderIntoPbStack ∗ memRegion (sp - 1520#64) 1424 := by
  simp only [stackAt]
  rw [ProofLib.memRegion_split ((sp - 96#64) - BitVec.ofNat 64 (encoderIntoPbStack + 1424))
    encoderIntoPbStack 1424 (by decide)]
  have h1 : (sp - 96#64) - BitVec.ofNat 64 (encoderIntoPbStack + 1424) =
      (sp - 1520#64) - BitVec.ofNat 64 encoderIntoPbStack := by
    change (sp - 96#64) - 5776#64 = (sp - 1520#64) - 4352#64
    bv_omega
  have h2 : (sp - 96#64) - BitVec.ofNat 64 (encoderIntoPbStack + 1424) +
      BitVec.ofNat 64 encoderIntoPbStack = sp - 1520#64 := by
    change (sp - 96#64) - 5776#64 + 4352#64 = sp - 1520#64
    bv_omega
  rw [h2, h1]

theorem stackAt_encoderIntoPb_eq_decoderIntoPb (fsp : BitVec 64) :
    stackAt fsp encoderIntoPbStack =
      memRegion (fsp - 4352#64) 64 ∗ stackAt fsp decoderIntoPbStack :=
  ProofLib.stackAt_split_bottom fsp decoderIntoPbStack 64 (by decide)

theorem stackAt_encoderIntoPb_eq_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderIntoPbStack =
      memRegion (fsp - 4352#64) 256 ∗ stackAt fsp allocHookStack :=
  ProofLib.stackAt_split_bottom fsp allocHookStack 256 (by decide)

theorem statesIntoPbSavedCells_entails_cells12 (s0 : State) :
    statesIntoPbSavedCells s0 ⊢ cells (s0.sp - 96#64) 12 := by
  unfold statesIntoPbSavedCells
  cells_unfold
  exact Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
      (Entails.sepExists_right (s0.readReg64 .x28)
        (Entails.sepExists_right (s0.readReg64 .x27)
          (Entails.sepExists_right (s0.readReg64 .x26)
            (Entails.sepExists_right (s0.readReg64 .x25)
              (Entails.sepExists_right (s0.readReg64 .x24)
                (Entails.sepExists_right (s0.readReg64 .x23)
                  (Entails.sepExists_right (s0.readReg64 .x22)
                    (Entails.sepExists_right (s0.readReg64 .x21)
                      (Entails.sepExists_right (s0.readReg64 .x20)
                        (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))))))

theorem stack_restore_statesIntoPb (s0 : State) :
    stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      memRegion (s0.sp - 1520#64) 1424 ∗
      statesIntoPbSavedCells s0 ⊢
      stackAt s0.sp statesIntoPbStack := by
  rw [stackAt_statesIntoPb_split_96 s0.sp, stackAt_statesIntoPb_split_fsp s0.sp, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (statesIntoPbSavedCells_entails_cells12 s0))

@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_16 (sp : BitVec 64) : (sp - 96#64) + 16#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_32 (sp : BitVec 64) : (sp - 96#64) + 32#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_48 (sp : BitVec 64) : (sp - 96#64) + 48#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_64 (sp : BitVec 64) : (sp - 96#64) + 64#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_80 (sp : BitVec 64) : (sp - 96#64) + 80#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_1424 (sp : BitVec 64) : (sp - 96#64) - 1424#64 = sp - 1520#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_160 (sp : BitVec 64) : (sp - 96#64) - 160#64 = sp - 256#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_1520_add_1424 (sp : BitVec 64) : (sp - 1520#64) + 1424#64 = sp - 96#64 := by bv_omega

/-! ## 4. Prologue (`+0 -> +44`) and Convert-to-`SepWPp` Helper -/

/-- Prologue (`+0 -> +44`, `0x5ce20 -> 0x5ce4c`):
    saves `x19..x30` at `s0.sp - 96`, sets `x29 = s0.sp - 96`, `sp = s0.sp - 1520`,
    stores `0#64` at `[sp]`, sets `x19 = out`, and sets `x28 = s0.sp - 256` (`x29 - 0xa0`). -/
theorem states_into_pb_prologue {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (out stA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = out)
    (hx0 : s0.readReg64 .x0 = stA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 44#64) s0
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
  states_into_pb_fetches_range b (Rust.withPanics ext) 0 44
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
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

/-- Convert a clean exit `SepWP` to `s0.readReg64 .x30` into a `SepWPp` for `statesIntoPbVariantSpec`. -/
theorem sepWPp_of_states_into_pb_exit {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out stA : BitVec 64) (st : States spqrPolyApi (spqrAuthApi F))
    (P R : SepProp)
    (h : SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          optProtoInnerStateAt A out st.into_pb.innerState ∗
          memRegion stA chunkedStatesSize ∗
          statesIntoPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesIntoPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesIntoPbVariantSpec A F b st).post (out, stA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantSpec A F b st).onPanic (out, stA) s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨hPf, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [statesIntoPbVariantSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨htrf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by ac_rfl))) hmem_f⟩

/-! ## 5. Jump Table Expansion, Prologue (`+0 -> +60`), and Common Epilogue (`+1544 -> ret`) -/

/-- Image offset of the 22-byte `.rodata` jump table for `<States>::into_pb` (`0x82444` = `533572`). -/
abbrev statesIntoPbJumpTableOff : Nat := num% (ls_xref% 0x57a74 0x57a78)

theorem statesIntoPbJumpTableBytes_eq_rodata :
    (libsignalSessionImage.data.drop (statesIntoPbJumpTableOff - libsignalSessionImage.dataOff)).take 22 =
      statesIntoPbJumpTableBytes := by
  rfl_kernel

theorem rodata_statesIntoPbJumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesIntoPbJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := statesIntoPbJumpTableOff) (n := 22) (bs := statesIntoPbJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) rfl statesIntoPbJumpTableBytes_eq_rodata
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem memRegion_1416_split (sp : BitVec 64) :
    memRegion (sp - 1512#64) 1416 =
      cells (sp - 1512#64) 19 ∗
      memRegion (sp - 1360#64) 880 ∗
      memRegion (sp - 480#64) 176 ∗
      cells (sp - 304#64) 6 ∗
      cells (sp - 256#64) 20 := by
  rw [ProofLib.memRegion_split' (b := sp - 1512#64) (n := 152) (k := 1264)
        (b' := sp - 1360#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1360#64) (n := 880) (k := 384)
        (b' := sp - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 480#64) (n := 176) (k := 208)
        (b' := sp - 304#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 304#64) (n := 48) (k := 160)
        (b' := sp - 256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 1512#64) 19 (by decide),
      ProofLib.memRegion_cells (sp - 304#64) 6 (by decide),
      ProofLib.memRegion_cells (sp - 256#64) 20 (by decide)]

/-- Combined trace and callee-saved SIMD register preservation from `s0` to `s`. -/
abbrev TraceCalleeSaved (s s0 : State) : Prop :=
  s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

/-- Extended prologue (`+0 -> +60`, `0x5ce20 -> 0x5ce5c`):
    saves `x19..x30`, allocates 1424B stack frame, stores `0#64` at `[sp]`,
    loads `x8 = tag` from `stA`, and initializes
    `x19 = out`, `x20 = stA`, `x26 = s0.sp - 480`, `x27 = s0.sp - 1360`, `x28 = s0.sp - 256`, `x29 = s0.sp - 96`. -/
theorem states_into_pb_prologue_60 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (out stA tag : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = out)
    (hx0 : s0.readReg64 .x0 = stA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 60#64) s0
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
  states_into_pb_fetches_range b (Rust.withPanics ext) 0 60
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
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

/-- The 28 64-bit words (`224` bytes) of `out` written by the common epilogue (`+1544 -> +1640`). -/
def outWords28 (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64) : SepProp :=
  (out ↦₆₄ w0) ∗
  ((out + 8#64) ↦₆₄ w8) ∗ ((out + 16#64) ↦₆₄ w16) ∗
  ((out + 24#64) ↦₆₄ w24) ∗ ((out + 32#64) ↦₆₄ w32) ∗
  ((out + 40#64) ↦₆₄ w40) ∗ ((out + 48#64) ↦₆₄ w48) ∗
  ((out + 56#64) ↦₆₄ w56) ∗
  ((out + 64#64) ↦₆₄ w64) ∗ ((out + 72#64) ↦₆₄ w72) ∗
  ((out + 80#64) ↦₆₄ w80) ∗ ((out + 88#64) ↦₆₄ w88) ∗
  ((out + 96#64) ↦₆₄ w96) ∗ ((out + 104#64) ↦₆₄ w104) ∗
  ((out + 112#64) ↦₆₄ w112) ∗ ((out + 120#64) ↦₆₄ w120) ∗
  ((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗
  ((out + 144#64) ↦₆₄ w144) ∗ ((out + 152#64) ↦₆₄ w152) ∗
  ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗
  ((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
  ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
  ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216)

/-- Stack staging cells read by the common epilogue (`+1544 -> +1640`):
    * `[s0.sp - 304 .. s0.sp - 256)` (`6` words -> `out + 8 .. out + 48`)
    * `[s0.sp - 1520 .. s0.sp - 1488)` (`4` words -> `out + 192 .. out + 216`)
    * `[s0.sp - 1488 .. s0.sp - 1360)` (`16` words -> `out + 64 .. out + 184`) -/
def epilogueStagingCells (sp : BitVec 64)
    (w8 w16 w24 w32 w40 w48
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64) : SepProp :=
  ((sp - 304#64) ↦₆₄ w8) ∗ ((sp - 296#64) ↦₆₄ w16) ∗
  ((sp - 288#64) ↦₆₄ w24) ∗ ((sp - 280#64) ↦₆₄ w32) ∗
  ((sp - 272#64) ↦₆₄ w40) ∗ ((sp - 264#64) ↦₆₄ w48) ∗
  ((sp - 1520#64) ↦₆₄ w192) ∗ ((sp - 1512#64) ↦₆₄ w200) ∗
  ((sp - 1504#64) ↦₆₄ w208) ∗ ((sp - 1496#64) ↦₆₄ w216) ∗
  ((sp - 1488#64) ↦₆₄ w64) ∗ ((sp - 1480#64) ↦₆₄ w72) ∗
  ((sp - 1472#64) ↦₆₄ w80) ∗ ((sp - 1464#64) ↦₆₄ w88) ∗
  ((sp - 1456#64) ↦₆₄ w96) ∗ ((sp - 1448#64) ↦₆₄ w104) ∗
  ((sp - 1440#64) ↦₆₄ w112) ∗ ((sp - 1432#64) ↦₆₄ w120) ∗
  ((sp - 1424#64) ↦₆₄ w128) ∗ ((sp - 1416#64) ↦₆₄ w136) ∗
  ((sp - 1408#64) ↦₆₄ w144) ∗ ((sp - 1400#64) ↦₆₄ w152) ∗
  ((sp - 1392#64) ↦₆₄ w160) ∗ ((sp - 1384#64) ↦₆₄ w168) ∗
  ((sp - 1376#64) ↦₆₄ w176) ∗ ((sp - 1368#64) ↦₆₄ w184)

theorem epilogueStagingCells_entails_memRegion (sp : BitVec 64)
    (w8 w16 w24 w32 w40 w48
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64) :
    epilogueStagingCells sp
      w8 w16 w24 w32 w40 w48
      w64 w72 w80 w88 w96 w104 w112 w120
      w128 w136 w144 w152 w160 w168 w176 w184
      w192 w200 w208 w216 ∗
    memRegion (sp - 1360#64) 880 ∗
    memRegion (sp - 480#64) 176 ∗
    memRegion (sp - 256#64) 160 ⊢
    memRegion (sp - 1520#64) 1424 := by
  have hc20 :
      ((sp - 1520#64) ↦₆₄ w192) ∗ ((sp - 1512#64) ↦₆₄ w200) ∗
      ((sp - 1504#64) ↦₆₄ w208) ∗ ((sp - 1496#64) ↦₆₄ w216) ∗
      ((sp - 1488#64) ↦₆₄ w64) ∗ ((sp - 1480#64) ↦₆₄ w72) ∗
      ((sp - 1472#64) ↦₆₄ w80) ∗ ((sp - 1464#64) ↦₆₄ w88) ∗
      ((sp - 1456#64) ↦₆₄ w96) ∗ ((sp - 1448#64) ↦₆₄ w104) ∗
      ((sp - 1440#64) ↦₆₄ w112) ∗ ((sp - 1432#64) ↦₆₄ w120) ∗
      ((sp - 1424#64) ↦₆₄ w128) ∗ ((sp - 1416#64) ↦₆₄ w136) ∗
      ((sp - 1408#64) ↦₆₄ w144) ∗ ((sp - 1400#64) ↦₆₄ w152) ∗
      ((sp - 1392#64) ↦₆₄ w160) ∗ ((sp - 1384#64) ↦₆₄ w168) ∗
      ((sp - 1376#64) ↦₆₄ w176) ∗ ((sp - 1368#64) ↦₆₄ w184) ⊢
      memRegion (sp - 1520#64) 160 := by
    rw [ProofLib.memRegion_cells (sp - 1520#64) 20 (by decide)]
    cells_unfold
    exact Entails.sepExists_right w192 (Entails.sepExists_right w200
      (Entails.sepExists_right w208 (Entails.sepExists_right w216
        (Entails.sepExists_right w64 (Entails.sepExists_right w72
          (Entails.sepExists_right w80 (Entails.sepExists_right w88
            (Entails.sepExists_right w96 (Entails.sepExists_right w104
              (Entails.sepExists_right w112 (Entails.sepExists_right w120
                (Entails.sepExists_right w128 (Entails.sepExists_right w136
                  (Entails.sepExists_right w144 (Entails.sepExists_right w152
                    (Entails.sepExists_right w160 (Entails.sepExists_right w168
                      (Entails.sepExists_right w176 (Entails.sepExists_right w184
                        (Entails.refl _))))))))))))))))))))
  have hc6 :
      ((sp - 304#64) ↦₆₄ w8) ∗ ((sp - 296#64) ↦₆₄ w16) ∗
      ((sp - 288#64) ↦₆₄ w24) ∗ ((sp - 280#64) ↦₆₄ w32) ∗
      ((sp - 272#64) ↦₆₄ w40) ∗ ((sp - 264#64) ↦₆₄ w48) ⊢
      memRegion (sp - 304#64) 48 := by
    rw [ProofLib.memRegion_cells (sp - 304#64) 6 (by decide)]
    cells_unfold
    exact Entails.sepExists_right w8 (Entails.sepExists_right w16
      (Entails.sepExists_right w24 (Entails.sepExists_right w32
        (Entails.sepExists_right w40 (Entails.sepExists_right w48 (Entails.refl _))))))
  have h1424 : memRegion (sp - 1520#64) 1424 =
      memRegion (sp - 1520#64) 160 ∗
      memRegion (sp - 1360#64) 880 ∗
      memRegion (sp - 480#64) 176 ∗
      memRegion (sp - 304#64) 48 ∗
      memRegion (sp - 256#64) 160 := by
    rw [ProofLib.memRegion_split' (b := sp - 1520#64) (n := 160) (k := 1264)
          (b' := sp - 1360#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 1360#64) (n := 880) (k := 384)
          (b' := sp - 480#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 480#64) (n := 176) (k := 208)
          (b' := sp - 304#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 304#64) (n := 48) (k := 160)
          (b' := sp - 256#64) rfl (by bv_omega) (by decide)]
  rw [h1424]
  unfold epilogueStagingCells
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp - 1520#64) ↦₆₄ w192) ∗ ((sp - 1512#64) ↦₆₄ w200) ∗
     ((sp - 1504#64) ↦₆₄ w208) ∗ ((sp - 1496#64) ↦₆₄ w216) ∗
     ((sp - 1488#64) ↦₆₄ w64) ∗ ((sp - 1480#64) ↦₆₄ w72) ∗
     ((sp - 1472#64) ↦₆₄ w80) ∗ ((sp - 1464#64) ↦₆₄ w88) ∗
     ((sp - 1456#64) ↦₆₄ w96) ∗ ((sp - 1448#64) ↦₆₄ w104) ∗
     ((sp - 1440#64) ↦₆₄ w112) ∗ ((sp - 1432#64) ↦₆₄ w120) ∗
     ((sp - 1424#64) ↦₆₄ w128) ∗ ((sp - 1416#64) ↦₆₄ w136) ∗
     ((sp - 1408#64) ↦₆₄ w144) ∗ ((sp - 1400#64) ↦₆₄ w152) ∗
     ((sp - 1392#64) ↦₆₄ w160) ∗ ((sp - 1384#64) ↦₆₄ w168) ∗
     ((sp - 1376#64) ↦₆₄ w176) ∗ ((sp - 1368#64) ↦₆₄ w184)) ∗
    (((sp - 304#64) ↦₆₄ w8) ∗ ((sp - 296#64) ↦₆₄ w16) ∗
     ((sp - 288#64) ↦₆₄ w24) ∗ ((sp - 280#64) ↦₆₄ w32) ∗
     ((sp - 272#64) ↦₆₄ w40) ∗ ((sp - 264#64) ↦₆₄ w48)) ∗
    (memRegion (sp - 1360#64) 880 ∗
     memRegion (sp - 480#64) 176 ∗
     memRegion (sp - 256#64) 160) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hc20 (sepConj_mono hc6 (Entails.refl _))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_out_224_eq (out : BitVec 64) :
    memRegion out optProtoInnerStateSize =
      ∃∗ z0 : BitVec 64, ∃∗ z8 : BitVec 64, ∃∗ z16 : BitVec 64, ∃∗ z24 : BitVec 64,
      ∃∗ z32 : BitVec 64, ∃∗ z40 : BitVec 64, ∃∗ z48 : BitVec 64, ∃∗ z56 : BitVec 64,
      ∃∗ z64 : BitVec 64, ∃∗ z72 : BitVec 64, ∃∗ z80 : BitVec 64, ∃∗ z88 : BitVec 64,
      ∃∗ z96 : BitVec 64, ∃∗ z104 : BitVec 64, ∃∗ z112 : BitVec 64, ∃∗ z120 : BitVec 64,
      ∃∗ z128 : BitVec 64, ∃∗ z136 : BitVec 64, ∃∗ z144 : BitVec 64, ∃∗ z152 : BitVec 64,
      ∃∗ z160 : BitVec 64, ∃∗ z168 : BitVec 64, ∃∗ z176 : BitVec 64, ∃∗ z184 : BitVec 64,
      ∃∗ z192 : BitVec 64, ∃∗ z200 : BitVec 64, ∃∗ z208 : BitVec 64, ∃∗ z216 : BitVec 64,
        outWords28 out
          z0 z8 z16 z24 z32 z40 z48 z56
          z64 z72 z80 z88 z96 z104 z112 z120
          z128 z136 z144 z152 z160 z168 z176 z184
          z192 z200 z208 z216 := by
  rw [show optProtoInnerStateSize = 8 * 28 from rfl,
      ProofLib.memRegion_cells out 28 (by decide)]
  unfold outWords28
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc]
  rfl

/-- Common epilogue (`+1544 -> s0.readReg64 .x30`, `0x5d428 -> 0x5d488`):
    copies the 28 output words from `x22`, `x21`, and `epilogueStagingCells s0.sp` into `out`,
    restores `x19..x30` and `sp = s0.sp`, and recombines `stackAt s0.sp statesIntoPbStack`. -/
theorem states_into_pb_epilogue {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64)
    (w8 w16 w24 w32 w40 w48
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1544#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
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
  states_into_pb_fetches_range b (Rust.withPanics ext) 1544 100
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  rw [memRegion_out_224_eq out]
  wp_pull_exists
  dsimp only [outWords28, epilogueStagingCells, statesIntoPbSavedCells]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

end CryptoVerification.SpqrV1.States.IntoPb
