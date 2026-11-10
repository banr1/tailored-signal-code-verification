/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Basic-Block Step Lemmas for `spqr::init_inner` (`0x532dc..0x5349c`, 112 instructions)

**Checked by Lean.**

Proves stack-frame layout helpers, the `.v0` path, `.v1` prologue/epilogue, post-`Authenticator::new`
state construction, and `auth_key` slice-clone basic blocks for `spqr::init_inner`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.InitInner

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
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
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

/-! ## 1. Stack Frame and Representation Helpers -/

/-- Callee-saved register save area at `[s0.sp - 48 .. s0.sp)` (`48` bytes = 6 words). -/
def initInnerSavedCells (s0 : State) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem initInnerSavedCells_entails_memRegion (s0 : State) :
    initInnerSavedCells s0 ⊢ memRegion (s0.sp - 48#64) 48 := by
  unfold initInnerSavedCells
  rw [ProofLib.memRegion_cells (s0.sp - 48#64) 6 (by decide)]
  cells_unfold
  refine Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
      (Entails.sepExists_right (s0.readReg64 .x28)
        (Entails.sepExists_right (s0.readReg64 .x21)
          (Entails.sepExists_right (s0.readReg64 .x20)
            (Entails.sepExists_right (s0.readReg64 .x19) ?_)))))
  exact Entails.of_eq (by simp only [arm64_norm])

theorem stackAt_initInner_split (sp : BitVec 64) :
    stackAt sp initInnerStack =
      stackAt (sp - 1040#64) authNewStackX ∗
      memRegion (sp - 1040#64) 992 ∗
      cells (sp - 48#64) 6 := by
  change memRegion (sp - 17680#64) 17680 =
    memRegion ((sp - 1040#64) - 16640#64) 16640 ∗
    memRegion (sp - 1040#64) 992 ∗
    cells (sp - 48#64) 6
  have hsub : (sp - 1040#64) - 16640#64 = sp - 17680#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 17680#64) (n := 16640) (k := 1040)
        (b' := sp - 1040#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1040#64) (n := 992) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]

theorem stack_restore_initInner (s0 : State) :
    stackAt (s0.sp - 1040#64) authNewStackX ∗
    memRegion (s0.sp - 1040#64) 992 ∗
    initInnerSavedCells s0 ⊢
    stackAt s0.sp initInnerStack := by
  rw [stackAt_initInner_split s0.sp, ← ProofLib.memRegion_cells (s0.sp - 48#64) 6 (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (initInnerSavedCells_entails_memRegion s0))

theorem memRegion_out_224_split_8 (out : BitVec 64) :
    memRegion out optProtoInnerStateSize =
      (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗ memRegion (out + 8#64) 216 := by
  change memRegion out 224 = (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗ memRegion (out + 8#64) 216
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 216)
        (b' := out + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_cells out 1 (by decide)]
  simp only [cells, sepConj_emp]

theorem vecU8_nil_of_cells (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A v [] := by
  refine Entails.trans ?_ (vecU8_of_header_payload A v 0#64 1#64 [])
  unfold vecU8Payload
  have hite :
      (if (0#64 : BitVec 64) = 0#64 then (emp : SepProp)
       else A.live 1#64 (0#64 : BitVec 64).toNat 1 ∗ (1#64 ↦ₛ ([] : Bytes)) ∗
         memRegion (1#64 + BitVec.ofNat 64 ([] : Bytes).length) ((0#64 : BitVec 64).toNat - ([] : Bytes).length)) =
      emp := rfl
  rw [hite, sepConj_emp]
  dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ 1#64 ≠ 0#64⌝ ∗
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) = _ by ac_rfl))
  exact Entails.pure_right
    (φ := 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ 1#64 ≠ 0#64)
    (by decide) (Entails.refl _)

theorem vecU8_nonempty_of_cells (A : RustAlloc) (v ptr : BitVec 64) (bs : Bytes)
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    ((v + 8#64) ↦₆₄ ptr) ∗
    ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    A.live ptr bs.length 1 ∗
    (ptr ↦ₛ bs) ⊢
      vecU8 A v bs := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne : BitVec.ofNat 64 bs.length ≠ 0#64 := by
    intro h
    have h1 := congrArg BitVec.toNat h
    rw [htoNat] at h1
    change bs.length = 0 at h1
    omega
  refine Entails.trans ?_ (vecU8_of_header_payload A v (BitVec.ofNat 64 bs.length) ptr bs)
  unfold vecU8Payload
  have hite :
      (if BitVec.ofNat 64 bs.length = 0#64 then (emp : SepProp)
       else A.live ptr (BitVec.ofNat 64 bs.length).toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) ((BitVec.ofNat 64 bs.length).toNat - bs.length)) =
      (A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)) := by
    rw [ite_eq_right_iff.mpr (fun h => False.elim (hne h)), htoNat, Nat.sub_self,
        ProofLib.memRegion_zero, sepConj_emp]
  rw [hite, htoNat]
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    ((v ↦₆₄ BitVec.ofNat 64 bs.length) ∗
     ((v + 8#64) ↦₆₄ ptr) ∗
     ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
     A.live ptr bs.length 1 ∗
     (ptr ↦ₛ bs)) = _ by ac_rfl))
  exact Entails.pure_right
    (φ := bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ ptr ≠ 0#64)
    ⟨Nat.le_refl _, hlt, hptr⟩ (Entails.refl _)

theorem sortedSetPtOf_withCapacity_zero (A : RustAlloc) (v : BitVec 64) :
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 2#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) ⊢
      sortedSetPtOf A v (SortedSetPt.withCapacity 0) := by
  unfold sortedSetPtOf vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 2#64 ?_)
  have hite :
      (if (0#64 : BitVec 64) = 0#64 then (emp : SepProp)
       else
         A.live (2#64) ((0#64 : BitVec 64).toNat * ptStride) ptAlign ∗
           arrayAt ptAt ptStride 2#64 [] ∗
             memRegion (2#64 + BitVec.ofNat 64 (0 * ptStride)) (((0#64 : BitVec 64).toNat - 0) * ptStride)) =
      emp := rfl
  dsimp only [SortedSetPt.withCapacity, List.length_nil, BitVec.ofNat_eq_ofNat]
  rw [hite, sepConj_comm _ (_ ∗ emp), sepConj_emp]
  exact Entails.pure_right
    (φ := 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * ptStride < 2 ^ 63 ∧ 2#64 ≠ 0#64)
    (by decide) (Entails.refl _)

/-- `n` consecutive 24-byte `(0, 2, 0)` `SortedSet<Pt>` headers starting at `base`. -/
def emptySortedSetPtCells : Nat → BitVec 64 → SepProp
  | 0, _ => emp
  | n + 1, base =>
    ((base ↦₆₄ 0#64) ∗ ((base + 8#64) ↦₆₄ 2#64) ∗ ((base + 16#64) ↦₆₄ 0#64)) ∗
      emptySortedSetPtCells n (base + 24#64)

theorem emptySortedSetPtCells_entails (A : RustAlloc) :
    ∀ (n : Nat) (base : BitVec 64),
      emptySortedSetPtCells n base ⊢
        sortedSetPtListOf A base (List.replicate n (SortedSetPt.withCapacity 0))
  | 0, _ => Entails.refl emp
  | n + 1, base =>
    sepConj_mono (sortedSetPtOf_withCapacity_zero A base)
      (emptySortedSetPtCells_entails A n (base + 24#64))

theorem polyDecoderAt_initHdrDecoder (A : RustAlloc) (a : BitVec 64) :
    emptySortedSetPtCells 16 a ∗
      ((a + 384#64) ↦₆₄ 48#64) ∗
      ((a + 392#64) ↦₈ 0#8) ∗
      memRegion (a + 393#64) 7 ⊢
      polyDecoderAt A a initHdrDecoder := by
  unfold polyDecoderAt polyDecoderPtsNeededOff polyDecoderIsCompleteOff
    polyDecoderPadOff polyDecoderPadSize boolByte
  dsimp only [initHdrDecoder, BitVec.ofNat_eq_ofNat]
  refine Entails.pure_right
    (φ := (List.replicate 16 (SortedSetPt.withCapacity 0)).length = NUM_POLYS ∧ 48 < 2 ^ 64)
    (by decide) ?_
  refine Entails.trans
    (sepConj_mono_left (emptySortedSetPtCells_entails A 16 a)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem initInner_seq_sepWP_inImage {prog : Program} {img : Obj.Image}
    {ret mid : BitVec 64} {s : State}
    {P P' : SepProp} {Post : State → Prop} {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hstep : SepWP prog mid s P (fun s' P1 => (P1 ⊢ P') ∧ Post s'))
    (hnext : ∀ s' : State, s'.pc = mid → s'.status = .Running →
      ImgCallInv img s' → Post s' → SepWPp prog ret s' P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.of_sepWP_inImage (mid := mid) hinv ?_
  refine SepWP.mono hstep ?_
  intro s' P1 hpc' hrun' ⟨hent, hpost⟩ hinv'
  exact SepWPp.weaken_pre hent (hnext s' hpc' hrun' hinv' hpost)

/-! ## 2. Version `.v0` Branch (`+0 -> +28 -> +92 -> +116`) and Epilogue (`+416 -> +432`) -/

/-- Full execution of `spqr::init_inner` for `v = .v0` (`w1 = 0#32`):
    `+0 -> +28 -> +92 -> +116 -> ret`. -/
theorem init_inner_v0 {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (out : BitVec 64) (d : Direction) (authKey : Bytes) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hw1 : s0.readReg32 .x1 = Version.v0.toI32) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0
      (memRegion out optProtoInnerStateSize ∗
       stackAt s0.sp initInnerStack ∗
       Rest)
      (fun sf Pf =>
        (Pf ⊢
          initInnerResultAt A (F := F) out .v0 d authKey ∗
          stackAt s0.sp initInnerStack ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hrestore :
      initInnerResultAt A (F := F) out .v0 d authKey ∗
      (stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992 ∗
       initInnerSavedCells s0) ∗
      Rest ⊢
      initInnerResultAt A (F := F) out .v0 d authKey ∗
      stackAt s0.sp initInnerStack ∗
      Rest :=
    sepConj_mono_right (sepConj_mono_left (stack_restore_initInner s0))
  refine SepWP.strengthen_entails_const hrestore ?_
  have hsp48_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 48#64 hsp0_align (by decide)
  have hsp1040_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  init_inner_fetches_range b (Rust.withPanics ext) 0 32
  init_inner_fetches_range b (Rust.withPanics ext) 92 28
  dsimp only [tripleRatchetProgAtExt, initInnerName, Version.toI32,
    State.readReg32, Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat] at hpc hx0 hw1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  rw [memRegion_out_224_split_8 out, stackAt_initInner_split s0.sp]
  cells_unfold
  wp_pull_exists
  dsimp only [initInnerResultAt, initInnerValue, Option.map,
    optProtoPqRatchetInnerAt, none3Cap',
    initInnerSavedCells]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- Epilogue of `spqr::init_inner` for `v = .v1` (`+416 -> +432 -> ret`). -/
theorem init_inner_epilogue {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992 ∗
       initInnerSavedCells s0 ∗
       Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp initInnerStack ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hrestore :
      (stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992 ∗
       initInnerSavedCells s0) ∗
      Rest ⊢
      stackAt s0.sp initInnerStack ∗ Rest :=
    sepConj_mono_left (stack_restore_initInner s0)
  refine SepWP.strengthen_entails_const hrestore ?_
  have hsp48_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 48#64 hsp0_align (by decide)
  have hsp1040_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_range b (Rust.withPanics ext) 416 20
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  dsimp only [initInnerSavedCells]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-! ## 3. Version `.v1` Prologue (`+0 -> +36`) and Post-`Authenticator::new` Construction -/

/-- Prologue of `spqr::init_inner` for `v = .v1` (`w1 = 1#32`):
    `+0 -> +36` (`0x532dc..0x53300`, 9 instructions). -/
theorem init_inner_prologue_v1 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (out akPtr : BitVec 64) (d : Direction) (authKey : Bytes) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hw1 : s0.readReg32 .x1 = Version.v1.toI32)
    (hw2 : s0.readReg32 .x2 = d.toI32)
    (hx3 : s0.readReg64 .x3 = akPtr)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 authKey.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64) s0
      (cells (s0.sp - 48#64) 6 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ initInnerSavedCells s0 ∗ Rest) ∧
        s1.sp = s0.sp - 1040#64 ∧
        s1.readReg64 .x29 = s0.sp - 48#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x20 = BitVec.ofNat 64 authKey.length ∧
        s1.readReg32 .x2 = d.toI32 ∧
        s1.readReg64 .x3 = akPtr ∧
        (s1.readReg64 .x22 = s0.readReg64 .x22 ∧
         s1.readReg64 .x23 = s0.readReg64 .x23 ∧
         s1.readReg64 .x24 = s0.readReg64 .x24 ∧
         s1.readReg64 .x25 = s0.readReg64 .x25 ∧
         s1.readReg64 .x26 = s0.readReg64 .x26 ∧
         s1.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        s1.trace = s0.trace) := by
  have hsp48_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 48#64 hsp0_align (by decide)
  init_inner_fetches_range b (Rust.withPanics ext) 0 36
  dsimp only [tripleRatchetProgAtExt, initInnerName, Version.toI32,
    State.readReg32, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, BitVec.ofNat_eq_ofNat]
    at hpc hx0 hw1 hw2 hx3 hx4 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  dsimp only [initInnerSavedCells]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- Post-`Authenticator::new` construction for `d = .a2b` (`+368 -> +412`, 11 instructions):
    copies `Authenticator` from `[s0.sp - 104 .. s0.sp - 56)` into `[s0.sp - 1024 .. s0.sp - 976)`,
    stores `epoch = 1` at `s0.sp - 976` and tag `2` at `s0.sp - 1032`, and sets `x0 = s0.sp - 1032`,
    `x8 = out` for `<States>::into_pb`. -/
theorem init_inner_a2b_post_auth {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (authKey : Bytes)
    (a0 a1 a2 a3 a4 a5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 368#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 412#64) s
      ((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
        ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
        ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
       cells (s0.sp - 1032#64) 8 ∗
       memRegion (s0.sp - 968#64) 864 ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢
          chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
          memRegion (s0.sp - 104#64) 48 ∗
          Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x8 = out ∧
        s2.readReg64 .x0 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hst :
      (((s0.sp - 1032#64) ↦₆₄ 2#64) ∗
       (((s0.sp - 1024#64) ↦₆₄ a0) ∗ ((s0.sp - 1016#64) ↦₆₄ a1) ∗
        ((s0.sp - 1008#64) ↦₆₄ a2) ∗ ((s0.sp - 1000#64) ↦₆₄ a3) ∗
        ((s0.sp - 992#64) ↦₆₄ a4) ∗ ((s0.sp - 984#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64)) ∗
       ((s0.sp - 976#64) ↦₆₄ 1#64) ∗
       memRegion (s0.sp - 968#64) 864) ∗
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
       ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
       ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
      Rest ⊢
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
      memRegion (s0.sp - 104#64) 48 ∗
      Rest := by
    have hauth :
        ((s0.sp - 1024#64) ↦₆₄ a0) ∗ ((s0.sp - 1016#64) ↦₆₄ a1) ∗
        ((s0.sp - 1008#64) ↦₆₄ a2) ∗ ((s0.sp - 1000#64) ↦₆₄ a3) ∗
        ((s0.sp - 992#64) ↦₆₄ a4) ∗ ((s0.sp - 984#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ⊢
        authenticatorAt A ((s0.sp - 1032#64) + 8#64) (Authenticator.new F authKey 1#64) := by
      have h := authenticatorAt_of_words_heap A ((s0.sp - 1032#64) + 8#64) a0 a1 a2 a3 a4 a5
        (Authenticator.new F authKey 1#64)
      simpa only [arm64_norm, sepConj_assoc] using h
    have h48 :
        ((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
        ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
        ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5) ⊢
        memRegion (s0.sp - 104#64) 48 := by
      rw [ProofLib.memRegion_cells (s0.sp - 104#64) 6 (by decide)]
      cells_unfold
      refine Entails.sepExists_right a0 (Entails.sepExists_right a1
        (Entails.sepExists_right a2 (Entails.sepExists_right a3
          (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
      exact Entails.of_eq (by simp only [arm64_norm])
    dsimp only [initV1State, chunkedStatesAt, chunkedKeysUnsampledAt, unchunkedKeysUnsampledAt]
    have h56 : (s0.sp - 1032#64) + 8#64 + 48#64 = s0.sp - 976#64 := by bv_omega
    have h64 : (s0.sp - 1032#64) + 64#64 = s0.sp - 968#64 := by bv_omega
    rw [h56, h64]
    refine sepConj_mono ?_ (sepConj_mono_left h48)
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left hauth)) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.strengthen_entails_const hst ?_
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_range b (Rust.withPanics ext) 368 44
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

set_option maxHeartbeats 1600000 in
/-- Post-`Authenticator::new` construction for `d = .b2a` (`+196 -> +340 -> +400 -> +412`, 41 instructions):
    copies `Authenticator` from `[s0.sp - 104 .. s0.sp - 56)` into `[s0.sp - 1024 .. s0.sp - 976)`,
    initializes `initHdrDecoder` at `[s0.sp - 968 .. s0.sp - 568)` and tag `7` at `s0.sp - 1032`,
    and sets `x0 = s0.sp - 1032`, `x8 = out` for `<States>::into_pb`. -/
theorem init_inner_b2a_post_auth {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (authKey : Bytes)
    (a0 a1 a2 a3 a4 a5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 196#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 412#64) s
      ((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
        ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
        ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
       cells (s0.sp - 56#64) 1 ∗
       cells (s0.sp - 1032#64) 20 ∗
       cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗
       (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗
       memRegion (s0.sp - 568#64) 464 ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢
          chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .b2a authKey) ∗
          memRegion (s0.sp - 104#64) 56 ∗
          Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x8 = out ∧
        s2.readReg64 .x0 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hst :
      (((s0.sp - 1032#64) ↦₆₄ 7#64) ∗
       (((s0.sp - 1024#64) ↦₆₄ a0) ∗ ((s0.sp - 1016#64) ↦₆₄ a1) ∗
        ((s0.sp - 1008#64) ↦₆₄ a2) ∗ ((s0.sp - 1000#64) ↦₆₄ a3) ∗
        ((s0.sp - 992#64) ↦₆₄ a4) ∗ ((s0.sp - 984#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64)) ∗
       ((s0.sp - 976#64) ↦₆₄ 1#64) ∗
       (emptySortedSetPtCells 16 (s0.sp - 968#64) ∗
        ((s0.sp - 584#64) ↦₆₄ 48#64) ∗
        ((s0.sp - 576#64) ↦₈ 0#8) ∗
        memRegion (s0.sp - 575#64) 7) ∗
       memRegion (s0.sp - 568#64) 464) ∗
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
       ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
       ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5) ∗
       ((s0.sp - 56#64) ↦₆₄ 1#64)) ∗
      Rest ⊢
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .b2a authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗
      Rest := by
    have hauth :
        ((s0.sp - 1024#64) ↦₆₄ a0) ∗ ((s0.sp - 1016#64) ↦₆₄ a1) ∗
        ((s0.sp - 1008#64) ↦₆₄ a2) ∗ ((s0.sp - 1000#64) ↦₆₄ a3) ∗
        ((s0.sp - 992#64) ↦₆₄ a4) ∗ ((s0.sp - 984#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ⊢
        authenticatorAt A ((s0.sp - 1032#64) + 8#64) (Authenticator.new F authKey 1#64) := by
      have h := authenticatorAt_of_words_heap A ((s0.sp - 1032#64) + 8#64) a0 a1 a2 a3 a4 a5
        (Authenticator.new F authKey 1#64)
      simpa only [arm64_norm, sepConj_assoc] using h
    have hpoly :
        emptySortedSetPtCells 16 (s0.sp - 968#64) ∗
        ((s0.sp - 584#64) ↦₆₄ 48#64) ∗
        ((s0.sp - 576#64) ↦₈ 0#8) ∗
        memRegion (s0.sp - 575#64) 7 ⊢
        polyDecoderAt A ((s0.sp - 1032#64) + 8#64 + 56#64) initHdrDecoder := by
      have h := polyDecoderAt_initHdrDecoder A (s0.sp - 968#64)
      simpa only [arm64_norm] using h
    have h56_cells :
        ((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
        ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
        ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5) ∗
        ((s0.sp - 56#64) ↦₆₄ 1#64) ⊢
        memRegion (s0.sp - 104#64) 56 := by
      rw [ProofLib.memRegion_cells (s0.sp - 104#64) 7 (by decide)]
      cells_unfold
      refine Entails.sepExists_right a0 (Entails.sepExists_right a1
        (Entails.sepExists_right a2 (Entails.sepExists_right a3
          (Entails.sepExists_right a4 (Entails.sepExists_right a5
            (Entails.sepExists_right 1#64 ?_))))))
      exact Entails.of_eq (by simp only [arm64_norm])
    dsimp only [initV1State, chunkedStatesAt, chunkedNoHeaderReceivedAt, unchunkedNoHeaderReceivedAt]
    have h56 : (s0.sp - 1032#64) + 8#64 + 48#64 = s0.sp - 976#64 := by bv_omega
    have h464 : (s0.sp - 1032#64) + 464#64 = s0.sp - 568#64 := by bv_omega
    rw [h56, h464]
    refine sepConj_mono ?_ (sepConj_mono_left h56_cells)
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left hauth)) ?_
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpoly)))) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.strengthen_entails_const hst ?_
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_range b (Rust.withPanics ext) 196 148
  init_inner_fetches_range b (Rust.withPanics ext) 400 12
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  simp (config := { maxSteps := 500000 }) only [ProofLib.cells_succ, ProofLib.cells_zero,
    sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  wp_pull_exists
  simp only [emptySortedSetPtCells, arm64_norm, sepConj_emp]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-! ## 4. Slice-Clone Basic Blocks (`authKey` -> `vecU8 A (s0.sp - 1032#64) authKey`) -/

/-- `.a2b` empty-slice path (`+36 -> +120 -> +344 -> +364`):
    constructs `vecU8 A (s0.sp - 1032#64) []` on the stack without allocating. -/
theorem init_inner_a2b_empty_to_364 {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hw2 : s.readReg32 .x2 = Direction.a2b.toI32)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 364#64) s
      (cells (s0.sp - 1032#64) 3 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ vecU8 A (s0.sp - 1032#64) [] ∗ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x0 = s0.sp - 104#64 ∧
        s2.readReg64 .x1 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hvec :
      (((s0.sp - 1032#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 1024#64) ↦₆₄ 1#64) ∗
       ((s0.sp - 1016#64) ↦₆₄ 0#64)) ∗ Rest ⊢
      vecU8 A (s0.sp - 1032#64) [] ∗ Rest := by
    refine sepConj_mono_left ?_
    simpa only [arm64_norm] using vecU8_nil_of_cells A (s0.sp - 1032#64)
  refine SepWP.strengthen_entails_const hvec ?_
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_range b (Rust.withPanics ext) 36 4
  init_inner_fetches_range b (Rust.withPanics ext) 120 4
  init_inner_fetches_range b (Rust.withPanics ext) 344 20
  dsimp only [tripleRatchetProgAtExt, initInnerName, Direction.toI32,
    State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- `.b2a` empty-slice path (`+36 -> +40 -> +172 -> +192`):
    constructs `vecU8 A (s0.sp - 1032#64) []` on the stack without allocating. -/
theorem init_inner_b2a_empty_to_192 {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hw2 : s.readReg32 .x2 = Direction.b2a.toI32)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 192#64) s
      (cells (s0.sp - 1032#64) 3 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ vecU8 A (s0.sp - 1032#64) [] ∗ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x0 = s0.sp - 104#64 ∧
        s2.readReg64 .x1 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hvec :
      (((s0.sp - 1032#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 1024#64) ↦₆₄ 1#64) ∗
       ((s0.sp - 1016#64) ↦₆₄ 0#64)) ∗ Rest ⊢
      vecU8 A (s0.sp - 1032#64) [] ∗ Rest := by
    refine sepConj_mono_left ?_
    simpa only [arm64_norm] using vecU8_nil_of_cells A (s0.sp - 1032#64)
  refine SepWP.strengthen_entails_const hvec ?_
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_range b (Rust.withPanics ext) 36 8
  init_inner_fetches_range b (Rust.withPanics ext) 172 20
  dsimp only [tripleRatchetProgAtExt, initInnerName, Direction.toI32,
    State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- `.a2b` non-empty slice step 1 (`+36 -> +120 -> +128`, 3 instructions). -/
theorem init_inner_a2b_to_128
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hlen_ne : (len == 0#64) = false)
    (hw2 : s.readReg32 .x2 = Direction.a2b.toI32)
    (hx3 : s.readReg64 .x3 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 128#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x21 = akPtr ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_range b (Rust.withPanics ext) 36 4
  init_inner_fetches_range b (Rust.withPanics ext) 120 8
  dsimp only [tripleRatchetProgAtExt, initInnerName, Direction.toI32,
    State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `.a2b` non-empty slice step 2 (`+132 -> +140`, 2 instructions). -/
theorem init_inner_a2b_132_to_140
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hx21 : s.readReg64 .x21 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 140#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x21 = akPtr ∧
        s2.readReg64 .x0 = len ∧
        s2.readReg64 .x1 = 1#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_range b (Rust.withPanics ext) 132 8
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `.a2b` non-empty slice OOM branch (`+144 -> +436 -> +444`, 3 instructions). -/
theorem init_inner_a2b_144_oom_to_444
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx20 : s.readReg64 .x20 = len)
    (hx0 : s.readReg64 .x0 = 0#64)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 444#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x0 = 1#64 ∧
        s2.readReg64 .x1 = len ∧
        s2.trace = s0.trace) := by
  init_inner_fetches_range b (Rust.withPanics ext) 144 4
  init_inner_fetches_range b (Rust.withPanics ext) 436 8
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `.a2b` non-empty slice step 3 (`+144 -> +160`, 4 instructions). -/
theorem init_inner_a2b_144_ok_to_160
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len ptr : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hx21 : s.readReg64 .x21 = akPtr)
    (hx0 : s.readReg64 .x0 = ptr)
    (hptr_ne : (ptr == 0#64) = false)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 160#64) s
      (cells (s0.sp - 1032#64) 2 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ ((s0.sp - 1032#64) ↦₆₄ len) ∗ ((s0.sp - 1024#64) ↦₆₄ ptr) ∗ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x0 = ptr ∧
        s2.readReg64 .x1 = akPtr ∧
        s2.readReg64 .x2 = len ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_range b (Rust.withPanics ext) 144 16
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- `.a2b` non-empty slice step 4 (`+164 -> +168 -> +356 -> +364`, 4 instructions). -/
theorem init_inner_a2b_164_to_364 {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out ptr : BitVec 64) (authKey : Bytes) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpos : 0 < authKey.length)
    (hlt : authKey.length < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 164#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 364#64) s
      (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
       cells (s0.sp - 1016#64) 1 ∗
       A.live ptr authKey.length 1 ∗
       (ptr ↦ₛ authKey) ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢ vecU8 A (s0.sp - 1032#64) authKey ∗ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x0 = s0.sp - 104#64 ∧
        s2.readReg64 .x1 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hvec :
      (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
       ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       A.live ptr authKey.length 1 ∗
       (ptr ↦ₛ authKey)) ∗ Rest ⊢
      vecU8 A (s0.sp - 1032#64) authKey ∗ Rest := by
    refine sepConj_mono_left ?_
    simpa only [arm64_norm] using vecU8_nonempty_of_cells A (s0.sp - 1032#64) ptr authKey hpos hlt hptr
  refine SepWP.strengthen_entails_const hvec ?_
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_range b (Rust.withPanics ext) 164 8
  init_inner_fetches_range b (Rust.withPanics ext) 356 8
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- `.b2a` non-empty slice step 1 (`+36 -> +48`, 3 instructions). -/
theorem init_inner_b2a_to_48
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hlen_ne : (len == 0#64) = false)
    (hw2 : s.readReg32 .x2 = Direction.b2a.toI32)
    (hx3 : s.readReg64 .x3 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 48#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x21 = akPtr ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_range b (Rust.withPanics ext) 36 12
  dsimp only [tripleRatchetProgAtExt, initInnerName, Direction.toI32,
    State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `.b2a` non-empty slice step 2 (`+52 -> +60`, 2 instructions). -/
theorem init_inner_b2a_52_to_60
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 52#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hx21 : s.readReg64 .x21 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 60#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x21 = akPtr ∧
        s2.readReg64 .x0 = len ∧
        s2.readReg64 .x1 = 1#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  init_inner_fetches_range b (Rust.withPanics ext) 52 8
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `.b2a` non-empty slice OOM branch (`+64 -> +436 -> +444`, 3 instructions). -/
theorem init_inner_b2a_64_oom_to_444
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx20 : s.readReg64 .x20 = len)
    (hx0 : s.readReg64 .x0 = 0#64)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 444#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x0 = 1#64 ∧
        s2.readReg64 .x1 = len ∧
        s2.trace = s0.trace) := by
  init_inner_fetches_range b (Rust.withPanics ext) 64 4
  init_inner_fetches_range b (Rust.withPanics ext) 436 8
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::init_inner" = entry
  examples_hide_fetches
  wp_steps
  wp_done

end CryptoVerification.SpqrV1.Top.InitInner
