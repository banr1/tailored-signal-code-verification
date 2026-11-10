/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.OneKeyStore
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCallees
/-!
# Substages P2.1–P2.3 Framing and Assembly for `message_decrypt_prekey::{closure#0}`

Stack/memory framing helpers and substage compositions for Substages P2.1–P2.3
(`+0x0868#64 -> +0x0d5c#64` and error branches to `+0x1648#64`) of
`message_decrypt_prekey::<PqxdhRng>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false
namespace CryptoVerification.E2E.Pqxdh.ResponderClosure
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
/-- Stack budget for Substages P2.1–P2.4 (`304 + allocHookStack = 4400` bytes). -/
abbrev stageP2aStack : Nat := 304 + allocHookStack
/-! ## 1. Stack & Memory Framing Lemmas for Stage P2a -/

theorem zext64_trunc32_id (w : BitVec 32) :
    (w.zeroExtend 64).setWidth 32 = w :=
  _root_.BitVec.setWidth_setWidth_of_le w (_root_.Nat.le_add_left 32 32)
theorem boxU8Buf_pk_serialize_entails (A : RustAlloc) (ptr : BitVec 64) (pk : PublicKey) :
    boxU8Buf A ptr pk.serialize ⊢ A.live ptr 33 1 ∗ memRegion ptr 33 := by
  have hlen : pk.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  have hne : pk.serialize ≠ [] := by
    intro h; rw [h] at hlen; contradiction
  unfold boxU8Buf
  have h1 := pointsToBytes_entails_memRegion ptr pk.serialize
  rw [hlen] at h1
  simp only [hne, ↓reduceIte, hlen]
  exact Entails.pure_left fun _ => sepConj_mono_right h1
theorem stackAt_1248_promote_eq (sp : BitVec 64) :
    stackAt sp 1248 =
      cells (sp - 1248#64) 8 ∗
      cells (sp - 1184#64) 10 ∗
      memRegion (sp - 1104#64) 656 ∗
      (∃∗ w2e0 : BitVec 64, (sp - 448#64) ↦₆₄ w2e0) ∗
      memRegion (sp - 440#64) 344 ∗
      cells (sp - 96#64) 12 := by
  unfold stackAt
  have h1 : memRegion (sp - BitVec.ofNat 64 1248) 1248 =
      memRegion (sp - 1248#64) 64 ∗ memRegion (sp - 1184#64) 1184 := by
    rw [show (1248 : Nat) = 64 + 1184 from rfl,
      memRegion_split (sp - 1248#64) 64 1184 (by decide),
      show sp - 1248#64 + 64#64 = sp - 1184#64 by bv_omega]
  have h2 : memRegion (sp - 1184#64) 1184 =
      memRegion (sp - 1184#64) 80 ∗ memRegion (sp - 1104#64) 1104 := by
    rw [show (1184 : Nat) = 80 + 1104 from rfl,
      memRegion_split (sp - 1184#64) 80 1104 (by decide),
      show sp - 1184#64 + 80#64 = sp - 1104#64 by bv_omega]
  have h3 : memRegion (sp - 1104#64) 1104 =
      memRegion (sp - 1104#64) 656 ∗ memRegion (sp - 448#64) 448 := by
    rw [show (1104 : Nat) = 656 + 448 from rfl,
      memRegion_split (sp - 1104#64) 656 448 (by decide),
      show sp - 1104#64 + 656#64 = sp - 448#64 by bv_omega]
  have h4 : memRegion (sp - 448#64) 448 =
      memRegion (sp - 448#64) 8 ∗ memRegion (sp - 440#64) 440 := by
    rw [show (448 : Nat) = 8 + 440 from rfl,
      memRegion_split (sp - 448#64) 8 440 (by decide),
      show sp - 448#64 + 8#64 = sp - 440#64 by bv_omega]
  have h5 : memRegion (sp - 440#64) 440 =
      memRegion (sp - 440#64) 344 ∗ memRegion (sp - 96#64) 96 := by
    rw [show (440 : Nat) = 344 + 96 from rfl,
      memRegion_split (sp - 440#64) 344 96 (by decide),
      show sp - 440#64 + 344#64 = sp - 96#64 by bv_omega]
  rw [h1, h2, h3, h4, h5,
    ProofLib.memRegion_cells (sp - 1248#64) 8 (by decide),
    ProofLib.memRegion_cells (sp - 1184#64) 10 (by decide),
    ProofLib.memRegion_eight (sp - 448#64),
    ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
theorem stackAt_176_keypair_eq (sp : BitVec 64) :
    stackAt sp 176 = cells (sp - 176#64) 8 ∗ cells (sp - 112#64) 14 := by
  unfold stackAt
  have h1 : memRegion (sp - BitVec.ofNat 64 176) 176 =
      memRegion (sp - 176#64) 64 ∗ memRegion (sp - 112#64) 112 := by
    rw [show (176 : Nat) = 64 + 112 from rfl,
      memRegion_split (sp - 176#64) 64 112 (by decide),
      show sp - 176#64 + 64#64 = sp - 112#64 by bv_omega]
  rw [h1,
    ProofLib.memRegion_cells (sp - 176#64) 8 (by decide),
    ProofLib.memRegion_cells (sp - 112#64) 14 (by decide)]
theorem memRegion_88_spkPollOut_eq (a : BitVec 64) :
    memRegion a 88 =
      ∃∗ u0 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u10 : BitVec 64,
      ∃∗ u18 : BitVec 64, ∃∗ u20 : BitVec 64, ∃∗ u28 : BitVec 64,
      ∃∗ u30 : BitVec 64, ∃∗ u38 : BitVec 64, ∃∗ u40 : BitVec 64,
      ∃∗ u48 : BitVec 64, ∃∗ u50 : BitVec 64,
        spkPollOutUninitAt a u0 u8 u10 u18 u20 u28 u30 u38 u40 u48 u50 := by
  rw [ProofLib.memRegion_cells a 11 (by decide)]
  unfold spkPollOutUninitAt
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
theorem spkRecordDstAt_eq_out64 (dst pubLen pubPtr privLen privPtr sigLen sigPtr timestamp : BitVec
  64)
    (id : BitVec 32) :
    spkRecordDstAt dst pubLen pubPtr privLen privPtr sigLen sigPtr timestamp id =
      preKeyRecordOut64At dst pubLen pubPtr pubLen privLen privPtr privLen sigLen sigPtr ∗
      ((dst + 0x40#64) ↦₆₄ sigLen) ∗
      ((dst + 0x48#64) ↦₆₄ timestamp) ∗
      ((dst + 0x50#64) ↦₃₂ id) := by
  unfold spkRecordDstAt preKeyRecordOut64At
  ac_rfl
theorem preKeyRecordOut64_tail_entails_88
    (a pubCap pubPtr pubLen privCap privPtr privLen sigCap sigPtr w40 w48 : BitVec 64)
    (w50 w54 : BitVec 32) :
    preKeyRecordOut64At a pubCap pubPtr pubLen privCap privPtr privLen sigCap sigPtr ∗
      ((a + 0x40#64) ↦₆₄ w40) ∗
      ((a + 0x48#64) ↦₆₄ w48) ∗
      ((a + 0x50#64) ↦₃₂ w50) ∗
      ((a + 0x54#64) ↦₃₂ w54) ⊢ memRegion a 88 := by
  rw [memRegion_88_spkPollOut_eq a]
  unfold spkPollOutUninitAt preKeyRecordOut64At
  have hp : ((a + 0x50#64) ↦₃₂ w50) ∗ ((a + 0x54#64) ↦₃₂ w54) =
      ((a + 0x50#64) ↦₆₄ (w54 ++ w50)) := by
    rw [pointsTo64_split32 (a + 0x50#64) (w54 ++ w50),
      show a + 0x50#64 + 4#64 = a + 0x54#64 by bv_omega,
      extractLsb_lo32_append32, extractLsb_hi32_append32]
  refine Entails.sepExists_right pubCap (Entails.sepExists_right pubPtr
    (Entails.sepExists_right pubLen (Entails.sepExists_right privCap
      (Entails.sepExists_right privPtr (Entails.sepExists_right privLen
        (Entails.sepExists_right sigCap (Entails.sepExists_right sigPtr
          (Entails.sepExists_right w40 (Entails.sepExists_right w48
            (Entails.sepExists_right (w54 ++ w50) ?_))))))))))
  rw [← hp]
  exact Entails.of_eq (by ac_rfl)
theorem sp3e0_9_entails_memRegion (sp w0 : BitVec 64) (b8 : BitVec 8) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₈ b8) ⊢ memRegion (sp + 0x3e0#64) 9 := by
  have h : memRegion (sp + 0x3e0#64) 9 =
      memRegion (sp + 0x3e0#64) 8 ∗ memRegion (sp + 0x3e8#64) 1 := by
    rw [show (9 : Nat) = 8 + 1 from rfl,
      memRegion_split (sp + 0x3e0#64) 8 1 (by decide),
      show sp + 0x3e0#64 + 8#64 = sp + 0x3e8#64 by bv_omega]
  rw [h]
  exact sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3e0#64) w0)
    (IsBlock.entails (IsBlock.pointsTo8 (sp + 0x3e8#64) b8)
      (IsBlock.memRegion (sp + 0x3e8#64) 1) fun _ _ => trivial)
theorem memRegion_9_sp3e0_eq (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 9 =
      (∃∗ w0 : BitVec 64, (sp + 0x3e0#64) ↦₆₄ w0) ∗
      (∃∗ b8 : BitVec 8, (sp + 0x3e8#64) ↦₈ b8) := by
  rw [show (9 : Nat) = 8 + 1 from rfl,
    memRegion_split (sp + 0x3e0#64) 8 1 (by decide),
    show sp + 0x3e0#64 + 8#64 = sp + 0x3e8#64 by bv_omega,
    ProofLib.memRegion_eight (sp + 0x3e0#64),
    ProofLib.memRegion_one (sp + 0x3e8#64)]
private theorem cond_eq_cbz_0 : (0#64 == 0#64) = true := rfl
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  cond_eq_cbz_0
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
/-! ### Stage P2 Combinators & Byte-Layout Helpers -/

/-- Extract a pure conjunct `⌜φ⌝` from `P` via `hP : P = ⌜φ⌝ ∗ P_rest` in `SepWPp`. -/
theorem SepWPp.pure_left_frame {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P P_rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = ⌜φ⌝ ∗ P_rest)
    (h : φ → SepWPp prog ret s P_rest Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hP]
  exact SepWPp.pure_elim h
/-- Framed `SepWPp` subroutine call for a `(spec.inImage img)` non-panicking callee. -/
theorem SepWPp.call_frame_inImage_nopanic {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_frame_frozen_nopanic hF hsym hcall hpc hrun hsp hlr
    (φ := (img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ φ)
    (T := T) (F := F) ?_ ⟨⟨hF, hsym⟩, hφ⟩ hP hpan_false hexit_false hnext hoom_false
  dsimp only [Spec.inImage]
  rw [hspec, pure_sepConj_pure_assoc]
/-- Framed `SepWPp` subroutine call for a `(spec.inImage img)` may-panic OOM callee. -/
theorem SepWPp.call_frame_inImage_oom {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗
      anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  refine SepWPp.call_frame_frozen_oom hF hsym htr hcall hpc hrun hsp hlr
    (φ := (img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ φ)
    (T := T) (F := F) ?_ ⟨⟨hF, hsym⟩, hφ⟩ hP hpan_eq hexit_false hnext hoom_false
  dsimp only [Spec.inImage]
  rw [hspec, pure_sepConj_pure_assoc]
def first7 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8]
theorem cell_split7 (a v : BitVec 64) :
    (a ↦₆₄ v) = ((a ↦ₛ first7 v) ∗ ((a + 7#64) ↦₈ v.extractLsb' 56 8)) := by
  rw [pointsTo64_eq_pointsToBytes, show unpack64 v = first7 v ++ [v.extractLsb' 56 8] from rfl,
    pointsToBytes_append, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  rfl
theorem bytes7At_first7_eq (a w : BitVec 64) :
    bytes7At a
      (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8)
      (w.extractLsb' 24 8) (w.extractLsb' 32 8) (w.extractLsb' 40 8)
      (w.extractLsb' 48 8) =
      (a ↦ₛ first7 w) := by
  unfold bytes7At first7
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem point8_bytes7At_eq_pointsTo64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ∃ w : BitVec 64,
      ∀ p : BitVec 64,
        (p ↦₈ b0) ∗ bytes7At (p + 1#64) b1 b2 b3 b4 b5 b6 b7 = (p ↦₆₄ w) := by
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 (bs := [b0, b1, b2, b3, b4, b5, b6, b7]) rfl
  refine ⟨w, fun p => ?_⟩
  rw [pointsTo64_eq_pointsToBytes, ← hw]
  unfold bytes7At
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem list_split4_32 (bs : List (BitVec 8)) :
    bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
  have h1 : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  have h2 : bs.drop 8 = (bs.drop 8).take 8 ++ bs.drop 16 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 8)).symm
  have h3 : bs.drop 16 = (bs.drop 16).take 8 ++ bs.drop 24 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 16)).symm
  exact h1.trans (congrArg (bs.take 8 ++ ·) (h2.trans (congrArg ((bs.drop 8).take 8 ++ ·) h3)))
/-- Complete 64-byte `KeyPair` decomposition relating `(a ↦ₛ pk) ∗ ((a + 32#64) ↦ₛ sk)`,
`keyPair64UnalignedAt a ...`, and the 8 aligned words `u0..u7` (including the 39-byte / 25-byte
split used across `p2_seg5c1_wp` and `p2_seg5c2_wp`). -/
theorem exists_keyPair64_decomp {pk sk : List (BitVec 8)}
    (hpk : pk.length = 32) (hsk : sk.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
      (w0 w1 w2 w3 w4 w5 w6 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64),
      (∀ a : BitVec 64,
        (a ↦ₛ pk) =
          (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3)) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ sk) =
          (a ↦₆₄ u4) ∗ ((a + 8#64) ↦₆₄ u5) ∗ ((a + 16#64) ↦₆₄ u6) ∗ ((a + 24#64) ↦₆₄ u7)) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ pk) ∗ ((a + 32#64) ↦ₛ sk) =
          keyPair64UnalignedAt a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63) ∧
      (∀ a : BitVec 64,
        bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗
        ((a + 7#64) ↦₆₄ w0) ∗ ((a + 15#64) ↦₆₄ w1) ∗ ((a + 23#64) ↦₆₄ w2) ∗ ((a + 31#64) ↦₆₄ w3) =
          (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ∗
          bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6) ∧
      (∀ a : BitVec 64,
        bytes7At a c0 c1 c2 c3 c4 c5 c6 ∗
        ((a + 7#64) ↦₆₄ w4) ∗ ((a + 15#64) ↦₆₄ w5) ∗ ((a + 23#64) ↦₆₄ w6) ∗ ((a + 31#64) ↦₈ b63) =
          (a ↦₆₄ u4) ∗ ((a + 8#64) ↦₆₄ u5) ∗ ((a + 16#64) ↦₆₄ u6) ∗ ((a + 24#64) ↦₆₄ u7)) := by
  obtain ⟨u0, hu0⟩ := exists_unpack64_of_length_8 (bs := pk.take 8) (by simp [hpk])
  obtain ⟨u1, hu1⟩ := exists_unpack64_of_length_8 (bs := (pk.drop 8).take 8) (by simp [hpk])
  obtain ⟨u2, hu2⟩ := exists_unpack64_of_length_8 (bs := (pk.drop 16).take 8) (by simp [hpk])
  obtain ⟨u3, hu3⟩ := exists_unpack64_of_length_8 (bs := pk.drop 24) (by simp [hpk])
  obtain ⟨u4, hu4⟩ := exists_unpack64_of_length_8 (bs := sk.take 8) (by simp [hsk])
  obtain ⟨u5, hu5⟩ := exists_unpack64_of_length_8 (bs := (sk.drop 8).take 8) (by simp [hsk])
  obtain ⟨u6, hu6⟩ := exists_unpack64_of_length_8 (bs := (sk.drop 16).take 8) (by simp [hsk])
  obtain ⟨u7, hu7⟩ := exists_unpack64_of_length_8 (bs := sk.drop 24) (by simp [hsk])
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 (bs := u0.extractLsb' 56 8 :: first7 u1) rfl
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 (bs := u1.extractLsb' 56 8 :: first7 u2) rfl
  obtain ⟨w2, hw2⟩ := exists_unpack64_of_length_8 (bs := u2.extractLsb' 56 8 :: first7 u3) rfl
  obtain ⟨w3, hw3⟩ := exists_unpack64_of_length_8 (bs := u3.extractLsb' 56 8 :: first7 u4) rfl
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 (bs := u4.extractLsb' 56 8 :: first7 u5) rfl
  obtain ⟨w5, hw5⟩ := exists_unpack64_of_length_8 (bs := u5.extractLsb' 56 8 :: first7 u6) rfl
  obtain ⟨w6, hw6⟩ := exists_unpack64_of_length_8 (bs := u6.extractLsb' 56 8 :: first7 u7) rfl
  have hpk_eq : pk = unpack64 u0 ++ (unpack64 u1 ++ (unpack64 u2 ++ unpack64 u3)) := by
    rw [← hu0, ← hu1, ← hu2, ← hu3, ← list_split4_32 pk]
  have hsk_eq : sk = unpack64 u4 ++ (unpack64 u5 ++ (unpack64 u6 ++ unpack64 u7)) := by
    rw [← hu4, ← hu5, ← hu6, ← hu7, ← list_split4_32 sk]
  have h_pk_words : ∀ a : BitVec 64,
      (a ↦ₛ pk) = (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
        ((a + 24#64) ↦₆₄ u3) := by
    intro a
    rw [hpk_eq]
    simp only [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have h_sk_words : ∀ a : BitVec 64,
      (a ↦ₛ sk) = (a ↦₆₄ u4) ∗ ((a + 8#64) ↦₆₄ u5) ∗ ((a + 16#64) ↦₆₄ u6) ∗
        ((a + 24#64) ↦₆₄ u7) := by
    intro a
    rw [hsk_eq]
    simp only [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have h_part1 : ∀ a : BitVec 64,
      bytes7At a
        (u0.extractLsb' 0 8) (u0.extractLsb' 8 8) (u0.extractLsb' 16 8)
        (u0.extractLsb' 24 8) (u0.extractLsb' 32 8) (u0.extractLsb' 40 8)
        (u0.extractLsb' 48 8) ∗
      ((a + 7#64) ↦₆₄ w0) ∗ ((a + 15#64) ↦₆₄ w1) ∗ ((a + 23#64) ↦₆₄ w2) ∗ ((a + 31#64) ↦₆₄ w3) =
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ∗
        bytes7At (a + 32#64)
          (u4.extractLsb' 0 8) (u4.extractLsb' 8 8) (u4.extractLsb' 16 8)
          (u4.extractLsb' 24 8) (u4.extractLsb' 32 8) (u4.extractLsb' 40 8)
          (u4.extractLsb' 48 8) := by
    intro a
    rw [bytes7At_first7_eq a u0, bytes7At_first7_eq (a + 32#64) u4,
        pointsTo64_eq_pointsToBytes (a + 7#64) w0, ← hw0,
        pointsTo64_eq_pointsToBytes (a + 15#64) w1, ← hw1,
        pointsTo64_eq_pointsToBytes (a + 23#64) w2, ← hw2,
        pointsTo64_eq_pointsToBytes (a + 31#64) w3, ← hw3,
        cell_split7 a u0, cell_split7 (a + 8#64) u1,
        cell_split7 (a + 16#64) u2, cell_split7 (a + 24#64) u3]
    simp only [pointsToBytes_cons, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have h_part2 : ∀ a : BitVec 64,
      bytes7At a
        (u4.extractLsb' 0 8) (u4.extractLsb' 8 8) (u4.extractLsb' 16 8)
        (u4.extractLsb' 24 8) (u4.extractLsb' 32 8) (u4.extractLsb' 40 8)
        (u4.extractLsb' 48 8) ∗
      ((a + 7#64) ↦₆₄ w4) ∗ ((a + 15#64) ↦₆₄ w5) ∗ ((a + 23#64) ↦₆₄ w6) ∗
      ((a + 31#64) ↦₈ (u7.extractLsb' 56 8)) =
        (a ↦₆₄ u4) ∗ ((a + 8#64) ↦₆₄ u5) ∗ ((a + 16#64) ↦₆₄ u6) ∗ ((a + 24#64) ↦₆₄ u7) := by
    intro a
    rw [bytes7At_first7_eq a u4,
        pointsTo64_eq_pointsToBytes (a + 7#64) w4, ← hw4,
        pointsTo64_eq_pointsToBytes (a + 15#64) w5, ← hw5,
        pointsTo64_eq_pointsToBytes (a + 23#64) w6, ← hw6,
        cell_split7 a u4, cell_split7 (a + 8#64) u5,
        cell_split7 (a + 16#64) u6, cell_split7 (a + 24#64) u7]
    simp only [pointsToBytes_cons, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine ⟨u0.extractLsb' 0 8, u0.extractLsb' 8 8, u0.extractLsb' 16 8,
    u0.extractLsb' 24 8, u0.extractLsb' 32 8, u0.extractLsb' 40 8,
    u0.extractLsb' 48 8, u7.extractLsb' 56 8,
    u4.extractLsb' 0 8, u4.extractLsb' 8 8, u4.extractLsb' 16 8,
    u4.extractLsb' 24 8, u4.extractLsb' 32 8, u4.extractLsb' 40 8,
    u4.extractLsb' 48 8,
    w0, w1, w2, w3, w4, w5, w6, u0, u1, u2, u3, u4, u5, u6, u7,
    h_pk_words, h_sk_words, ?_, h_part1, h_part2⟩
  intro a
  unfold keyPair64UnalignedAt
  have hp1 := h_part1 a
  have hp2 := h_part2 (a + 32#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp2
  rw [h_pk_words a, h_sk_words (a + 32#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [← hp2]
  have hassoc1 :
      (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ∗
      (bytes7At (a + 32#64)
        (u4.extractLsb' 0 8) (u4.extractLsb' 8 8) (u4.extractLsb' 16 8)
        (u4.extractLsb' 24 8) (u4.extractLsb' 32 8) (u4.extractLsb' 40 8)
        (u4.extractLsb' 48 8) ∗
       ((a + 39#64) ↦₆₄ w4) ∗ ((a + 47#64) ↦₆₄ w5) ∗ ((a + 55#64) ↦₆₄ w6) ∗
       ((a + 63#64) ↦₈ (u7.extractLsb' 56 8))) =
      ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ∗
       bytes7At (a + 32#64)
        (u4.extractLsb' 0 8) (u4.extractLsb' 8 8) (u4.extractLsb' 16 8)
        (u4.extractLsb' 24 8) (u4.extractLsb' 32 8) (u4.extractLsb' 40 8)
        (u4.extractLsb' 48 8)) ∗
      (((a + 39#64) ↦₆₄ w4) ∗ ((a + 47#64) ↦₆₄ w5) ∗ ((a + 55#64) ↦₆₄ w6) ∗
       ((a + 63#64) ↦₈ (u7.extractLsb' 56 8))) := by ac_rfl
  rw [hassoc1, ← hp1]
  ac_rfl

/-! ## 2. Substage P2.2 (`+0x0f14 -> +0x1460` / `+0x1648`) -/

theorem emp_eq_pure_true_emp : (emp : SepProp) = (⌜True⌝ ∗ emp) := by
  simp
theorem pointsToBytes_33_entails_memRegion (ptr : BitVec 64) (pk : List (BitVec 8))
    (h : pk.length = 32) :
    (ptr ↦ₛ (5#8 :: pk)) ⊢ memRegion ptr 33 := by
  have h1 := pointsToBytes_entails_memRegion ptr (5#8 :: pk)
  have hlen : (5#8 :: pk).length = 33 := by simp [h]
  rwa [hlen] at h1
theorem pointsToBytes_32_entails_memRegion (ptr : BitVec 64) (sk : List (BitVec 8))
    (h : sk.length = 32) :
    (ptr ↦ₛ sk) ⊢ memRegion ptr 32 := by
  have h1 := pointsToBytes_entails_memRegion ptr sk
  rwa [h] at h1

theorem sp_a90_65_entails_memRegion (p : BitVec 64) (b0 : BitVec 8)
    (pk sk : List (BitVec 8)) (hpk : pk.length = 32) (hsk : sk.length = 32) :
    (p ↦₈ b0) ∗ ((p + 1#64) ↦ₛ pk) ∗ ((p + 33#64) ↦ₛ sk) ⊢ memRegion p 65 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 1) (k := 64)
        (b' := p + 1#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 1#64) (n := 32) (k := 32)
        (b' := p + 33#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo8_entails_memRegion p b0)
    (sepConj_mono (pointsToBytes_32_entails_memRegion (p + 1#64) pk hpk)
      (pointsToBytes_32_entails_memRegion (p + 33#64) sk hsk))

theorem preKeyRecordOut64_err_entails_88 (p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) :
    preKeyRecordOut64At p w0 w1 w2 w3 w4 w5 w6 w7 ∗
    ((p + 0x40#64) ↦₆₄ w8) ∗ ((p + 0x48#64) ↦₆₄ w9) ∗ ((p + 0x50#64) ↦₆₄ w10) ⊢
      memRegion p 88 := by
  rw [memRegion_88_spkPollOut_eq p]
  unfold spkPollOutUninitAt preKeyRecordOut64At
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5
    (Entails.sepExists_right w6 (Entails.sepExists_right w7
    (Entails.sepExists_right w8 (Entails.sepExists_right w9
    (Entails.sepExists_right w10 (Entails.of_eq (by ac_rfl))))))))))))

/-! ## 3. Substage P2.3 (`+0x1460 -> +0x0d5c` / `+0x1648`) -/

theorem pointsToBytes_1569_entails_memRegion (ptr : BitVec 64) (pk : List (BitVec 8))
    (h : pk.length = 1568) :
    (ptr ↦ₛ (8#8 :: pk)) ⊢ memRegion ptr 1569 := by
  have h1 := pointsToBytes_entails_memRegion ptr (8#8 :: pk)
  have hlen : (8#8 :: pk).length = 1569 := by simp [h]
  rwa [hlen] at h1

theorem pointsToBytes_3169_entails_memRegion (ptr : BitVec 64) (sk : List (BitVec 8))
    (h : sk.length = 3168) :
    (ptr ↦ₛ (8#8 :: sk)) ⊢ memRegion ptr 3169 := by
  have h1 := pointsToBytes_entails_memRegion ptr (8#8 :: sk)
  have hlen : (8#8 :: sk).length = 3169 := by simp [h]
  rwa [hlen] at h1

theorem stackAt_kemKeyPair_eq (sp : BitVec 64) :
    stackAt sp (64 + allocHookStack) =
      (memRegion (sp - 4160#64) 64 ∗ stackAt sp allocHookStack) := by
  have h1 := stackAt_split_top sp 64 allocHookStack (by decide)
  have h2 : BitVec.ofNat 64 (64 + allocHookStack) = 4160#64 := rfl
  rw [h2] at h1
  exact h1

theorem memRegion_65_split_cells5 (p : BitVec 64) :
    memRegion p 65 = cells p 5 ∗ memRegion (p + 40#64) 25 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 40) (k := 25)
        (b' := p + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells p 5 (by decide)]

theorem sp_a90_5words_entails_memRegion (p w0 w1 w2 w3 w4 : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗
    ((p + 24#64) ↦₆₄ w3) ∗ ((p + 32#64) ↦₆₄ w4) ∗ memRegion (p + 40#64) 25 ⊢
      memRegion p 65 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 57) (b' :=
    p + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 49) (b' :=
        p + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 16#64) (n := 8) (k := 41) (b' :=
        p + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 24#64) (n := 8) (k := 33) (b' :=
        p + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 32#64) (n := 8) (k := 25) (b' :=
        p + 40#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion p w0)
    (sepConj_mono (pointsTo64_entails_memRegion (p + 8#64) w1)
    (sepConj_mono (pointsTo64_entails_memRegion (p + 16#64) w2)
    (sepConj_mono (pointsTo64_entails_memRegion (p + 24#64) w3)
      (sepConj_mono_left (pointsTo64_entails_memRegion (p + 32#64) w4)))))

theorem errStr_21_split16_eq (p : BitVec 64) :
    memRegion p 21 =
      (∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u8) ∗ memRegion (p + 16#64) 5) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 13) (b' :=
    p + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 5) (b' :=
        p + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem errStr_overlap13_entails (p ro8 : BitVec 64) :
    ((p + 8#64) ↦₆₄ ro8) ∗ memRegion (p + 16#64) 5 ⊢
      memRegion (p + 8#64) 5 ∗ (∃∗ u13 : BitVec 64, (p + 13#64) ↦₆₄ u13) := by
  rw [← ProofLib.memRegion_eight (p + 13#64),
      ← ProofLib.memRegion_split' (b := p + 8#64) (n := 5) (k := 8) (b' :=
        p + 13#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 5) (b' :=
        p + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (p + 8#64) ro8)

theorem errStr_21_rejoin_entails (p ro0 ro13 : BitVec 64) :
    (p ↦₆₄ ro0) ∗ memRegion (p + 8#64) 5 ∗ ((p + 13#64) ↦₆₄ ro13) ⊢
      memRegion p 21 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 13) (b' :=
    p + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 5) (k := 8) (b' :=
        p + 13#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion p ro0)
    (sepConj_mono_right (pointsTo64_entails_memRegion (p + 13#64) ro13))

theorem memRegion_88_spe_split_eq (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 88 =
      (∃∗ b_400 : BitVec 8, ∃∗ u_3f8 : BitVec 64, ∃∗ u_3f0 : BitVec 64,
       ∃∗ u_3e8 : BitVec 64, ∃∗ u_3e0 : BitVec 64,
        ((sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
        ((sp + 0x3e8#64) ↦₆₄ u_3e8) ∗
        ((sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
        ((sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
        ((sp + 0x400#64) ↦₈ b_400) ∗
        memRegion (sp + 0x401#64) 15 ∗
        memRegion (sp + 0x410#64) 40) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 80) (b' :=
    sp + 0x3e8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 8) (k := 72) (b' :=
        sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 64) (b' :=
        sp + 0x3f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 56) (b' :=
        sp + 0x400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 1) (k := 55) (b' :=
        sp + 0x401#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x401#64) (n := 15) (k := 40) (b' :=
        sp + 0x410#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x3e0#64),
      ProofLib.memRegion_eight (sp + 0x3e8#64),
      ProofLib.memRegion_eight (sp + 0x3f0#64),
      ProofLib.memRegion_eight (sp + 0x3f8#64),
      ProofLib.memRegion_one (sp + 0x400#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem speAt_badCiphertext_preKey_intro (A : RustAlloc) (sp errStrPtr : BitVec 64)
    (herr_nz : errStrPtr ≠ 0#64) :
    ((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
    ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
    ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
    ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
    ((sp + 0x400#64) ↦₈ 3#8) ∗
    memRegion (sp + 0x401#64) 15 ∗
    A.live errStrPtr 21 1 ∗
    memRegion errStrPtr 21 ⊢
      speAt A [] (sp + 0x3e0#64) (.invalidMessage .preKey .badCiphertext) := by
  rw [ProofLib.memRegion_eq_exists_bytes errStrPtr 21 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro bs
  rw [show ((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
        ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
        ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
        ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
        ((sp + 0x400#64) ↦₈ 3#8) ∗
        memRegion (sp + 0x401#64) 15 ∗
        A.live errStrPtr 21 1 ∗
        ⌜bs.length = 21⌝ ∗ (errStrPtr ↦ₛ bs) =
      ⌜bs.length = 21⌝ ∗
        (((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
         ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
         ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
         ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
         ((sp + 0x400#64) ↦₈ 3#8) ∗
         memRegion (sp + 0x401#64) 15 ∗
         A.live errStrPtr 21 1 ∗
         (errStrPtr ↦ₛ bs)) by ac_rfl]
  apply Entails.pure_left; intro hbs
  dsimp only [speAt, invalidMessageStrAt, RustHeap.vecU8, RustHeap.vecU8At, RustHeap.vecHeader]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_right bs (Entails.sepExists_right 21#64 (Entails.sepExists_right
    errStrPtr ?_))
  have h21_nat : (21#64).toNat = 21 := rfl
  have hspe24 : speWord 24 = 0x8000000000000018#64 := rfl
  have hmsg_pk : msgTypeByte MessageType.preKey = 3#8 := rfl
  have h21_sub : (21 : Nat) - 21 = 0 := rfl
  simp only [hbs, show (21#64 = 0#64) = False by decide, show (21#64 = 0) = False by decide,
    ↓reduceIte,
    h21_nat, hspe24, hmsg_pk, h21_sub,
    BitVec.ofNat_eq_ofNat, ProofLib.memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (sp + 0x3e0#64) + 8#64 = sp + 0x3e8#64 by bv_omega,
      show (sp + 0x3e8#64) + 8#64 = sp + 0x3f0#64 by bv_omega,
      show (sp + 0x3e8#64) + 16#64 = sp + 0x3f8#64 by bv_omega,
      show (sp + 0x3e0#64) + 32#64 = sp + 0x400#64 by bv_omega,
      show (sp + 0x3e0#64) + 33#64 = sp + 0x401#64 by bv_omega]
  rw [show ((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
        ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
        ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
        ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
        ⌜21 ≤ 21 ∧ 21 < 2 ^ 63 ∧ errStrPtr ≠ 0#64⌝ ∗
        A.live errStrPtr 21 1 ∗
        (errStrPtr ↦ₛ bs) ∗
        ((sp + 0x400#64) ↦₈ 3#8) ∗
        memRegion (sp + 0x401#64) 15 =
      ⌜21 ≤ 21 ∧ 21 < 2 ^ 63 ∧ errStrPtr ≠ 0#64⌝ ∗
        (((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
         ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
         ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
         ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
         ((sp + 0x400#64) ↦₈ 3#8) ∗
         memRegion (sp + 0x401#64) 15 ∗
         A.live errStrPtr 21 1 ∗
         (errStrPtr ↦ₛ bs)) by ac_rfl]
  refine Entails.pure_right ⟨by decide, by decide, herr_nz⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem SepWPp.bind_sepWPp_frame' {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage F : SepProp} {P_stage_post : State → SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.E2E.Pqxdh.ResponderClosure
