/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb`: Shared Helpers for Arms 7, 8, and 9

**Checked by Lean.**

OOM panic helpers at `+1700` (`0x5d4c4..0x5d4cc`) and `+884` (`0x5d194..0x5d19c`), together with
`vecU8` exposure, clone (`__rust_alloc` + `memcpy`), and deallocation (`__rust_dealloc`) helpers
shared across Arms 7 (`ct1Sampled`), 8 (`ekReceivedCt1Sampled`), and 9 (`ct1Acknowledged`).
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
open CryptoVerification.SpqrV1.Layout.Stubs

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Bit-63 Bounds and `vecU8` Clone/Dealloc Exposure Helpers -/

theorem ofNat_lt_2pow63_msb_zero {n : Nat} (h : n < 2 ^ 63) :
    BitVec.extractLsb' 63 1 (BitVec.ofNat 64 n) = 0#1 := by
  have hlt : (BitVec.ofNat 64 n).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact h
  revert hlt; bv_bits

theorem ofNat_lt_2pow63_and_highBit_zero {n : Nat} (h : n < 2 ^ 63) :
    BitVec.ofNat 64 n &&& 9223372036854775808#64 = 0#64 := by
  have hlt : (BitVec.ofNat 64 n).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact h
  revert hlt; bv_bits

theorem ofNat_lt_2pow63_lsr63_zero {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n >>> 63) &&& 1#64 = 0#64 := by
  have hlt : (BitVec.ofNat 64 n).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact h
  revert hlt; bv_bits

/-- Remaining heap ownership of a `Vec<u8>` after splitting out `(ptr ↦ₛ bs)`. -/
def vecU8CloneTail (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8_expose_clone (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length < 2 ^ 63⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        vecU8CloneTail A cap ptr bs := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_header_sep_buf, vecHeader]
  unfold vecU8Buf vecU8CloneTail
  rw [show ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
  apply Entails.pure_left; intro hpure
  rcases hpure with ⟨hle, hcap, hptr⟩
  have hlen : bs.length < 2 ^ 63 := by omega
  refine Entails.pure_right hlen ?_
  by_cases hc : cap = 0
  · subst hc
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hnil
    have hpure0 : ([] : List (BitVec 8)).length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0 :=
      ⟨hle, hcap, hptr⟩
    simp only [↓reduceIte, pointsToBytes_nil, sepConj_emp, emp_sepConj, List.length_nil]
    have hg :
        ((v ↦₆₄ 0) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗
          ⌜0 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝) =
        ⌜0 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          ((v ↦₆₄ 0) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 0)) := by ac_rfl
    rw [hg]
    exact Entails.pure_right hpure0 (Entails.refl _)
  · simp only [hc, ↓reduceIte]
    have hpure0 : bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 := ⟨hle, hcap, hptr⟩
    have hg :
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
            (A.live ptr cap.toNat 1 ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)))) =
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by ac_rfl
    rw [hg]
    exact Entails.pure_right hpure0 (Entails.refl _)

theorem pointsToBytes_entails_memRegion' (bs : List (BitVec 8)) (ptr : BitVec 64) (h : bs.length < 2 ^ 64) :
    (ptr ↦ₛ bs) ⊢ memRegion ptr bs.length := by
  induction bs generalizing ptr with
  | nil =>
      simp only [pointsToBytes_nil, List.length_nil, memRegion_zero]
      exact Entails.refl _
  | cons b tl ih =>
      simp only [pointsToBytes_cons, List.length_cons] at h ⊢
      rw [Nat.add_comm tl.length 1, ProofLib.memRegion_split ptr 1 tl.length (by omega),
          ProofLib.memRegion_one]
      exact sepConj_mono (Entails.sepExists_right b (Entails.refl _)) (ih (ptr + 1#64) (by omega))

theorem vecU8CloneTail_entails_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (ptr ↦ₛ bs) ∗ vecU8CloneTail A cap ptr bs ⊢ vecCapPtrDealloc A cap ptr := by
  have hbuf : (ptr ↦ₛ bs) ∗ vecU8CloneTail A cap ptr bs ⊢ vecU8Buf A cap ptr bs := by
    unfold vecU8CloneTail vecU8Buf
    rw [show (ptr ↦ₛ bs) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) =
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          ((ptr ↦ₛ bs) ∗
            (if cap = 0 then emp
             else A.live ptr cap.toNat 1 ∗
               memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
    apply Entails.pure_left; intro hpure
    rcases hpure with ⟨hle, hcap, hptr⟩
    have hpure0 : bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 := ⟨hle, hcap, hptr⟩
    refine Entails.pure_right hpure0 ?_
    by_cases hc : cap = 0
    · subst hc
      have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
      subst hnil
      simp only [↓reduceIte, pointsToBytes_nil, sepConj_emp]
      exact Entails.refl _
    · simp only [hc, ↓reduceIte]
      exact Entails.of_eq (by ac_rfl)
  refine Entails.trans hbuf ?_
  unfold vecU8Buf vecCapPtrDealloc
  apply Entails.pure_left; rintro ⟨hle, hcap, hptr⟩
  by_cases hc : (cap == 0#64) = true
  · have hc0 : cap = 0 := by simpa [beq_iff_eq] using hc
    simp only [hc, hc0, ↓reduceIte]
    exact Entails.refl _
  · have hc0 : cap ≠ 0 := by
      intro h; subst h; exact hc rfl
    simp only [hc, hc0, Bool.false_eq_true, ↓reduceIte]
    have hmr : (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
        memRegion ptr cap.toNat := by
      have hsplit := ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
      rw [Nat.add_sub_of_le hle] at hsplit
      rw [hsplit]
      exact sepConj_mono_left (pointsToBytes_entails_memRegion' bs ptr (by omega))
    exact sepConj_mono_right hmr

/-! ## 2. OOM Panic Blocks at `+1700` (`0x5d4c4`) and `+884` (`0x5d194`) -/

/-- OOM panic block at `+1700` (`0x5d4c4..0x5d4cc`: `mov x0, x25; mov x1, x21; bl handle_error`). -/
theorem states_into_pb_panic_1700 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1700#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesIntoPbOnPanic s0 sf ∗ R)) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := statesIntoPbName)
    (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "alloc::raw_vec::handle_error"))
  states_into_pb_fetches_range b (Rust.withPanics ext) 1700 12
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [statesIntoPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

namespace DecoderPb

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

theorem SepWPp.seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_mid : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_mid sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

end DecoderPb

theorem vecU8Buf_nil_intro' (A : RustAlloc) (Rest : SepProp) :
    Rest ⊢ vecU8Buf A 0#64 1#64 [] ∗ Rest := by
  unfold vecU8Buf
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 := by decide
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte, sepConj_emp]
  exact Entails.pure_right hp (Entails.refl _)

theorem vecU8Buf_of_exact_alloc' (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen_pos : 0 < bs.length) (hlen_bound : bs.length < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((ptr ↦ₛ bs) ∗ A.live ptr bs.length 1) ⊢
      vecU8Buf A (BitVec.ofNat 64 bs.length) ptr bs := by
  unfold vecU8Buf
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [htoNat] at ht
    change bs.length = 0 at ht
    omega
  have hp : bs.length ≤ (BitVec.ofNat 64 bs.length).toNat ∧
      (BitVec.ofNat 64 bs.length).toNat < 2 ^ 63 ∧ ptr ≠ 0 :=
    ⟨by omega, by omega, hptr⟩
  have hite :
      (if BitVec.ofNat 64 bs.length = 0 then emp
       else A.live ptr (BitVec.ofNat 64 bs.length).toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) ((BitVec.ofNat 64 bs.length).toNat - bs.length)) =
      (A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)) := by
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  rw [hite]
  exact Entails.pure_right hp (Entails.of_eq (by ac_rfl))

theorem vecU8_of_header_buf (A : RustAlloc) (el cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (el ↦₆₄ cap) ∗ ((el + 8#64) ↦₆₄ ptr) ∗
      ((el + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ⊢
    vecU8 A el bs := by
  have heq :
      (el ↦₆₄ cap) ∗ ((el + 8#64) ↦₆₄ ptr) ∗
        ((el + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs =
      vecU8At A el cap ptr bs := by
    rw [vecU8At_eq_header_sep_buf, vecHeader]
    ac_rfl
  rw [heq]
  exact RustHeap.vecU8At_entails_vecU8 A el cap ptr bs

theorem ofNat_beq_zero_false' {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

theorem ofNat_ne_zero_true {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n != 0#64) = true := by
  rw [bne_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

/-- OOM panic block at `+884` (`0x5d194..0x5d19c`: `mov x0, x25; mov x1, x22; bl handle_error`). -/
theorem states_into_pb_panic_884 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 884#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesIntoPbOnPanic s0 sf ∗ R)) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := statesIntoPbName)
    (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "alloc::raw_vec::handle_error"))
  states_into_pb_fetches_range b (Rust.withPanics ext) 884 12
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [statesIntoPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem vecU8Heap_nil_intro (A : RustAlloc) (Rest : SepProp) :
    Rest ⊢ vecU8Heap A (BitVec.ofNat 64 ([] : List (BitVec 8)).length) 1#64
      (BitVec.ofNat 64 ([] : List (BitVec 8)).length) [] ∗ Rest := by
  unfold vecU8Heap
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, eq_self, pure_true, emp_sepConj]
  exact vecU8Buf_nil_intro' A Rest

theorem vecU8Heap_of_exact_alloc (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen_pos : 0 < bs.length) (hlen_bound : bs.length < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((ptr ↦ₛ bs) ∗ A.live ptr bs.length 1) ⊢
      vecU8Heap A (BitVec.ofNat 64 bs.length) ptr (BitVec.ofNat 64 bs.length) bs := by
  unfold vecU8Heap
  simp only [eq_self, pure_true, emp_sepConj]
  exact vecU8Buf_of_exact_alloc' A ptr bs hlen_pos hlen_bound hptr

theorem memRegion_1424_split_epilogue (sp : BitVec 64) :
    memRegion (sp - 1520#64) 1424 ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64,
      ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w64 : BitVec 64, ∃∗ w72 : BitVec 64,
      ∃∗ w80 : BitVec 64, ∃∗ w88 : BitVec 64, ∃∗ w96 : BitVec 64, ∃∗ w104 : BitVec 64,
      ∃∗ w112 : BitVec 64, ∃∗ w120 : BitVec 64, ∃∗ w128 : BitVec 64, ∃∗ w136 : BitVec 64,
      ∃∗ w144 : BitVec 64, ∃∗ w152 : BitVec 64, ∃∗ w160 : BitVec 64, ∃∗ w168 : BitVec 64,
      ∃∗ w176 : BitVec 64, ∃∗ w184 : BitVec 64, ∃∗ w192 : BitVec 64, ∃∗ w200 : BitVec 64,
      ∃∗ w208 : BitVec 64, ∃∗ w216 : BitVec 64,
        epilogueStagingCells sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        memRegion (sp - 1360#64) 880 ∗
        memRegion (sp - 480#64) 176 ∗
        memRegion (sp - 256#64) 160 := by
  have h1424 : memRegion (sp - 1520#64) 1424 =
      ProofLib.cells (sp - 1520#64) 20 ∗
      memRegion (sp - 1360#64) 880 ∗
      memRegion (sp - 480#64) 176 ∗
      ProofLib.cells (sp - 304#64) 6 ∗
      memRegion (sp - 256#64) 160 := by
    rw [ProofLib.memRegion_split' (b := sp - 1520#64) (n := 160) (k := 1264)
          (b' := sp - 1360#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 1360#64) (n := 880) (k := 384)
          (b' := sp - 480#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 480#64) (n := 176) (k := 208)
          (b' := sp - 304#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 304#64) (n := 48) (k := 160)
          (b' := sp - 256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (sp - 1520#64) 20 (by decide),
        ProofLib.memRegion_cells (sp - 304#64) 6 (by decide)]
  rw [h1424]
  unfold epilogueStagingCells
  cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro w32
  apply Entails.sepExists_elim; intro w40
  apply Entails.sepExists_elim; intro w48
  apply Entails.sepExists_elim; intro w192
  apply Entails.sepExists_elim; intro w200
  apply Entails.sepExists_elim; intro w208
  apply Entails.sepExists_elim; intro w216
  apply Entails.sepExists_elim; intro w64
  apply Entails.sepExists_elim; intro w72
  apply Entails.sepExists_elim; intro w80
  apply Entails.sepExists_elim; intro w88
  apply Entails.sepExists_elim; intro w96
  apply Entails.sepExists_elim; intro w104
  apply Entails.sepExists_elim; intro w112
  apply Entails.sepExists_elim; intro w120
  apply Entails.sepExists_elim; intro w128
  apply Entails.sepExists_elim; intro w136
  apply Entails.sepExists_elim; intro w144
  apply Entails.sepExists_elim; intro w152
  apply Entails.sepExists_elim; intro w160
  apply Entails.sepExists_elim; intro w168
  apply Entails.sepExists_elim; intro w176
  apply Entails.sepExists_elim; intro w184
  refine Entails.sepExists_right w8 (Entails.sepExists_right w16
    (Entails.sepExists_right w24 (Entails.sepExists_right w32
      (Entails.sepExists_right w40 (Entails.sepExists_right w48
        (Entails.sepExists_right w64 (Entails.sepExists_right w72
          (Entails.sepExists_right w80 (Entails.sepExists_right w88
            (Entails.sepExists_right w96 (Entails.sepExists_right w104
              (Entails.sepExists_right w112 (Entails.sepExists_right w120
                (Entails.sepExists_right w128 (Entails.sepExists_right w136
                  (Entails.sepExists_right w144 (Entails.sepExists_right w152
                    (Entails.sepExists_right w160 (Entails.sepExists_right w168
                      (Entails.sepExists_right w176 (Entails.sepExists_right w184
                        (Entails.sepExists_right w192 (Entails.sepExists_right w200
                          (Entails.sepExists_right w208 (Entails.sepExists_right w216
                            (Entails.of_eq (by ac_rfl)))))))))))))))))))))))))))

/-! ## 3. Exposure, Stack Split, and Postcondition Lemmas for Arm 8 (`States.ekReceivedCt1Sampled`) -/

theorem unchunkedCt1SentEkReceived_expose_clone (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (uc : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) :
    unchunkedCt1SentEkReceivedAt A a uc ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ es0 : BitVec 64, ∃∗ es1 : BitVec 64, ∃∗ es2 : BitVec 64,
      ∃∗ ek0 : BitVec 64, ∃∗ ek1 : BitVec 64, ∃∗ ek2 : BitVec 64,
      ∃∗ cap_ct1 : BitVec 64, ∃∗ ptr_ct1 : BitVec 64,
        ⌜uc.ct1.length < 2 ^ 63⌝ ∗
        (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
        ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
        ((a + 48#64) ↦₆₄ es0) ∗ ((a + 56#64) ↦₆₄ es1) ∗ ((a + 64#64) ↦₆₄ es2) ∗
        ((a + 72#64) ↦₆₄ ek0) ∗ ((a + 80#64) ↦₆₄ ek1) ∗ ((a + 88#64) ↦₆₄ ek2) ∗
        ((a + 96#64) ↦₆₄ cap_ct1) ∗ ((a + 104#64) ↦₆₄ ptr_ct1) ∗
        ((a + 112#64) ↦₆₄ BitVec.ofNat 64 uc.ct1.length) ∗
        ((a + 120#64) ↦₆₄ uc.epoch) ∗
        (ptr_ct1 ↦ₛ uc.ct1) ∗
        vecU8CloneTail A cap_ct1 ptr_ct1 uc.ct1 ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 uc.auth ∗
        vecU8Heap A es0 es1 es2 uc.es ∗
        vecU8Heap A ek0 ek1 ek2 uc.ek := by
  unfold unchunkedCt1SentEkReceivedAt
  refine Entails.trans (sepConj_mono (authenticatorAt_expose A a uc.auth)
    (sepConj_mono (vecU8_expose A (a + 48#64) uc.es)
      (sepConj_mono (vecU8_expose A (a + 72#64) uc.ek)
        (sepConj_mono (vecU8_expose_clone A (a + 96#64) uc.ct1) (Entails.refl _))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro cap_ct1
  apply Entails.sepExists_elim; intro ptr_ct1
  apply Entails.sepExists_elim; intro ek0
  apply Entails.sepExists_elim; intro ek1
  apply Entails.sepExists_elim; intro ek2
  apply Entails.sepExists_elim; intro es0
  apply Entails.sepExists_elim; intro es1
  apply Entails.sepExists_elim; intro es2
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5
        (Entails.sepExists_right es0 (Entails.sepExists_right es1
          (Entails.sepExists_right es2 (Entails.sepExists_right ek0
            (Entails.sepExists_right ek1 (Entails.sepExists_right ek2
              (Entails.sepExists_right cap_ct1 (Entails.sepExists_right ptr_ct1 ?_)))))))))))))
  exact Entails.of_eq (by ac_rfl)

theorem chunkedEkReceivedCt1Sampled_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.ekReceivedCt1Sampled s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ es0 : BitVec 64, ∃∗ es1 : BitVec 64, ∃∗ es2 : BitVec 64,
      ∃∗ ek0 : BitVec 64, ∃∗ ek1 : BitVec 64, ∃∗ ek2 : BitVec 64,
      ∃∗ cap_ct1 : BitVec 64, ∃∗ ptr_ct1 : BitVec 64,
        ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
        (stA ↦₆₄ 10#64) ∗
        polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
        ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
        ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
        ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
        ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
        ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
        (ptr_ct1 ↦ₛ s.uc.ct1) ∗
        vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A es0 es1 es2 s.uc.es ∗
        vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
        memRegion (stA + 536#64) 392 := by
  dsimp only [chunkedStatesAt, chunkedEkReceivedCt1SampledAt]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right (unchunkedCt1SentEkReceived_expose_clone A (stA + 8#64 + 400#64) s.uc)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  apply Entails.sepExists_elim; intro es0
  apply Entails.sepExists_elim; intro es1
  apply Entails.sepExists_elim; intro es2
  apply Entails.sepExists_elim; intro ek0
  apply Entails.sepExists_elim; intro ek1
  apply Entails.sepExists_elim; intro ek2
  apply Entails.sepExists_elim; intro cap_ct1
  apply Entails.sepExists_elim; intro ptr_ct1
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5
        (Entails.sepExists_right es0 (Entails.sepExists_right es1
          (Entails.sepExists_right es2 (Entails.sepExists_right ek0
            (Entails.sepExists_right ek1 (Entails.sepExists_right ek2
              (Entails.sepExists_right cap_ct1 (Entails.sepExists_right ptr_ct1 ?_)))))))))))))
  exact Entails.of_eq (by ac_rfl)

theorem stA_ekReceivedCt1Sampled_entails_928 (stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2 c0 c1 c2 epoch : BitVec 64) :
    (stA ↦₆₄ 10#64) ∗
    memRegion (stA + 8#64) polyEncoderSize ∗
    ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
    ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
    ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
    ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
    ((stA + 504#64) ↦₆₄ c0) ∗ ((stA + 512#64) ↦₆₄ c1) ∗ ((stA + 520#64) ↦₆₄ c2) ∗
    ((stA + 528#64) ↦₆₄ epoch) ∗
    memRegion (stA + 536#64) 392 ⊢
    memRegion stA chunkedStatesSize := by
  have hc16 :
      ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
      ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
      ((stA + 504#64) ↦₆₄ c0) ∗ ((stA + 512#64) ↦₆₄ c1) ∗ ((stA + 520#64) ↦₆₄ c2) ∗
      ((stA + 528#64) ↦₆₄ epoch) ⊢
      memRegion (stA + 408#64) 128 := by
    rw [ProofLib.memRegion_cells (stA + 408#64) 16 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5
          (Entails.sepExists_right es0 (Entails.sepExists_right es1
            (Entails.sepExists_right es2 (Entails.sepExists_right ek0
              (Entails.sepExists_right ek1 (Entails.sepExists_right ek2
                (Entails.sepExists_right c0 (Entails.sepExists_right c1
                  (Entails.sepExists_right c2 (Entails.sepExists_right epoch
                    (Entails.refl _))))))))))))))))
  have h1 : (stA ↦₆₄ 10#64) ⊢ memRegion stA 8 := Drop.pointsTo64_entails_memRegion stA 10#64
  have hsplit : memRegion stA chunkedStatesSize =
      memRegion stA 8 ∗
      memRegion (stA + 8#64) polyEncoderSize ∗
      memRegion (stA + 408#64) 128 ∗
      memRegion (stA + 536#64) 392 := by
    change memRegion stA 928 =
      memRegion stA 8 ∗ memRegion (stA + 8#64) 400 ∗
      memRegion (stA + 408#64) 128 ∗ memRegion (stA + 536#64) 392
    rw [ProofLib.memRegion_split' (b := stA) (n := 8) (k := 920)
          (b' := stA + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := stA + 8#64) (n := 400) (k := 520)
          (b' := stA + 408#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := stA + 408#64) (n := 128) (k := 392)
          (b' := stA + 536#64) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  refine Entails.trans (Entails.of_eq (show _ =
    (stA ↦₆₄ 10#64) ∗
    memRegion (stA + 8#64) polyEncoderSize ∗
    (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     ((stA + 504#64) ↦₆₄ c0) ∗ ((stA + 512#64) ↦₆₄ c1) ∗ ((stA + 520#64) ↦₆₄ c2) ∗
     ((stA + 528#64) ↦₆₄ epoch)) ∗
    memRegion (stA + 536#64) 392 by ac_rfl)) ?_
  exact sepConj_mono h1 (sepConj_mono (Entails.refl _) (sepConj_mono hc16 (Entails.refl _)))

/-- Scratch stack cells used in Arm 8 (`ekReceivedCt1Sampled`) outside `epilogueStagingCells`. -/
def ekReceivedScratchCells (sp : BitVec 64)
    (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64) : SepProp :=
  ((sp - 1360#64) ↦₆₄ t0) ∗ ((sp - 1352#64) ↦₆₄ t1) ∗
  ((sp - 1344#64) ↦₆₄ t2) ∗ ((sp - 1336#64) ↦₆₄ t3) ∗
  ((sp - 1328#64) ↦₆₄ t4) ∗ ((sp - 1320#64) ↦₆₄ t5) ∗
  ((sp - 1312#64) ↦₆₄ t6) ∗ ((sp - 1304#64) ↦₆₄ t7) ∗
  ((sp - 1296#64) ↦₆₄ t8) ∗ ((sp - 1288#64) ↦₆₄ t9) ∗
  ((sp - 1280#64) ↦₆₄ t10) ∗ ((sp - 1272#64) ↦₆₄ t11) ∗
  ((sp - 1264#64) ↦₆₄ t12) ∗ ((sp - 1256#64) ↦₆₄ t13) ∗
  ((sp - 1248#64) ↦₆₄ t14) ∗ ((sp - 1240#64) ↦₆₄ t15) ∗
  ((sp - 480#64) ↦₆₄ u0) ∗ ((sp - 472#64) ↦₆₄ u1) ∗
  ((sp - 464#64) ↦₆₄ u2) ∗ ((sp - 456#64) ↦₆₄ u3) ∗
  ((sp - 448#64) ↦₆₄ u4) ∗ ((sp - 440#64) ↦₆₄ u5) ∗
  ((sp - 256#64) ↦₆₄ v0) ∗ ((sp - 248#64) ↦₆₄ v1) ∗
  ((sp - 240#64) ↦₆₄ v2) ∗ ((sp - 232#64) ↦₆₄ v3) ∗
  ((sp - 224#64) ↦₆₄ v4) ∗ ((sp - 216#64) ↦₆₄ v5)

theorem memRegion_ekReceived_scratch_split (sp : BitVec 64) :
    memRegion (sp - 1360#64) 880 ∗
    memRegion (sp - 480#64) 176 ∗
    memRegion (sp - 256#64) 160 ⊢
      ∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64,
      ∃∗ t4 : BitVec 64, ∃∗ t5 : BitVec 64, ∃∗ t6 : BitVec 64, ∃∗ t7 : BitVec 64,
      ∃∗ t8 : BitVec 64, ∃∗ t9 : BitVec 64, ∃∗ t10 : BitVec 64, ∃∗ t11 : BitVec 64,
      ∃∗ t12 : BitVec 64, ∃∗ t13 : BitVec 64, ∃∗ t14 : BitVec 64, ∃∗ t15 : BitVec 64,
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
      ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ekReceivedScratchCells sp
          t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
          u0 u1 u2 u3 u4 u5
          v0 v1 v2 v3 v4 v5 ∗
        memRegion (sp - 1232#64) 56 ∗
        memRegion (sp - 1176#64) 696 ∗
        memRegion (sp - 432#64) 128 ∗
        memRegion (sp - 208#64) 112 := by
  have h880 : memRegion (sp - 1360#64) 880 =
      ProofLib.cells (sp - 1360#64) 16 ∗
      memRegion (sp - 1232#64) 56 ∗
      memRegion (sp - 1176#64) 696 := by
    rw [ProofLib.memRegion_split' (b := sp - 1360#64) (n := 128) (k := 752)
          (b' := sp - 1232#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 1232#64) (n := 56) (k := 696)
          (b' := sp - 1176#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (sp - 1360#64) 16 (by decide)]
  have h176 : memRegion (sp - 480#64) 176 =
      ProofLib.cells (sp - 480#64) 6 ∗ memRegion (sp - 432#64) 128 := by
    rw [ProofLib.memRegion_split' (b := sp - 480#64) (n := 48) (k := 128)
          (b' := sp - 432#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (sp - 480#64) 6 (by decide)]
  have h160 : memRegion (sp - 256#64) 160 =
      ProofLib.cells (sp - 256#64) 6 ∗ memRegion (sp - 208#64) 112 := by
    rw [ProofLib.memRegion_split' (b := sp - 256#64) (n := 48) (k := 112)
          (b' := sp - 208#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (sp - 256#64) 6 (by decide)]
  rw [h880, h176, h160]
  unfold ekReceivedScratchCells
  cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  apply Entails.sepExists_elim; intro v0
  apply Entails.sepExists_elim; intro v1
  apply Entails.sepExists_elim; intro v2
  apply Entails.sepExists_elim; intro v3
  apply Entails.sepExists_elim; intro v4
  apply Entails.sepExists_elim; intro v5
  apply Entails.sepExists_elim; intro u0
  apply Entails.sepExists_elim; intro u1
  apply Entails.sepExists_elim; intro u2
  apply Entails.sepExists_elim; intro u3
  apply Entails.sepExists_elim; intro u4
  apply Entails.sepExists_elim; intro u5
  apply Entails.sepExists_elim; intro t0
  apply Entails.sepExists_elim; intro t1
  apply Entails.sepExists_elim; intro t2
  apply Entails.sepExists_elim; intro t3
  apply Entails.sepExists_elim; intro t4
  apply Entails.sepExists_elim; intro t5
  apply Entails.sepExists_elim; intro t6
  apply Entails.sepExists_elim; intro t7
  apply Entails.sepExists_elim; intro t8
  apply Entails.sepExists_elim; intro t9
  apply Entails.sepExists_elim; intro t10
  apply Entails.sepExists_elim; intro t11
  apply Entails.sepExists_elim; intro t12
  apply Entails.sepExists_elim; intro t13
  apply Entails.sepExists_elim; intro t14
  apply Entails.sepExists_elim; intro t15
  refine Entails.sepExists_right t0 (Entails.sepExists_right t1
    (Entails.sepExists_right t2 (Entails.sepExists_right t3
      (Entails.sepExists_right t4 (Entails.sepExists_right t5
        (Entails.sepExists_right t6 (Entails.sepExists_right t7
          (Entails.sepExists_right t8 (Entails.sepExists_right t9
            (Entails.sepExists_right t10 (Entails.sepExists_right t11
              (Entails.sepExists_right t12 (Entails.sepExists_right t13
                (Entails.sepExists_right t14 (Entails.sepExists_right t15
                  (Entails.sepExists_right u0 (Entails.sepExists_right u1
                    (Entails.sepExists_right u2 (Entails.sepExists_right u3
                      (Entails.sepExists_right u4 (Entails.sepExists_right u5
                        (Entails.sepExists_right v0 (Entails.sepExists_right v1
                          (Entails.sepExists_right v2 (Entails.sepExists_right v3
                            (Entails.sepExists_right v4 (Entails.sepExists_right v5
                              (Entails.of_eq (by ac_rfl)))))))))))))))))))))))))))))

theorem ekReceivedScratchCells_entails_memRegions (sp : BitVec 64)
    (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64) :
    ekReceivedScratchCells sp
      t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
      u0 u1 u2 u3 u4 u5
      v0 v1 v2 v3 v4 v5 ∗
    (((sp - 1232#64) ↦₆₄ e0) ∗ ((sp - 1224#64) ↦₆₄ e1) ∗
     ((sp - 1216#64) ↦₆₄ e2) ∗ ((sp - 1208#64) ↦₆₄ e3) ∗
     ((sp - 1200#64) ↦₆₄ e4) ∗ ((sp - 1192#64) ↦₆₄ e5) ∗
     ((sp - 1184#64) ↦₆₄ e6)) ∗
    memRegion (sp - 1176#64) 696 ∗
    memRegion (sp - 432#64) 128 ∗
    memRegion (sp - 208#64) 112 ⊢
    memRegion (sp - 1360#64) 880 ∗
    memRegion (sp - 480#64) 176 ∗
    memRegion (sp - 256#64) 160 := by
  have ht16 :
      ((sp - 1360#64) ↦₆₄ t0) ∗ ((sp - 1352#64) ↦₆₄ t1) ∗
      ((sp - 1344#64) ↦₆₄ t2) ∗ ((sp - 1336#64) ↦₆₄ t3) ∗
      ((sp - 1328#64) ↦₆₄ t4) ∗ ((sp - 1320#64) ↦₆₄ t5) ∗
      ((sp - 1312#64) ↦₆₄ t6) ∗ ((sp - 1304#64) ↦₆₄ t7) ∗
      ((sp - 1296#64) ↦₆₄ t8) ∗ ((sp - 1288#64) ↦₆₄ t9) ∗
      ((sp - 1280#64) ↦₆₄ t10) ∗ ((sp - 1272#64) ↦₆₄ t11) ∗
      ((sp - 1264#64) ↦₆₄ t12) ∗ ((sp - 1256#64) ↦₆₄ t13) ∗
      ((sp - 1248#64) ↦₆₄ t14) ∗ ((sp - 1240#64) ↦₆₄ t15) ⊢
      memRegion (sp - 1360#64) 128 := by
    rw [ProofLib.memRegion_cells (sp - 1360#64) 16 (by decide)]
    cells_unfold
    exact Entails.sepExists_right t0 (Entails.sepExists_right t1
      (Entails.sepExists_right t2 (Entails.sepExists_right t3
        (Entails.sepExists_right t4 (Entails.sepExists_right t5
          (Entails.sepExists_right t6 (Entails.sepExists_right t7
            (Entails.sepExists_right t8 (Entails.sepExists_right t9
              (Entails.sepExists_right t10 (Entails.sepExists_right t11
                (Entails.sepExists_right t12 (Entails.sepExists_right t13
                  (Entails.sepExists_right t14 (Entails.sepExists_right t15
                    (Entails.refl _))))))))))))))))
  have he56 :
      ((sp - 1232#64) ↦₆₄ e0) ∗ ((sp - 1224#64) ↦₆₄ e1) ∗
      ((sp - 1216#64) ↦₆₄ e2) ∗ ((sp - 1208#64) ↦₆₄ e3) ∗
      ((sp - 1200#64) ↦₆₄ e4) ∗ ((sp - 1192#64) ↦₆₄ e5) ∗
      ((sp - 1184#64) ↦₆₄ e6) ⊢
      memRegion (sp - 1232#64) 56 := by
    rw [ProofLib.memRegion_cells (sp - 1232#64) 7 (by decide)]
    cells_unfold
    exact Entails.sepExists_right e0 (Entails.sepExists_right e1
      (Entails.sepExists_right e2 (Entails.sepExists_right e3
        (Entails.sepExists_right e4 (Entails.sepExists_right e5
          (Entails.sepExists_right e6 (Entails.refl _)))))))
  have hu6 :
      ((sp - 480#64) ↦₆₄ u0) ∗ ((sp - 472#64) ↦₆₄ u1) ∗
      ((sp - 464#64) ↦₆₄ u2) ∗ ((sp - 456#64) ↦₆₄ u3) ∗
      ((sp - 448#64) ↦₆₄ u4) ∗ ((sp - 440#64) ↦₆₄ u5) ⊢
      memRegion (sp - 480#64) 48 := by
    rw [ProofLib.memRegion_cells (sp - 480#64) 6 (by decide)]
    cells_unfold
    exact Entails.sepExists_right u0 (Entails.sepExists_right u1
      (Entails.sepExists_right u2 (Entails.sepExists_right u3
        (Entails.sepExists_right u4 (Entails.sepExists_right u5 (Entails.refl _))))))
  have hv6 :
      ((sp - 256#64) ↦₆₄ v0) ∗ ((sp - 248#64) ↦₆₄ v1) ∗
      ((sp - 240#64) ↦₆₄ v2) ∗ ((sp - 232#64) ↦₆₄ v3) ∗
      ((sp - 224#64) ↦₆₄ v4) ∗ ((sp - 216#64) ↦₆₄ v5) ⊢
      memRegion (sp - 256#64) 48 := by
    rw [ProofLib.memRegion_cells (sp - 256#64) 6 (by decide)]
    cells_unfold
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1
      (Entails.sepExists_right v2 (Entails.sepExists_right v3
        (Entails.sepExists_right v4 (Entails.sepExists_right v5 (Entails.refl _))))))
  have h880 : memRegion (sp - 1360#64) 880 =
      memRegion (sp - 1360#64) 128 ∗
      memRegion (sp - 1232#64) 56 ∗
      memRegion (sp - 1176#64) 696 := by
    rw [ProofLib.memRegion_split' (b := sp - 1360#64) (n := 128) (k := 752)
          (b' := sp - 1232#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 1232#64) (n := 56) (k := 696)
          (b' := sp - 1176#64) rfl (by bv_omega) (by decide)]
  have h176 : memRegion (sp - 480#64) 176 =
      memRegion (sp - 480#64) 48 ∗ memRegion (sp - 432#64) 128 :=
    ProofLib.memRegion_split' (b := sp - 480#64) (n := 48) (k := 128)
      (b' := sp - 432#64) rfl (by bv_omega) (by decide)
  have h160 : memRegion (sp - 256#64) 160 =
      memRegion (sp - 256#64) 48 ∗ memRegion (sp - 208#64) 112 :=
    ProofLib.memRegion_split' (b := sp - 256#64) (n := 48) (k := 112)
      (b' := sp - 208#64) rfl (by bv_omega) (by decide)
  rw [h880, h176, h160]
  unfold ekReceivedScratchCells
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp - 1360#64) ↦₆₄ t0) ∗ ((sp - 1352#64) ↦₆₄ t1) ∗
     ((sp - 1344#64) ↦₆₄ t2) ∗ ((sp - 1336#64) ↦₆₄ t3) ∗
     ((sp - 1328#64) ↦₆₄ t4) ∗ ((sp - 1320#64) ↦₆₄ t5) ∗
     ((sp - 1312#64) ↦₆₄ t6) ∗ ((sp - 1304#64) ↦₆₄ t7) ∗
     ((sp - 1296#64) ↦₆₄ t8) ∗ ((sp - 1288#64) ↦₆₄ t9) ∗
     ((sp - 1280#64) ↦₆₄ t10) ∗ ((sp - 1272#64) ↦₆₄ t11) ∗
     ((sp - 1264#64) ↦₆₄ t12) ∗ ((sp - 1256#64) ↦₆₄ t13) ∗
     ((sp - 1248#64) ↦₆₄ t14) ∗ ((sp - 1240#64) ↦₆₄ t15)) ∗
    (((sp - 1232#64) ↦₆₄ e0) ∗ ((sp - 1224#64) ↦₆₄ e1) ∗
     ((sp - 1216#64) ↦₆₄ e2) ∗ ((sp - 1208#64) ↦₆₄ e3) ∗
     ((sp - 1200#64) ↦₆₄ e4) ∗ ((sp - 1192#64) ↦₆₄ e5) ∗
     ((sp - 1184#64) ↦₆₄ e6)) ∗
    (((sp - 480#64) ↦₆₄ u0) ∗ ((sp - 472#64) ↦₆₄ u1) ∗
     ((sp - 464#64) ↦₆₄ u2) ∗ ((sp - 456#64) ↦₆₄ u3) ∗
     ((sp - 448#64) ↦₆₄ u4) ∗ ((sp - 440#64) ↦₆₄ u5)) ∗
    (((sp - 256#64) ↦₆₄ v0) ∗ ((sp - 248#64) ↦₆₄ v1) ∗
     ((sp - 240#64) ↦₆₄ v2) ∗ ((sp - 232#64) ↦₆₄ v3) ∗
     ((sp - 224#64) ↦₆₄ v4) ∗ ((sp - 216#64) ↦₆₄ v5)) ∗
    (memRegion (sp - 1176#64) 696 ∗
     memRegion (sp - 432#64) 128 ∗
     memRegion (sp - 208#64) 112) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono ht16 (sepConj_mono he56 (sepConj_mono hu6 (sepConj_mono hv6 (Entails.refl _))))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem outWords28_entails_ekReceivedCt1Sampled (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (es0 es1 es2 ek0 ek1 ek2 : BitVec 64)
    (c0 c1 c2 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      0x8000000000000008#64
      es0 es1 es2 ek0 ek1 ek2
      c0 c1 c2
      a0 a1 a2 a3 a4 a5 s.uc.epoch
      e0 e1 e2 e3 e4 e5 e6
      w192 w200 w208 w216 ∗
    protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
    vecU8Heap A es0 es1 es2 s.uc.es ∗
    vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
    vecU8Heap A c0 c1 c2 s.uc.ct1 ⊢
    optProtoInnerStateAt A out (States.ekReceivedCt1Sampled s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendCt.EkReceivedCt1Sampled.into_pb,
    Unchunked.SendCt.Ct1SentEkReceived.into_pb,
    optProtoInnerStateAt, protoInnerStateAt, protoChunkedEkReceivedCt1SampledAt,
    optProtoUnchunkedCt1SentEkReceivedAt, protoUnchunkedCt1SentEkReceivedAt,
    optProtoPolynomialEncoderAt, Option.map,
    spqrPolyApi, pbToProtoPolyEncoder, protoPolyEncoderToPb,
    optProtoAuthenticatorAt_some_into_pb]
  have hes := vecU8_of_words_heap A (out + 8#64) es0 es1 es2 s.uc.es
  have hek := vecU8_of_words_heap A (out + 32#64) ek0 ek1 ek2 s.uc.ek
  have hct1 := vecU8_of_words_heap A (out + 56#64) c0 c1 c2 s.uc.ct1
  have hauth := authenticatorAt_of_words_heap A (out + 80#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  have henc := protoPolynomialEncoder_of_words_heap A (out + 136#64)
    e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb
  have hpad :
      ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
      ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 192#64) 32 := by
    rw [ProofLib.memRegion_cells (out + 192#64) 4 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w192 (Entails.sepExists_right w200
      (Entails.sepExists_right w208 (Entails.sepExists_right w216 (Entails.refl _))))
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hes hek hct1 hauth henc ⊢
  unfold outWords28
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 0x8000000000000008#64) ∗
    (((((out + 8#64) ↦₆₄ es0) ∗ ((out + 16#64) ↦₆₄ es1) ∗ ((out + 24#64) ↦₆₄ es2) ∗
       vecU8Heap A es0 es1 es2 s.uc.es) ∗
      (((out + 32#64) ↦₆₄ ek0) ∗ ((out + 40#64) ↦₆₄ ek1) ∗ ((out + 48#64) ↦₆₄ ek2) ∗
       vecU8Heap A ek0 ek1 ek2 s.uc.ek) ∗
      (((out + 56#64) ↦₆₄ c0) ∗ ((out + 64#64) ↦₆₄ c1) ∗ ((out + 72#64) ↦₆₄ c2) ∗
       vecU8Heap A c0 c1 c2 s.uc.ct1) ∗
      (((out + 80#64) ↦₆₄ a0) ∗ ((out + 88#64) ↦₆₄ a1) ∗ ((out + 96#64) ↦₆₄ a2) ∗
       ((out + 104#64) ↦₆₄ a3) ∗ ((out + 112#64) ↦₆₄ a4) ∗ ((out + 120#64) ↦₆₄ a5) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
      ((out + 128#64) ↦₆₄ s.uc.epoch)) ∗
     (((out + 136#64) ↦₆₄ e0) ∗ ((out + 144#64) ↦₆₄ e1) ∗ ((out + 152#64) ↦₆₄ e2) ∗
      ((out + 160#64) ↦₆₄ e3) ∗ ((out + 168#64) ↦₆₄ e4) ∗ ((out + 176#64) ↦₆₄ e5) ∗
      ((out + 184#64) ↦₆₄ e6) ∗
      protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb)) ∗
    (((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
     ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216)) by ac_rfl)) ?_
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono
      (sepConj_mono
        (sepConj_mono hes (sepConj_mono hek (sepConj_mono hct1 (sepConj_mono hauth (Entails.refl _)))))
        henc)
      hpad)

end CryptoVerification.SpqrV1.States.IntoPb
