/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Varint
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Proof -- shake: keep

/-!
# `spqr::recv`: Message Preamble & Common Epilogue

48-byte `recvResultExactKeyAt` folding, stack-frame prologue/epilogue (`+1040..+1072`),
`Err(MsgDecode)` exit (`+276..+288`), and LEB128 varint decoding loops (`+0..+312`) for
`spqr::recv` (`0x5462c`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Top.DecodeState

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Result buffer (`ret`, 48 bytes) folding for `recvResultExactKeyAt` -/

/-- The 48-byte `recv` result buffer `ret`, cut at the four 8-byte words touched on the `Ok` and
    `Err` paths (`+0`, `+8`, `+16`, `+24`). -/
theorem ret_48_split (r : BitVec 64) :
    memRegion r 48 =
      (∃∗ r0 : BitVec 64, r ↦₆₄ r0) ∗
      (∃∗ r1 : BitVec 64, (r + 8#64) ↦₆₄ r1) ∗
      (∃∗ r2 : BitVec 64, (r + 16#64) ↦₆₄ r2) ∗
      (∃∗ r3 : BitVec 64, (r + 24#64) ↦₆₄ r3) ∗
      memRegion (r + 32#64) 16 := by
  have hs : ∀ (b : BitVec 64) (k : Nat), k ≤ 40 →
      memRegion b (8 + k) = memRegion b 8 ∗ memRegion (b + 8#64) k :=
    fun b k _ => memRegion_split' rfl rfl (by omega)
  rw [hs r 40 (by decide), hs _ 32 (by decide), hs _ 24 (by decide), hs _ 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight]

/-- `recvResultExactKeyAt A r (.ok ([], none))` folded from `0, 1, 0, -1`. -/
theorem recv_ok_empty_foldX (A : RustAlloc) (r : BitVec 64) :
    ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
      ((r + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (r + 32#64) 16) ⊢
    recvResultExactKeyAt A r (.ok ([], none)) := by
  have hv : ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗ ((r + 16#64) ↦₆₄ 0#64)) ⊢ vecU8 A r [] := by
    unfold vecU8
    refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
    refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
    simp only [vecU8At, vecHeader, List.length_nil]
    split
    · rw [sepConj_emp, sepConj_comm _ ⌜_⌝]
      refine Entails.pure_right ?_ (Entails.refl _)
      exact ⟨Nat.zero_le _, by decide, by decide⟩
    · exact absurd rfl ‹_›
  simp only [recvResultExactKeyAt, optKeyBytesAt]
  refine Entails.trans (Entails.of_eq (Q := ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗
      ((r + 16#64) ↦₆₄ 0#64)) ∗ (((r + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      memRegion (r + 32#64) 16)) (by simp only [sepConj_assoc])) ?_
  exact sepConj_mono hv (Entails.of_eq (by rw [BitVec.add_assoc]; rfl))

/-- `recvResultExactKeyAt A r (.error false)` for `Err(MsgDecode)` (`w8 = 2#64`). -/
theorem recv_err_msgDecode_foldX (A : RustAlloc) (r r2 r3 : BitVec 64) :
    ((r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((r + 8#64) ↦₆₄ 2#64) ∗
      ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗ memRegion (r + 32#64) 16) ⊢
    recvResultExactKeyAt A r (.error false) := by
  simp only [recvResultExactKeyAt]
  have h8 : ((r + 8#64) ↦₆₄ 2#64) ⊢ ((r + 8#64) ↦₈ 2#8) ∗ memRegion (r + 9#64) 7 := by
    rw [pointsTo64_eq_pointsToBytes]
    change ((r + 8#64) ↦ₛ (2#8 :: [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8])) ⊢ _
    rw [pointsToBytes_cons, show r + 8#64 + 1#64 = r + 9#64 by bv_arith]
    exact sepConj_mono_right (pointsToBytes_entails_memRegion _ _)
  have htail :
      memRegion (r + 9#64) 7 ∗ ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗
        memRegion (r + 32#64) 16 ⊢
      memRegion (r + 9#64) 39 := by
    rw [show (39 : Nat) = 7 + (8 + (8 + 16)) by decide,
        memRegion_split (r + 9#64) 7 32 (by decide),
        show r + 9#64 + 7#64 = r + 16#64 by bv_arith,
        memRegion_split (r + 16#64) 8 24 (by decide),
        show r + 16#64 + 8#64 = r + 24#64 by bv_arith,
        memRegion_split (r + 24#64) 8 16 (by decide),
        show r + 24#64 + 8#64 = r + 32#64 by bv_arith]
    exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_left h8) ?_
  rw [sepConj_assoc]
  refine Entails.trans (sepConj_mono_right htail) ?_
  refine sepConj_mono_left ?_
  refine Entails.trans ?_ (Entails.sepExists_intro 2#8)
  exact Entails.pure_right (by decide) (Entails.refl _)

/-- Split the second 8-byte word `r + 8` of `ret` into its leading byte `r + 8` and 7 trailing
    bytes `r + 9 .. r + 16` (for `strb w8, [x19, #0x8]` error paths). -/
theorem ret8_expose_byte (r r1 : BitVec 64) :
    ((r + 8#64) ↦₆₄ r1) ⊢
      ∃∗ b : BitVec 8, ((r + 8#64) ↦₈ b) ∗ memRegion (r + 9#64) 7 := by
  refine Entails.trans (pointsTo64_entails_memRegion (r + 8#64) r1) ?_
  rw [memRegion_split (r + 8#64) 1 7 (by decide),
      show r + 8#64 + 1#64 = r + 9#64 by bv_arith,
      ProofLib.memRegion_one (r + 8#64), sepExists_sepConj_left]
  exact Entails.refl _

/-- Fold `Err(sd)` at `ret` when `r + 8` has been written via `strb` (`code : BitVec 8` with
    `code = 0#8 ↔ sd = true`). -/
theorem recv_err_byte_foldX (A : RustAlloc) (r r2 r3 : BitVec 64) (code : BitVec 8) (sd : Bool)
    (hsd : code = 0#8 ↔ sd = true) :
    ((r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((r + 8#64) ↦₈ code) ∗ memRegion (r + 9#64) 7 ∗
      ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗ memRegion (r + 32#64) 16) ⊢
    recvResultExactKeyAt A r (.error sd) := by
  simp only [recvResultExactKeyAt]
  have htail :
      memRegion (r + 9#64) 7 ∗ ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗
        memRegion (r + 32#64) 16 ⊢
      memRegion (r + 9#64) 39 := by
    rw [show (39 : Nat) = 7 + (8 + (8 + 16)) by decide,
        memRegion_split (r + 9#64) 7 32 (by decide),
        show r + 9#64 + 7#64 = r + 16#64 by bv_arith,
        memRegion_split (r + 16#64) 8 24 (by decide),
        show r + 16#64 + 8#64 = r + 24#64 by bv_arith,
        memRegion_split (r + 24#64) 8 16 (by decide),
        show r + 24#64 + 8#64 = r + 32#64 by bv_arith]
    exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_right htail) ?_
  refine sepConj_mono_left ?_
  refine Entails.trans ?_ (Entails.sepExists_intro code)
  exact Entails.pure_right hsd (Entails.refl _)

/-! ## Exposing the `m.remaining` slice `(x24 ↦ₛ m.remaining)` inside `msg.at A` -/

/-- Validity invariant relating `(x24 = ptr_rem, x23 = rem.length)` after `msgPreamble` to
    `msg`: either `msg.bytes = []` and `rem = []`, or `msg.bytes = pre ++ rem` with `ptr_rem =
    msg.ptr + pre.length`. -/
def MsgRemValid (msg : VecArg) (ptr_rem : BitVec 64) (rem : List (BitVec 8)) : Prop :=
  (rem = [] ∧ msg.bytes = []) ∨
    ∃ pre : List (BitVec 8),
      msg.bytes = pre ++ rem ∧ ptr_rem = msg.ptr + BitVec.ofNat 64 pre.length

/-- Frame of `msg.at A` when `(ptr_rem ↦ₛ rem)` is exposed for `Message::deserialize`. -/
def msgRemFrame (A : RustAlloc) (msg : VecArg) (ptr_rem : BitVec 64) (rem : List (BitVec 8)) : SepProp :=
  ∃∗ pre : List (BitVec 8),
    ⌜(rem = [] ∧ pre = msg.bytes) ∨
      (msg.cap ≠ 0 ∧ msg.bytes = pre ++ rem ∧ ptr_rem = msg.ptr + BitVec.ofNat 64 pre.length)⌝ ∗
    ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
    vecHeader msg.v msg.cap msg.ptr (BitVec.ofNat 64 msg.bytes.length) ∗
    if msg.cap = 0 then emp
    else A.live msg.ptr msg.cap.toNat 1 ∗ (msg.ptr ↦ₛ pre) ∗
      memRegion (msg.ptr + BitVec.ofNat 64 msg.bytes.length) (msg.cap.toNat - msg.bytes.length)

theorem msg_expose_rem (A : RustAlloc) (msg : VecArg) (ptr_rem : BitVec 64) (rem : List (BitVec 8))
    (hvalid : MsgRemValid msg ptr_rem rem) :
    msg.at A ⊢ (ptr_rem ↦ₛ rem) ∗ msgRemFrame A msg ptr_rem rem := by
  simp only [VecArg.at, vecU8At, msgRemFrame]
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hp => ?_
  by_cases hcap : msg.cap = 0
  · have hlen0 : msg.bytes.length = 0 := by
      have hc0 : msg.cap.toNat = 0 := by rw [hcap]; rfl
      omega
    have hnil : msg.bytes = [] := List.eq_nil_of_length_eq_zero hlen0
    have hrem0 : rem = [] := by
      rcases hvalid with ⟨hr, _⟩ | ⟨pre, hsplit, _⟩
      · exact hr
      · rw [hnil] at hsplit
        exact (List.append_eq_nil_iff.mp hsplit.symm).2
    subst hrem0
    rw [pointsToBytes_nil, emp_sepConj]
    refine Entails.sepExists_right msg.bytes ?_
    refine Entails.pure_right (Or.inl ⟨rfl, rfl⟩) (Entails.pure_right hp ?_)
    exact Entails.refl _
  · rcases hvalid with ⟨rfl, _⟩ | ⟨pre, hsplit, hptr⟩
    · rw [pointsToBytes_nil, emp_sepConj]
      refine Entails.sepExists_right msg.bytes ?_
      refine Entails.pure_right (Or.inl ⟨rfl, rfl⟩) (Entails.pure_right hp ?_)
      exact Entails.refl _
    · rw [sepExists_sepConj_right]
      refine Entails.sepExists_right pre ?_
      rw [ite_eq_right_iff.mpr (fun h => (hcap h).elim),
          ite_eq_right_iff.mpr (fun h => (hcap h).elim)]
      have hpts : (msg.ptr ↦ₛ msg.bytes) = (msg.ptr ↦ₛ pre) ∗ (ptr_rem ↦ₛ rem) := by
        rw [hsplit, pointsToBytes_append, ← hptr]
      rw [hpts]
      have hcomm :
          vecHeader msg.v msg.cap msg.ptr (BitVec.ofNat 64 msg.bytes.length) ∗
            (A.live msg.ptr msg.cap.toNat 1 ∗ (msg.ptr ↦ₛ pre ∗ ptr_rem ↦ₛ rem) ∗
              memRegion (msg.ptr + BitVec.ofNat 64 msg.bytes.length) (msg.cap.toNat - msg.bytes.length)) =
          (ptr_rem ↦ₛ rem) ∗
            (vecHeader msg.v msg.cap msg.ptr (BitVec.ofNat 64 msg.bytes.length) ∗
              (A.live msg.ptr msg.cap.toNat 1 ∗ (msg.ptr ↦ₛ pre) ∗
                memRegion (msg.ptr + BitVec.ofNat 64 msg.bytes.length) (msg.cap.toNat - msg.bytes.length))) := by
        ac_rfl
      rw [hcomm]
      refine sepConj_mono_right ?_
      refine Entails.pure_right (Or.inr ⟨hcap, hsplit, hptr⟩) (Entails.pure_right hp ?_)
      exact Entails.refl _

theorem msg_unexpose_rem (A : RustAlloc) (msg : VecArg) (ptr_rem : BitVec 64) (rem : List (BitVec 8)) :
    ((ptr_rem ↦ₛ rem) ∗ msgRemFrame A msg ptr_rem rem) ⊢ msg.at A := by
  simp only [VecArg.at, vecU8At, msgRemFrame, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun pre => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hcase => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hp => ?_
  conv_rhs => rw [sepConj_pure_left_comm]
  refine Entails.pure_right hp ?_
  rcases hcase with ⟨rfl, rfl⟩ | ⟨hcap, hsplit, hptr⟩
  · rw [pointsToBytes_nil, emp_sepConj]
    exact Entails.refl _
  · rw [ite_eq_right_iff.mpr (fun h => (hcap h).elim),
        ite_eq_right_iff.mpr (fun h => (hcap h).elim)]
    have hpts : (msg.ptr ↦ₛ msg.bytes) = (msg.ptr ↦ₛ pre) ∗ (ptr_rem ↦ₛ rem) := by
      rw [hsplit, pointsToBytes_append, ← hptr]
    rw [hpts]
    exact Entails.of_eq (by ac_rfl)

/-! ## Prologue & Epilogue Stack Frame Lemmas (`fsp = s0.sp - 0x1380`) -/

theorem memRegion_16_split (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ v0 : BitVec 64, a ↦₆₄ v0) ∗ (∃∗ v1 : BitVec 64, (a + 8#64) ↦₆₄ v1) := by
  rw [show (16 : Nat) = 8 + 8 by rfl, memRegion_split a 8 8 (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64)]

theorem prologue_frame_split (fsp : BitVec 64) :
    memRegion fsp 0x1320 ∗ memRegion (fsp + 0x1320#64) 96 ⊢
      memRegion fsp 0x320 ∗
      (∃∗ probe : BitVec 64, (fsp + 0x320#64) ↦₆₄ probe) ∗
      memRegion (fsp + 0x328#64) 0xff8 ∗
      (∃∗ s29 : BitVec 64, (fsp + 0x1320#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (fsp + 0x1328#64) ↦₆₄ s30) ∗
      (∃∗ s28 : BitVec 64, (fsp + 0x1330#64) ↦₆₄ s28) ∗
      (∃∗ s27 : BitVec 64, (fsp + 0x1338#64) ↦₆₄ s27) ∗
      (∃∗ s26 : BitVec 64, (fsp + 0x1340#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (fsp + 0x1348#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (fsp + 0x1350#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (fsp + 0x1358#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (fsp + 0x1360#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (fsp + 0x1368#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (fsp + 0x1370#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (fsp + 0x1378#64) ↦₆₄ s19) := by
  have h1 : memRegion fsp 0x1320 =
      memRegion fsp 0x320 ∗ (∃∗ probe : BitVec 64, (fsp + 0x320#64) ↦₆₄ probe) ∗
      memRegion (fsp + 0x328#64) 0xff8 := by
    rw [show (0x1320 : Nat) = 0x320 + (8 + 0xff8) by decide,
        memRegion_split fsp 0x320 (8 + 0xff8) (by decide),
        memRegion_split (fsp + 0x320#64) 8 0xff8 (by decide),
        show fsp + 0x320#64 + 8#64 = fsp + 0x328#64 by bv_arith,
        ProofLib.memRegion_eight (fsp + 0x320#64)]
  have h2 : memRegion (fsp + 0x1320#64) 96 =
      (∃∗ s29 : BitVec 64, (fsp + 0x1320#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (fsp + 0x1328#64) ↦₆₄ s30) ∗
      (∃∗ s28 : BitVec 64, (fsp + 0x1330#64) ↦₆₄ s28) ∗
      (∃∗ s27 : BitVec 64, (fsp + 0x1338#64) ↦₆₄ s27) ∗
      (∃∗ s26 : BitVec 64, (fsp + 0x1340#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (fsp + 0x1348#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (fsp + 0x1350#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (fsp + 0x1358#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (fsp + 0x1360#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (fsp + 0x1368#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (fsp + 0x1370#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (fsp + 0x1378#64) ↦₆₄ s19) := by
    rw [show (96 : Nat) = 16 + (16 + (16 + (16 + (16 + 16)))) by decide,
        memRegion_split (fsp + 0x1320#64) 16 80 (by decide),
        memRegion_split (fsp + 0x1320#64 + 16#64) 16 64 (by decide),
        memRegion_split (fsp + 0x1320#64 + 16#64 + 16#64) 16 48 (by decide),
        memRegion_split (fsp + 0x1320#64 + 16#64 + 16#64 + 16#64) 16 32 (by decide),
        memRegion_split (fsp + 0x1320#64 + 16#64 + 16#64 + 16#64 + 16#64) 16 16 (by decide)]
    simp only [memRegion_16_split, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [h1, h2]
  exact Entails.of_eq (by ac_rfl)

theorem prologue_frame_unsplit (fsp probe : BitVec 64) :
    memRegion fsp 0x320 ∗ ((fsp + 0x320#64) ↦₆₄ probe) ∗ memRegion (fsp + 0x328#64) 0xff8 ⊢
      memRegion fsp 0x1320 := by
  rw [show (0x1320 : Nat) = 0x320 + (8 + 0xff8) by decide,
      memRegion_split fsp 0x320 (8 + 0xff8) (by decide),
      memRegion_split (fsp + 0x320#64) 8 0xff8 (by decide),
      show fsp + 0x320#64 + 8#64 = fsp + 0x328#64 by bv_arith]
  exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

/-! ## Common Epilogue (`+1040 .. +1072`, `0x54a3c .. 0x54a5c`) -/

noncomputable def spqrRecvEntry (b : BitVec 64) (ext : String → Option (State → State)) : BitVec 64 :=
  (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName

theorem spqrRecvEntry_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName = spqrRecvEntry b ext := rfl

/-- Core postcondition of `spqr::recv` (with `spqrRecvRoAt b` included and `TokenInit img ∗
    logOff img` framed in `R`), without the `¬ M.recvPanics st msg` conjunct. -/
abbrev spqrRecvCorePost0 (A : RustAlloc) (b : BitVec 64) (M : SpqrRecvModel)
    (st msg : VecArg) (ret : BitVec 64) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗
    spqrRecvRoAt b ∗
    st.at A ∗
    msg.at A ∗
    recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
    A.pool ∗
    stackAt s0.sp spqrRecvStack

abbrev spqrRecvPost0 (A : RustAlloc) (b : BitVec 64) (M : SpqrRecvModel)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spqrRecvCorePost0 A b M st msg ret s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-- Core postcondition of `spqr::recv`: `spqrRecvCorePost0` with `¬ M.recvPanics st msg` in the
    first pure conjunct, matching `spqrRecvSpecExactKey.post`. -/
abbrev spqrRecvCorePost (A : RustAlloc) (b : BitVec 64) (M : SpqrRecvModel)
    (st msg : VecArg) (ret : BitVec 64) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace ∧ ¬ M.recvPanics st.bytes msg.bytes⌝ ∗
    spqrRecvRoAt b ∗
    st.at A ∗
    msg.at A ∗
    recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
    A.pool ∗
    stackAt s0.sp spqrRecvStack

abbrev spqrRecvPost (A : RustAlloc) (b : BitVec 64) (M : SpqrRecvModel)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spqrRecvCorePost A b M st msg ret s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

theorem satisfies_pure_and_of_pure {mem : Memory} {p q : Prop} {X R : SepProp}
    (h : mem ⊨ (⌜p⌝ ∗ X) ∗ R) (hq : q) : mem ⊨ (⌜p ∧ q⌝ ∗ X) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  exact ⟨⟨h.1, hq⟩, h.2⟩

/-- `spqrRecvPost0` gives `spqrRecvPost` once the model does not panic. -/
theorem spqrRecvPost_of_post0 {A : RustAlloc} {b : BitVec 64} {M : SpqrRecvModel}
    {st msg : VecArg} {ret : BitVec 64} {s0 : State} {R : SepProp} {sf : State} {P_f : SepProp}
    (hnp : ¬ M.recvPanics st.bytes msg.bytes)
    (h : spqrRecvPost0 A b M st msg ret s0 R sf P_f) :
    spqrRecvPost A b M st msg ret s0 R sf P_f :=
  ⟨fun hm => satisfies_pure_and_of_pure (h.1 hm) hnp, h.2⟩

/-- Lift `SepWP` from `spqrRecvPost0` to `spqrRecvPost` given `¬ M.recvPanics st msg`. -/
theorem sepWP_spqrRecvPost_of_post0 {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {A : RustAlloc} {b : BitVec 64} {M : SpqrRecvModel}
    {st msg : VecArg} {ret : BitVec 64} {s0 : State} {R : SepProp}
    (hnp : ¬ M.recvPanics st.bytes msg.bytes)
    (h : SepWP prog target_pc s P (spqrRecvPost0 A b M st msg ret s0 R)) :
    SepWP prog target_pc s P (spqrRecvPost A b M st msg ret s0 R) :=
  SepWP.mono h (fun _ _ _ _ hq => spqrRecvPost_of_post0 hnp hq)

abbrev spqrRecvPanicPost (M : SpqrRecvModel)
    (st msg : VecArg) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ M.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem sp_sub_4992_aligned (s0 : State) (h : s0.spAligned = true) :
    ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := by
  simp only [State.spAligned, beq_iff_eq] at h ⊢
  generalize s0.sp = sp at h ⊢
  revert sp h; bv_kernel

theorem sp_sub_96_aligned (s0 : State) (h : s0.spAligned = true) :
    ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := by
  simp only [State.spAligned, beq_iff_eq] at h ⊢
  generalize s0.sp = sp at h ⊢
  revert sp h; bv_kernel

theorem spqrRecvSavedRegs_eq_decodeStateSavedAt (sp0 : BitVec 64) (s0 : State) :
    spqrRecvSavedRegs (sp0 - 4992#64) s0 =
      decodeStateSavedAt sp0 (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19) := by
  unfold spqrRecvSavedRegs decodeStateSavedAt
  rw [bv_sub_add_lit sp0 4992 4896,
      bv_sub_add_lit sp0 4992 4904,
      bv_sub_add_lit sp0 4992 4912,
      bv_sub_add_lit sp0 4992 4920,
      bv_sub_add_lit sp0 4992 4928,
      bv_sub_add_lit sp0 4992 4936,
      bv_sub_add_lit sp0 4992 4944,
      bv_sub_add_lit sp0 4992 4952,
      bv_sub_add_lit sp0 4992 4960,
      bv_sub_add_lit sp0 4992 4968,
      bv_sub_add_lit sp0 4992 4976,
      bv_sub_add_lit sp0 4992 4984]

/-- Shared epilogue (`+1040 .. +1072`, `0x54a3c .. 0x54a5c`, 9 instructions): restores `sp =
    s0.sp`, `x19..x30` from `spqrRecvSavedRegs (s0.sp - 4992#64) s0`, reassembles `stackAt s0.sp
    spqrRecvStack`, and returns to `s0.readReg64 .x30`. -/
theorem step_epilogue (b : BitVec 64) (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b M st msg ret s0 R)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 1040#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_4992_aligned s0 hs0A
  have hsp96A : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    sp_sub_96_aligned s0 hs0A
  subst hP hpost
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, spqrRecvPost0, spqrRecvCorePost0] at hpc ⊢
  spqr_recv_fetches_range b (Rust.withPanics ext) 1040 36
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::recv" = entry
  examples_hide_fetches
  generalize hsp0 : s0.sp = sp0 at hsp hsp96A ⊢
  rw [spqrRecvSavedRegs_eq_decodeStateSavedAt sp0 s0]
  unfold decodeStateSavedAt
  wp_steps 9
  have hrestore := stack_restore_spqrRecv sp0 s0
  rw [spqrRecvSavedRegs_eq_decodeStateSavedAt sp0 s0] at hrestore
  refine SepWP.fold hrestore (by
    unfold decodeStateSavedAt
    sep_focus) ?_
  wp_done

/-- `Err(MsgDecode)` exit (`+276 .. +288`, `0x54740 .. 0x5474c` -> `+1040 .. +1072`): stores
    `-1` and `2` (`Error::MsgDecode`) at `ret` (`x19`), folds `recvResultExactKeyAt A ret
    (.error false)`, and runs `step_epilogue`. -/
theorem step_err_msgDecode (b : BitVec 64) (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b M st msg ret s0 R)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_4992_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName] at hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 276 16
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::recv" = entry
  examples_hide_fetches
  rw [ret_48_split ret]
  wp_pull_exists
  rename_i r3 r2 r1 r0
  wp_steps 4
  have hfold := recv_err_msgDecode_foldX A ret r2 r3
  rw [← herr] at hfold
  refine SepWP.fold hfold (by sep_focus) ?_
  exact step_epilogue b A M ext st msg ret s0 _ _ R post hpost
    (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hs0A
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- Lift `step_err_msgDecode` into `SepWPpI`. -/
theorem step_err_msgDecode_wppI (img : Obj.Image) (b : BitVec 64) (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 s : State) (P R : SepProp)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (spqrRecvPost0 A b M st msg ret s0 R)
      (spqrRecvPanicPost M st msg s0 R) :=
  SepWPpI.of_sepWPp (SepWPp.of_sepWP_ret
    (step_err_msgDecode b A M ext st msg ret s0 s P R _ rfl herr hpc hrun hsp hs0A htr hx19 hP))

/-! ## Preamble Varint Decoding (`+0 .. +312`, `0x5462c .. 0x54764`) -/

open CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
  (msgByteFrame msg_expose_byte msg_unexpose_byte
   varint_out_norm list_cons_of_length_pos
   nat_le_of_bv_ule nat_lt_of_not_bv_ule
   hb_ne_of_sxtb_tb hb_eq_of_not_sxtb_tb
   csel_rest1_min_10 rest1_nil_of_ule rest1_cons_of_not_ule
   index_bounds_ne varint_end_of_ge varint_cont_of_lt)

theorem decodeVarintLoop_err_of_hi {i : Nat} {out : BitVec 64} {b : BitVec 8} {rest' : List (BitVec 8)}
    (hb : b &&& 0x80#8 ≠ 0#8) (hend : i + 1 = 10 ∨ rest' = []) :
    LibsignalSpqrV1.decodeVarintLoop i out (b :: rest') = none := by
  rw [LibsignalSpqrV1.decodeVarintLoop]
  simp only [hb, ↓reduceIte, MAX_VARINT_BYTES_LEN]
  rcases hend with h10 | rfl
  · simp [h10]
  · by_cases h10 : i + 1 = 10 <;> simp [h10, LibsignalSpqrV1.decodeVarintLoop]

theorem decodeVarintLoop_ok_of_lo {i : Nat} {out : BitVec 64} {b : BitVec 8} {rest' : List (BitVec 8)}
    (hb : b &&& 0x80#8 = 0#8) :
    LibsignalSpqrV1.decodeVarintLoop i out (b :: rest') =
      some (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * i)), rest') := by
  rw [LibsignalSpqrV1.decodeVarintLoop]
  simp [hb]

theorem decodeVarintLoop_step_of_hi {i : Nat} {out : BitVec 64} {b : BitVec 8} {rest' : List (BitVec 8)}
    (hb : b &&& 0x80#8 ≠ 0#8) (hi : i + 1 < 10) :
    LibsignalSpqrV1.decodeVarintLoop i out (b :: rest') =
      LibsignalSpqrV1.decodeVarintLoop (i + 1) (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * i))) rest' := by
  conv => lhs; rw [LibsignalSpqrV1.decodeVarintLoop]
  have hne : i + 1 ≠ MAX_VARINT_BYTES_LEN := by unfold MAX_VARINT_BYTES_LEN; omega
  simp [hb, hne]

theorem msgPreamble_nil :
    msgPreamble [] = .ok { version := 0#8, epoch := 0#64, index := 0#32, remaining := [] } := rfl

theorem msgPreamble_singleton (v : BitVec 8) :
    msgPreamble [v] = .error .msgDecode := rfl

theorem msgPreamble_cons_cons (v b : BitVec 8) (rest : List (BitVec 8)) :
    msgPreamble (v :: b :: rest) =
      match LibsignalSpqrV1.decodeVarintLoop 0 0#64 (b :: rest) with
      | none => .error .msgDecode
      | some (epoch, rest1) =>
        if epoch == 0#64 then .error .msgDecode
        else
          match LibsignalSpqrV1.decodeVarint rest1 with
          | .error e => .error e
          | .ok (index, rest2) =>
            if index.toNat < 2 ^ 32 then
              .ok { version := v, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
            else
              .error .msgDecode := by
  unfold msgPreamble msg_preamble LibsignalSpqrV1.decodeVarint
  simp only [decode_varint, Bind.bind, Except.bind]
  cases LibsignalSpqrV1.decodeVarintLoop 0 0#64 (b :: rest) with
  | none => rfl
  | some p =>
    rcases p with ⟨epoch, rest1⟩
    dsimp only
    by_cases he : epoch = 0#64
    · subst he; rfl
    · have heb : (epoch == 0#64) = false := beq_false_of_ne he
      simp only [he, heb, Bool.false_eq_true, ↓reduceIte]
      cases LibsignalSpqrV1.decodeVarintLoop 0 0#64 rest1 with
      | none => rfl
      | some q =>
        rcases q with ⟨index, rest2⟩
        rfl

open CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
  (msgHeaderTail msg_expose_hdr msg_unexpose_hdr
   msg_nil_of_len_zero msg_singleton_of_len_one msg_cons_cons_of_len_ge_two)

theorem zeroExtend_setWidth32_of_lt {x : BitVec 64} (h : x.toNat < 2 ^ 32) :
    (x.setWidth 32).zeroExtend 64 = x := by
  revert x h; bv_kernel

theorem rem_len_add_not {msg_len pre1_len j rem_len : Nat}
    (hlen : msg_len = 1 + pre1_len + j + 1 + rem_len)
    (hlt : msg_len < 2 ^ 63) :
    ~~~ (BitVec.ofNat 64 (pre1_len + j + 1)) + BitVec.ofNat 64 msg_len =
      BitVec.ofNat 64 rem_len := by
  have h1 : pre1_len + j + 1 < 2 ^ 63 := by omega
  have h2 : rem_len < 2 ^ 63 := by omega
  have hnot : ~~~ (BitVec.ofNat 64 (pre1_len + j + 1)) =
      -1#64 - BitVec.ofNat 64 (pre1_len + j + 1) := by bv_arith
  rw [hnot]
  bv_omega

/-- Frame invariant throughout `+0 .. +312` (after the prologue): all stack/heap resources of
    `spqr::recv` at `fsp = s0.sp - 4992#64`. -/
abbrev spqrRecvPreambleFrame (b : BitVec 64) (A : RustAlloc) (st msg : VecArg)
    (ret : BitVec 64) (s0 : State) : SepProp :=
  spqrRecvRoAt b ∗
  st.at A ∗
  msg.at A ∗
  memRegion ret 48 ∗
  A.pool ∗
  stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
  memRegion (s0.sp - 4992#64) 0x1320 ∗
  spqrRecvSavedRegs (s0.sp - 4992#64) s0

/-- Continuation hypothesis at `+276` (`Err(MsgDecode)`). -/
abbrev PreambleErrTail (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64) (s0 : State)
    (post : State → SepProp → Prop) : Prop :=
  ∀ (s1 : State) (P1 : SepProp),
    msgPreamble msg.bytes = .error .msgDecode →
    s1.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 276#64 →
    s1.status = .Running →
    s1.sp = s0.sp - 4992#64 →
    TraceVRegs s1 s0 →
    s1.readReg64 .x19 = ret →
    P1 = spqrRecvPreambleFrame b A st msg ret s0 →
    SepWP (tripleRatchetProgAtExt b ext) target_pc s1 P1 post

/-- Continuation hypothesis at `+312` (`Ok(pre)`). -/
abbrev PreambleOkTail (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64) (s0 : State)
    (post : State → SepProp → Prop) : Prop :=
  ∀ (pre : MsgPreamble) (msgPtr : BitVec 64) (s1 : State) (P1 : SepProp),
    msgPreamble msg.bytes = .ok pre →
    MsgRemValid msg msgPtr pre.remaining →
    s1.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 312#64 →
    s1.status = .Running →
    s1.sp = s0.sp - 4992#64 →
    TraceVRegs s1 s0 →
    s1.readReg64 .x0 = st.v →
    s1.readReg64 .x19 = ret →
    s1.readReg64 .x21 = pre.index.zeroExtend 64 →
    s1.readReg64 .x22 = pre.epoch →
    s1.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
    s1.readReg64 .x24 = msgPtr →
    s1.readReg64 .x25 = pre.version.zeroExtend 64 →
    s1.readReg64 .x29 = s0.sp - 96#64 →
    P1 = spqrRecvPreambleFrame b A st msg ret s0 →
    SepWP (tripleRatchetProgAtExt b ext) target_pc s1 P1 post

set_option maxHeartbeats 800000 in
/-- Steps from `+252` (`0x54728: lsr x11, x21, #32`) after decoding `(index, rest')`. -/
theorem step_after_index (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (version : BitVec 8) (epoch index : BitVec 64)
    (pre₁ pre₂ rest' : List (BitVec 8)) (byteJ : BitVec 8) (j : Nat)
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (herr_tail : PreambleErrTail b A ext st msg ret target_pc s0 post)
    (hok_tail : PreambleOkTail b A ext st msg ret target_pc s0 post)
    (hlen_lt : msg.bytes.length < 2 ^ 63)
    (hsplit : msg.bytes = (version :: pre₁ ++ pre₂) ++ byteJ :: rest')
    (hpre2 : pre₂.length = j)
    (hpre : msgPreamble msg.bytes =
      if index.toNat < 2 ^ 32 then
        .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest' }
      else
        .error .msgDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx8 : s.readReg64 .x8 = msg.ptr + 1#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (pre₁.length + j + 1))
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = index)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx25 : s.readReg64 .x25 = version.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = spqrRecvPreambleFrame b A st msg ret s0) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s P post := by
  spqr_recv_fetches_range b (Rust.withPanics ext) 252 24
  have hlen_eq : msg.bytes.length = 1 + pre₁.length + j + 1 + rest'.length := by
    rw [hsplit]; simp [hpre2]; omega
  have hrem := rem_len_add_not hlen_eq hlen_lt
  clear hlen_eq
  have hvalid : MsgRemValid msg
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j + 1))) rest' := by
    right
    refine ⟨(version :: pre₁ ++ pre₂) ++ [byteJ], ?_, ?_⟩
    · rw [hsplit]; simp [List.append_assoc]
    · have hlen_p : ((version :: pre₁ ++ pre₂) ++ [byteJ]).length = 1 + (pre₁.length + j + 1) := by
        simp [List.length_cons, List.length_append, List.length_singleton, hpre2]; omega
      rw [hlen_p]
      simp only [BitVec.ofNat_add]
  clear hsplit
  dsimp only [PreambleErrTail, PreambleOkTail, tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_if hhi
  · have hnlt : ¬ index.toNat < 2 ^ 32 := by bv_omega
    have herr : msgPreamble msg.bytes = .error .msgDecode := by
      simp only [hpre, hnlt, ↓reduceIte]
    exact herr_tail _ P herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm]) (by simp [hx19, arm64_norm]) hP
  · have hlt : index.toNat < 2 ^ 32 := by bv_omega
    have hok : msgPreamble msg.bytes =
        .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest' } := by
      simp only [hpre, hlt, ↓reduceIte]
    wp_steps
    exact hok_tail
      { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest' }
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j + 1)))
      _ P hok hvalid
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
      (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx21, arm64_norm, zeroExtend_setWidth32_of_lt hlt])
      (by simp [hx22, arm64_norm])
      (by simp [hx9, hx10, hrem, arm64_norm])
      (by simp [hx8, hx10, arm64_norm]; bv_arith)
      (by simp [hx25, arm64_norm])
      (by simp [hx29, arm64_norm])
      hP

set_option maxHeartbeats 1600000 in
/-- Steps the index varint loop (`+192 .. +248`) from iteration `j` (`k = 10 - j` fuel). -/
theorem step_index_loop (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (version : BitVec 8) (epoch : BitVec 64)
    (pre₁ rest1 : List (BitVec 8))
    (s0 : State) (post : State → SepProp → Prop)
    (herr_tail : PreambleErrTail b A ext st msg ret target_pc s0 post)
    (hok_tail : PreambleOkTail b A ext st msg ret target_pc s0 post)
    (hpre1 : 1 ≤ pre₁.length)
    (hlen_lt : msg.bytes.length < 2 ^ 63) :
    ∀ (k j : Nat) (out : BitVec 64) (pre₂ rest' : List (BitVec 8)) (byteJ : BitVec 8)
      (s : State) (P : SepProp),
      10 - j ≤ k →
      j < 10 →
      msg.bytes = (version :: pre₁ ++ pre₂) ++ byteJ :: rest' →
      rest1 = pre₂ ++ byteJ :: rest' →
      pre₂.length = j →
      (msgPreamble msg.bytes =
        match LibsignalSpqrV1.decodeVarintLoop j out (byteJ :: rest') with
        | none => .error .msgDecode
        | some (index, rest2) =>
          if index.toNat < 2 ^ 32 then
            .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
          else
            .error .msgDecode) →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 192#64 →
      s.status = .Running →
      s.sp = s0.sp - 4992#64 →
      TraceVRegs s s0 →
      s.readReg64 .x0 = st.v →
      s.readReg64 .x19 = ret →
      s.readReg64 .x22 = epoch →
      s.readReg64 .x25 = version.zeroExtend 64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      s.readReg64 .x8 = msg.ptr + 1#64 →
      s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length →
      s.readReg64 .x10 = BitVec.ofNat 64 (pre₁.length + j) →
      s.readReg64 .x11 = BitVec.ofNat 64 (7 * j) →
      s.readReg64 .x12 = BitVec.ofNat 64 (pre₁.length - 1 + j) →
      s.readReg64 .x13 = BitVec.ofNat 64 (min rest1.length 10) →
      s.readReg64 .x14 = BitVec.ofNat 64 (msg.bytes.length - 2) →
      s.readReg64 .x15 = BitVec.ofNat 64 (j + 1) →
      s.readReg64 .x21 = out →
      P = spqrRecvPreambleFrame b A st msg ret s0 →
      SepWP (tripleRatchetProgAtExt b ext) target_pc s P post := by
  intro k
  induction k with
  | zero =>
    intro j _ _ _ _ _ _ hjk hj
    omega
  | succ k ih =>
    intro j out pre₂ rest' byteJ s P hjk hj hsplit hrest1 hpre2 hpre
      hpc hrun hsp htr hx0 hx19 hx22 hx25 hx29 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx21 hP
    have hafter := step_after_index b A ext st msg ret target_pc version epoch
      (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
      pre₁ pre₂ rest' byteJ j s0
    spqr_recv_fetches_range b (Rust.withPanics ext) 192 60
    have hmsg_ge : pre₁.length + j + 2 ≤ msg.bytes.length := by
      rw [hsplit]; simp [hpre2]
    have hne_bounds := index_bounds_ne hpre1 hmsg_ge hlen_lt
    have hoff : msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j)) =
        msg.ptr + BitVec.ofNat 64 (version :: pre₁ ++ pre₂).length := by
      simp only [List.length_cons, List.length_append, hpre2]; bv_omega
    have hexp := msg_expose_byte A msg (version :: pre₁ ++ pre₂) rest' byteJ
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j))) hsplit hoff
    have hunexp := msg_unexpose_byte A msg (version :: pre₁ ++ pre₂) rest' byteJ
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j))) hsplit hoff
    clear hoff
    have hsplit_symm := hsplit.symm; clear hsplit
    have hrest1_symm := hrest1.symm; clear hrest1
    subst hP
    dsimp only [PreambleErrTail, PreambleOkTail, tripleRatchetProgAtExt, spqrRecvName, spqrRecvPreambleFrame, BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail hafter ih ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::recv" = entry
    examples_hide_fetches
    wp_steps
    wp_if hbounds
    · exact False.elim (hne_bounds hbounds)
    clear hbounds
    refine SepWP.fold hexp (by sep_focus) ?_
    wp_steps
    refine SepWP.fold hunexp (by sep_focus) ?_
    wp_if hhs
    · have hge : min rest1.length 10 ≤ j + 1 :=
        nat_le_of_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      have hend := varint_end_of_ge hj hrest1_symm.symm hpre2 hge
      wp_steps
      wp_if htb
      · have hb : byteJ &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb byteJ htb
        have herr : msgPreamble msg.bytes = .error .msgDecode := by
          rw [hpre, decodeVarintLoop_err_of_hi hb hend]
        exact herr_tail _ _ herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm])
          (by simp [hx19, arm64_norm]) (by ac_rfl)
      · have hb : byteJ &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb byteJ htb
        have hpre_ok : msgPreamble msg.bytes =
            if (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).toNat < 2 ^ 32 then
              .ok { version := version, epoch := epoch,
                    index := (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).setWidth 32,
                    remaining := rest' }
            else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_ok_of_lo hb]
        exact hafter _ _ post herr_tail hok_tail hlen_lt hsplit_symm.symm hpre2 hpre_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx8, arm64_norm])
          (by simp [hx9, arm64_norm]) (by simp [hx10, arm64_norm]; try bv_omega)
          (by simp [hx19, arm64_norm])
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by simp [hx22, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by ac_rfl)
    · have hlt : j + 1 < min rest1.length 10 :=
        nat_lt_of_not_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      obtain ⟨hj1, b', rest'', rfl⟩ := varint_cont_of_lt hrest1_symm.symm hpre2 hlt
      wp_steps
      wp_if htb
      · have hb : byteJ &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb byteJ htb
        have hpre_step : msgPreamble msg.bytes =
            match LibsignalSpqrV1.decodeVarintLoop (j + 1) (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) (b' :: rest'') with
            | none => .error .msgDecode
            | some (index, rest2) =>
              if index.toNat < 2 ^ 32 then
                .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
              else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_step_of_hi hb hj1]
        have hsplit' : msg.bytes = (version :: pre₁ ++ (pre₂ ++ [byteJ])) ++ b' :: rest'' := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hrest1' : rest1 = (pre₂ ++ [byteJ]) ++ b' :: rest'' := by
          rw [← hrest1_symm]; simp [List.append_assoc]
        have hpre2' : (pre₂ ++ [byteJ]).length = j + 1 := by
          rw [List.length_append, List.length_singleton, hpre2]
        exact ih (j + 1) (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
          (pre₂ ++ [byteJ]) rest'' b' _ _ (by omega) hj1 hsplit' hrest1' hpre2' hpre_step
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx22, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; try bv_omega)
          (by simp [hx13, arm64_norm]) (by simp [hx14, arm64_norm])
          (by simp [arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by ac_rfl)
      · have hb : byteJ &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb byteJ htb
        have hpre_ok : msgPreamble msg.bytes =
            if (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).toNat < 2 ^ 32 then
              .ok { version := version, epoch := epoch,
                    index := (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).setWidth 32,
                    remaining := b' :: rest'' }
            else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_ok_of_lo hb]
        wp_steps
        exact hafter _ _ post herr_tail hok_tail hlen_lt hsplit_symm.symm hpre2 hpre_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx8, arm64_norm])
          (by simp [hx9, arm64_norm]) (by simp [hx10, arm64_norm]; try bv_omega)
          (by simp [hx19, arm64_norm])
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by simp [hx22, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- Steps from `+144` (`0x546bc: cbz x22, 0x54740`) after decoding `(epoch, rest1)`. -/
theorem step_after_epoch (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (version : BitVec 8) (pre₁ rest1 : List (BitVec 8)) (epoch : BitVec 64)
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (herr_tail : PreambleErrTail b A ext st msg ret target_pc s0 post)
    (hok_tail : PreambleOkTail b A ext st msg ret target_pc s0 post)
    (hpre1 : 1 ≤ pre₁.length)
    (hlen_lt : msg.bytes.length < 2 ^ 63)
    (hmsg_eq : msg.bytes = version :: (pre₁ ++ rest1))
    (hpre : msgPreamble msg.bytes =
      if epoch == 0#64 then .error .msgDecode
      else
        match LibsignalSpqrV1.decodeVarint rest1 with
        | .error e => .error e
        | .ok (index, rest2) =>
          if index.toNat < 2 ^ 32 then
            .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
          else .error .msgDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx19 : s.readReg64 .x19 = ret)
    (hx25 : s.readReg64 .x25 = version.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx8 : s.readReg64 .x8 = msg.ptr + 1#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 (1 + pre₁.length))
    (hx22 : s.readReg64 .x22 = epoch)
    (hP : P = spqrRecvPreambleFrame b A st msg ret s0) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s P post := by
  have hidx_loop := step_index_loop b A ext st msg ret target_pc version epoch pre₁ rest1
    s0 post herr_tail hok_tail hpre1 hlen_lt 10 0 0#64 []
  spqr_recv_fetches_range b (Rust.withPanics ext) 144 48
  have hmsg_symm := hmsg_eq.symm; clear hmsg_eq
  dsimp only [PreambleErrTail, PreambleOkTail, tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail hidx_loop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_if hepoch
  · have herr : msgPreamble msg.bytes = .error .msgDecode := by
      simp [hpre, hepoch]
    exact herr_tail _ P herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm]) (by simp [hx19, arm64_norm]) hP
  · have hepoch_f : (epoch == 0#64) = false := beq_false_of_ne hepoch
    wp_steps
    wp_if hls
    · have hrest1_nil := rest1_nil_of_ule hmsg_symm.symm hlen_lt hls
      have herr : msgPreamble msg.bytes = .error .msgDecode := by
        rw [hpre, hepoch_f, hrest1_nil]; rfl
      exact herr_tail _ P herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm]) (by simp [hx19, arm64_norm]) hP
    · wp_steps
      obtain ⟨b₀, rest1', hrest1_cons⟩ := rest1_cons_of_not_ule hmsg_symm.symm hlen_lt hls
      have hlen_eq : msg.bytes.length = 1 + pre₁.length + rest1.length := by
        rw [← hmsg_symm, List.length_cons, List.length_append]
        omega
      have hpre1_lt : 1 + pre₁.length < 2 ^ 63 := by omega
      have hlen_ge : 2 ≤ msg.bytes.length := by
        rw [← hmsg_symm, hrest1_cons]; simp; omega
      have hsplit0 : msg.bytes = (version :: pre₁ ++ []) ++ b₀ :: rest1' := by
        rw [← hmsg_symm, hrest1_cons]; simp
      have hrest1_0 : rest1 = [] ++ b₀ :: rest1' := hrest1_cons
      have hpre0 : msgPreamble msg.bytes =
          match LibsignalSpqrV1.decodeVarintLoop 0 0#64 (b₀ :: rest1') with
          | none => .error .msgDecode
          | some (index, rest2) =>
            if index.toNat < 2 ^ 32 then
              .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
            else .error .msgDecode := by
        rw [hpre, hepoch_f, hrest1_cons]
        dsimp only [LibsignalSpqrV1.decodeVarint, decode_varint, Bool.false_eq_true, ↓reduceIte]
        cases LibsignalSpqrV1.decodeVarintLoop 0 0#64 (b₀ :: rest1') <;> rfl
      exact hidx_loop rest1' b₀ _ P (by omega) (by omega) hsplit0 hrest1_0 rfl hpre0
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
        (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx22, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
        (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
        (by simp [arm64_norm]; try bv_omega)
        (by simp [arm64_norm])
        (by simp [arm64_norm]; try bv_omega)
        (by simp [arm64_norm]; exact csel_rest1_min_10 hlen_eq hlen_lt)
        (by simp [arm64_norm]; try bv_omega)
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        hP

set_option maxHeartbeats 1600000 in
/-- Steps the epoch varint loop (`+96 .. +140`) from iteration `j` (`k = 10 - j` fuel). -/
theorem step_epoch_loop (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (version : BitVec 8) (rest0 : List (BitVec 8))
    (s0 : State) (post : State → SepProp → Prop)
    (herr_tail : PreambleErrTail b A ext st msg ret target_pc s0 post)
    (hok_tail : PreambleOkTail b A ext st msg ret target_pc s0 post)
    (hlen_lt : msg.bytes.length < 2 ^ 63) :
    ∀ (k j : Nat) (out : BitVec 64) (pre₁ rest0' : List (BitVec 8)) (byteJ : BitVec 8)
      (s : State) (P : SepProp),
      10 - j ≤ k →
      j < 10 →
      msg.bytes = (version :: pre₁) ++ byteJ :: rest0' →
      rest0 = pre₁ ++ byteJ :: rest0' →
      pre₁.length = j →
      (msgPreamble msg.bytes =
        match LibsignalSpqrV1.decodeVarintLoop j out (byteJ :: rest0') with
        | none => .error .msgDecode
        | some (epoch, rest1) =>
          if epoch == 0#64 then .error .msgDecode
          else
            match LibsignalSpqrV1.decodeVarint rest1 with
            | .error e => .error e
            | .ok (index, rest2) =>
              if index.toNat < 2 ^ 32 then
                .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
              else .error .msgDecode) →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 96#64 →
      s.status = .Running →
      s.sp = s0.sp - 4992#64 →
      TraceVRegs s s0 →
      s.readReg64 .x0 = st.v →
      s.readReg64 .x19 = ret →
      s.readReg64 .x25 = version.zeroExtend 64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      s.readReg64 .x8 = msg.ptr + 1#64 →
      s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length →
      s.readReg64 .x10 = BitVec.ofNat 64 (7 * j) →
      s.readReg64 .x11 = msg.ptr →
      s.readReg64 .x12 = BitVec.ofNat 64 (min rest0.length 10) →
      s.readReg64 .x14 = BitVec.ofNat 64 (j + 1) →
      s.readReg64 .x22 = out →
      P = spqrRecvPreambleFrame b A st msg ret s0 →
      SepWP (tripleRatchetProgAtExt b ext) target_pc s P post := by
  intro k
  induction k with
  | zero =>
    intro j _ _ _ _ _ _ hjk hj
    omega
  | succ k ih =>
    intro j out pre₁ rest0' byteJ s P hjk hj hsplit hrest0 hpre1 hpre
      hpc hrun hsp htr hx0 hx19 hx25 hx29 hx8 hx9 hx10 hx11 hx12 hx14 hx22 hP
    have hafter := step_after_epoch b A ext st msg ret target_pc version
      (pre₁ ++ [byteJ]) rest0' (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) s0
    spqr_recv_fetches_range b (Rust.withPanics ext) 96 48
    have hoff : msg.ptr + BitVec.ofNat 64 (j + 1) =
        msg.ptr + BitVec.ofNat 64 (version :: pre₁).length := by
      simp only [List.length_cons, hpre1]
    have hexp := msg_expose_byte A msg (version :: pre₁) rest0' byteJ
      (msg.ptr + BitVec.ofNat 64 (j + 1)) hsplit hoff
    have hunexp := msg_unexpose_byte A msg (version :: pre₁) rest0' byteJ
      (msg.ptr + BitVec.ofNat 64 (j + 1)) hsplit hoff
    clear hoff
    have hsplit_symm := hsplit.symm; clear hsplit
    have hrest0_symm := hrest0.symm; clear hrest0
    subst hP
    dsimp only [PreambleErrTail, PreambleOkTail, tripleRatchetProgAtExt, spqrRecvName, spqrRecvPreambleFrame, BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail hafter ih ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::recv" = entry
    examples_hide_fetches
    refine SepWP.fold hexp (by sep_focus) ?_
    wp_steps
    refine SepWP.fold hunexp (by sep_focus) ?_
    wp_if hhs
    · have hge : min rest0.length 10 ≤ j + 1 :=
        nat_le_of_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      have hend := varint_end_of_ge hj hrest0_symm.symm hpre1 hge
      wp_steps
      wp_if htb
      · have hb : byteJ &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb byteJ htb
        have herr : msgPreamble msg.bytes = .error .msgDecode := by
          rw [hpre, decodeVarintLoop_err_of_hi hb hend]
        exact herr_tail _ _ herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          (by simp [hsp, arm64_norm]) (by simp [htr, arm64_norm])
          (by simp [hx19, arm64_norm]) (by ac_rfl)
      · have hb : byteJ &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb byteJ htb
        have hpre_ok : msgPreamble msg.bytes =
            if (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) == 0#64 then .error .msgDecode
            else
              match LibsignalSpqrV1.decodeVarint rest0' with
              | .error e => .error e
              | .ok (index, rest2) =>
                if index.toNat < 2 ^ 32 then
                  .ok { version := version,
                        epoch := out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)),
                        index := index.setWidth 32, remaining := rest2 }
                else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_ok_of_lo hb]
        have hmsg_eq' : msg.bytes = version :: ((pre₁ ++ [byteJ]) ++ rest0') := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hpre1' : 1 ≤ (pre₁ ++ [byteJ]).length := by
          rw [List.length_append, List.length_singleton]; omega
        exact hafter _ _ post herr_tail hok_tail hpre1' hlen_lt hmsg_eq' hpre_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [hpre1, arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by ac_rfl)
    · have hlt : j + 1 < min rest0.length 10 :=
        nat_lt_of_not_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      obtain ⟨hj1, b', rest0'', rfl⟩ := varint_cont_of_lt hrest0_symm.symm hpre1 hlt
      wp_steps
      wp_if htb
      · have hb : byteJ &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb byteJ htb
        have hpre_step : msgPreamble msg.bytes =
            match LibsignalSpqrV1.decodeVarintLoop (j + 1) (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) (b' :: rest0'') with
            | none => .error .msgDecode
            | some (epoch, rest1) =>
              if epoch == 0#64 then .error .msgDecode
              else
                match LibsignalSpqrV1.decodeVarint rest1 with
                | .error e => .error e
                | .ok (index, rest2) =>
                  if index.toNat < 2 ^ 32 then
                    .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
                  else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_step_of_hi hb hj1]
        have hsplit' : msg.bytes = (version :: (pre₁ ++ [byteJ])) ++ b' :: rest0'' := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hrest0' : rest0 = (pre₁ ++ [byteJ]) ++ b' :: rest0'' := by
          rw [← hrest0_symm]; simp [List.append_assoc]
        have hpre1' : (pre₁ ++ [byteJ]).length = j + 1 := by
          rw [List.length_append, List.length_singleton, hpre1]
        exact ih (j + 1) (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
          (pre₁ ++ [byteJ]) rest0'' b' _ _ (by omega) hj1 hsplit' hrest0' hpre1' hpre_step
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [arm64_norm]; try bv_omega)
          (by simp [hx11, arm64_norm]) (by simp [hx12, arm64_norm])
          (by simp [arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by ac_rfl)
      · have hb : byteJ &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb byteJ htb
        have hpre_ok : msgPreamble msg.bytes =
            if (out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) == 0#64 then .error .msgDecode
            else
              match LibsignalSpqrV1.decodeVarint (b' :: rest0'') with
              | .error e => .error e
              | .ok (index, rest2) =>
                if index.toNat < 2 ^ 32 then
                  .ok { version := version,
                        epoch := out ||| ((byteJ &&& 0x7F#8).zeroExtend 64 <<< (7 * j)),
                        index := index.setWidth 32, remaining := rest2 }
                else .error .msgDecode := by
          rw [hpre, decodeVarintLoop_ok_of_lo hb]
        have hmsg_eq' : msg.bytes = version :: ((pre₁ ++ [byteJ]) ++ b' :: rest0'') := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hpre1' : 1 ≤ (pre₁ ++ [byteJ]).length := by
          rw [List.length_append, List.length_singleton]; omega
        wp_steps
        exact hafter _ _ post herr_tail hok_tail hpre1' hlen_lt hmsg_eq' hpre_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx29, arm64_norm])
          (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [hpre1, arm64_norm]; try bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out byteJ j hj)
          (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv

