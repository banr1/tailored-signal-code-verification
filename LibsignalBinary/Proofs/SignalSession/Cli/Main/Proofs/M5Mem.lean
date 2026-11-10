/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5Iface
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5Sites -- shake: keep
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Specifications.AsmConstants

/-!
# Instruction Decodes, Heap Borrow Lemmas, and `commitFiles` Helpers for `main` Hop M5

Layout-independent M5 instruction decodes (`m5Dec`), 128-bit pair and stride-48 `vecBuf`
borrow/unborrow lemmas, `dirAt` unpacking, and `pathOf` / `commitFiles` stepping lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops.LoopDrop

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open Arm64.Process
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint DoReserveNorm
open CryptoVerification.SignalSession.Cli.Path.Helpers

/-! ## 1. Layout-Independent Instruction Decodes (`m5Dec`) -/

gen_decodes CryptoVerification.libsignalSessionCode_tree m5Dec
  [(ls_off% "main" + 0x820) → (ls_off% "main" + 0xa4c),
   (ls_off% "main" + 0xad8) → (ls_off% "main" + 0xae4),
   (ls_off% "main" + 0xb74) → (ls_off% "main" + 0xb80),
   (ls_off% "main" + 0xc20) → (ls_off% "main" + 0xc24),
   (ls_off% "main" + 0xf34) → (ls_off% "main" + 0xf34)]

theorem mFetch (img : Obj.Image) (ext : String → Option (State → State))
    (k : Nat) {ins}
    (hbound : k < 0x1000 := by decide)
    (hdec : CryptoVerification.libsignalSessionCode_tree.fetchDecodeAt
      (num% (ls_off% "main") + k) = some ins) :
    (mProg img ext).fetch (mPc img ext k) = some ins :=
  CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := img.base) (H := Rust.withPanics ext) (k := k) main_fnOff
    (by omega) hdec (hoff := by omega)

/-! ## 2. 128-Bit Pair Access, Address Arithmetic & Memory Helpers -/

@[simp, arm64_norm]
theorem concat64_lo (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_kernel

@[simp, arm64_norm]
theorem concat64_hi (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_kernel

theorem pair64_eq_128 (a o1 o2 w0 w1 : BitVec 64)
    (ho : a + o2 = (a + o1) + 8#64 := by bv_omega) :
    ((a + o1) ↦₆₄ w0) ∗ ((a + o2) ↦₆₄ w1) = ((a + o1) ↦₁₂₈ (w1 ++ w0)) := by
  rw [ho, pointsTo64_pair_eq_pointsTo128]

theorem sep_anyHeap_absorb (P : SepProp) : P ∗ anyHeap ⊢ anyHeap :=
  entails_anyHeap _

theorem pure_sepConj_pure (p q : Prop) : (⌜p⌝ : SepProp) ∗ ⌜q⌝ = ⌜p ∧ q⌝ := by
  apply Entails.antisymm
  · apply Entails.pure_left; intro hp
    rw [← sepConj_emp ⌜q⌝, ← sepConj_emp ⌜p ∧ q⌝]
    apply Entails.pure_left; intro hq
    exact Entails.pure_right ⟨hp, hq⟩ (Entails.refl _)
  · rw [← sepConj_emp ⌜p ∧ q⌝]
    apply Entails.pure_left; rintro ⟨hp, hq⟩
    rw [← sepConj_emp ⌜q⌝]
    exact Entails.pure_right hp (Entails.pure_right hq (Entails.refl _))

theorem fp_eq_fsp_add (s0 : State) :
    s0.sp - 0x60#64 = (s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x480#64 := by
  simp only [mainFrameSize]
  bv_omega

theorem fsp_fp_sub_40 (fsp : BitVec 64) : (fsp + 0x480#64) - 40#64 = fsp + 0x458#64 := by
  bv_omega

theorem addr_add_40_add_48 (a : BitVec 64) :
    (a + 0x28#64) + 48#64 = (a + 48#64) + 0x28#64 := by
  bv_omega

theorem addr_add_32_add_48 (a : BitVec 64) :
    (a + 0x20#64) + 48#64 = (a + 48#64) + 0x20#64 := by
  bv_omega

theorem stride48_bv (v : BitVec 64) :
    ((v + (v <<< 1#64)) <<< 4#64) = v * 48#64 := by
  bv_kernel

theorem stride48_mul_eq (n : Nat) (_h : n < 2 ^ 58) :
    ((BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1#64)) <<< 4#64) =
      BitVec.ofNat 64 (n * 48) := by
  rw [stride48_bv]
  exact (BitVec.ofNat_mul n 48).symm

theorem ubfm_60_59_eq_shl4 (v : BitVec 64) :
    BitVec.extractLsb' 0 60 v ++ 0#4 = v <<< 4#64 := by
  bv_kernel

/-- Collapse writable byte slice `(p ↦ₛ bs)` into `memRegion p bs.length`. -/
theorem bytes_entails_memRegion (p : BitVec 64) (bs : List (BitVec 8)) :
    (p ↦ₛ bs) ⊢ memRegion p bs.length :=
  ProofLib.pointsToBytes_entails_memRegion p bs

/-- Expose `vecHeader` and optional `A.live ∗ memRegion` from `vecU8At` for deallocation. -/
theorem vecU8At_entails_dealloc (A : RustAlloc) (v c p : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v c p bs ⊢
      vecHeader v c p (BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ c.toNat ∧ c.toNat < 2 ^ 63 ∧ p ≠ 0#64⌝ ∗
          (if c = 0#64 then emp else A.live p c.toNat 1 ∗ memRegion p c.toNat)) := by
  unfold vecU8At
  apply sepConj_mono_right
  apply Entails.pure_left; rintro ⟨hle, hlt, hp⟩
  apply Entails.pure_right ⟨hle, hlt, hp⟩
  by_cases hc : c = 0
  · subst hc; exact Entails.refl _
  · have hc' : c ≠ 0#64 := hc
    simp only [hc, hc', ↓reduceIte]
    apply sepConj_mono_right
    have hsplit :
        memRegion p c.toNat =
          memRegion p bs.length ∗ memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length) := by
      conv => lhs; rw [show c.toNat = bs.length + (c.toNat - bs.length) by omega]
      exact ProofLib.memRegion_split p bs.length (c.toNat - bs.length) (by omega)
    rw [hsplit]
    exact sepConj_mono_left (bytes_entails_memRegion p bs)

/-- Residual ownership of `ownedBytes A cap ptr len bs` when `(ptr ↦ₛ bs)` is borrowed out. -/
def m5OwnedBytesRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

/-- Borrow `(ptr ↦ₛ bs)` cleanly out of `ownedBytes` with no `cap = 0` case split. -/
theorem ownedBytes_borrow (A : RustAlloc) (cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes A cap ptr len bs =
      ⌜len = BitVec.ofNat 64 bs.length ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (ptr ↦ₛ bs) ∗ m5OwnedBytesRest A cap ptr bs := by
  unfold ownedBytes m5OwnedBytesRest
  by_cases hcap : cap = 0
  · subst hcap
    simp only [↓reduceIte, sepConj_emp]
    by_cases hbs : bs = []
    · subst hbs
      rw [pointsToBytes_nil, sepConj_emp]
    · have hpos : 0 < bs.length := List.length_pos_of_ne_nil hbs
      apply Entails.antisymm
      · rw [← sepConj_emp ⌜_⌝]
        apply Entails.pure_left; rintro ⟨_, hle, _, _⟩
        change bs.length ≤ 0 at hle; omega
      · apply Entails.pure_left; rintro ⟨_, hle, _, _⟩
        change bs.length ≤ 0 at hle; omega
  · simp only [hcap, ↓reduceIte]
    ac_rfl

/-- Package an exact-capacity allocation `A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)` (`bs ≠ []`) into
`ownedBytes A (BitVec.ofNat 64 bs.length) ptr (BitVec.ofNat 64 bs.length) bs`. -/
theorem ownedBytes_of_live_bytes (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hptr : ptr ≠ 0) :
    A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs) ⊢
      ownedBytes A (BitVec.ofNat 64 bs.length) ptr (BitVec.ofNat 64 bs.length) bs := by
  have hcap_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0
    have h1 : (BitVec.ofNat 64 bs.length).toNat = (0 : BitVec 64).toNat := congrArg BitVec.toNat h0
    have h0t : (0 : BitVec 64).toNat = 0 := rfl
    rw [hcap_toNat, h0t] at h1
    omega
  unfold ownedBytes
  apply Entails.pure_right ⟨rfl, by omega, by omega, hptr⟩
  simp only [hcap_ne, ↓reduceIte, hcap_toNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.of_eq (by ac_rfl)

/-- Convert `vecU8` at `v` into `vecHeader` + `ownedBytes`. -/
theorem vecU8_eq_header_ownedBytes (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
          ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs := by
  unfold vecU8 vecU8At ownedBytes
  congr 1; funext cap; congr 1; funext ptr
  simp only [true_and]

/-- Package `vecU8RestAt A cap ptr bs` into `ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs`. -/
theorem ownedBytes_of_vecU8RestAt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    vecU8RestAt A cap ptr bs ⊢
      ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs := by
  unfold vecU8RestAt ownedBytes
  exact Entails.pure_right ⟨rfl, hle, hlt, hptr⟩ (Entails.refl _)

/-- Focus element `e` at `done.length * stride` inside `arrayAt elem stride curPtr (done ++ e :: rest)`. -/
theorem arrayAt_focus {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (curPtr : BitVec 64) (done : List α) (e : α) (rest : List α) :
    arrayAt elem stride curPtr (done ++ e :: rest) =
      elem e (curPtr + BitVec.ofNat 64 (done.length * stride)) ∗
        (arrayAt elem stride curPtr done ∗
          arrayAt elem stride (curPtr + BitVec.ofNat 64 ((done.length + 1) * stride)) rest) := by
  induction done generalizing curPtr with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_mul, Nat.zero_add, Nat.one_mul, arrayAt]
    have hz : curPtr + BitVec.ofNat 64 0 = curPtr := BitVec.add_zero curPtr
    rw [hz]
    ac_rfl
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, arrayAt, ih (curPtr + BitVec.ofNat 64 stride)]
    have h1 : (curPtr + BitVec.ofNat 64 stride) + BitVec.ofNat 64 (xs.length * stride) =
        curPtr + BitVec.ofNat 64 ((xs.length + 1) * stride) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact congrArg (curPtr + ·) (congrArg (BitVec.ofNat 64)
        ((Nat.add_comm (xs.length * stride) stride).symm.trans (Nat.succ_mul xs.length stride).symm))
    have h2 : (curPtr + BitVec.ofNat 64 stride) + BitVec.ofNat 64 ((xs.length + 1) * stride) =
        curPtr + BitVec.ofNat 64 ((xs.length + 1 + 1) * stride) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact congrArg (curPtr + ·) (congrArg (BitVec.ofNat 64)
        ((Nat.add_comm ((xs.length + 1) * stride) stride).symm.trans
          (Nat.succ_mul (xs.length + 1) stride).symm))
    rw [h1, h2]
    ac_rfl

/-- Frame left behind when entry `e` at `done.length * 48` is borrowed from
`vecBuf A 48 8 (dirEntryAt A) curCap curPtr (done ++ e :: rest)`. -/
def entryBorrowRest (A : RustAlloc) (curCap curPtr : BitVec 64)
    (done : List (List (BitVec 8) × List (BitVec 8)))
    (e : List (BitVec 8) × List (BitVec 8))
    (rest : List (List (BitVec 8) × List (BitVec 8)))
    (c1 p1 c2 p2 : BitVec 64) : SepProp :=
  ⌜(e.1.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0) ∧
    (e.2.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0) ∧
    ((done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63 ∧ curPtr ≠ 0)⌝ ∗
    m5OwnedBytesRest A c1 p1 e.1 ∗
    m5OwnedBytesRest A c2 p2 e.2 ∗
    arrayAt (dirEntryAt A) 48 curPtr done ∗
    arrayAt (dirEntryAt A) 48 (curPtr + BitVec.ofNat 64 ((done.length + 1) * 48)) rest ∗
    (if curCap = 0 then emp
     else A.live curPtr (curCap.toNat * 48) 8 ∗
       memRegion (curPtr + BitVec.ofNat 64 ((done ++ e :: rest).length * 48))
         ((curCap.toNat - (done ++ e :: rest).length) * 48))

/-- Exact borrow/unborrow identity for `e = (name, bs)` at `base = curPtr + 48 * done.length` inside
`vecBuf A 48 8 (dirEntryAt A) curCap curPtr (done ++ e :: rest)`. -/
theorem vecBuf_borrow_eq (A : RustAlloc) (curCap curPtr : BitVec 64)
    (done : List (List (BitVec 8) × List (BitVec 8)))
    (e : List (BitVec 8) × List (BitVec 8))
    (rest : List (List (BitVec 8) × List (BitVec 8))) :
    vecBuf A 48 8 (dirEntryAt A) curCap curPtr (done ++ e :: rest) =
      ∃∗ c1 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ p2 : BitVec 64,
        vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
          vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
            (BitVec.ofNat 64 e.2.length) ∗
          (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
          entryBorrowRest A curCap curPtr done e rest c1 p1 c2 p2 := by
  by_cases hcap : curCap = 0
  · subst hcap
    have hpos : 0 < (done ++ e :: rest).length := by simp
    apply Entails.antisymm
    · unfold vecBuf
      apply Entails.pure_left; rintro ⟨hle, _, _⟩
      change (done ++ e :: rest).length ≤ 0 at hle; omega
    · apply Entails.sepExists_elim; intro c1
      apply Entails.sepExists_elim; intro p1
      apply Entails.sepExists_elim; intro c2
      apply Entails.sepExists_elim; intro p2
      unfold entryBorrowRest
      have hfront :
          vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1
              (BitVec.ofNat 64 e.1.length) ∗
            vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
              (BitVec.ofNat 64 e.2.length) ∗
            (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
            ⌜(e.1.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0) ∧
              (e.2.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0) ∧
              ((done ++ e :: rest).length ≤ (0 : BitVec 64).toNat ∧
                (0 : BitVec 64).toNat * 48 < 2 ^ 63 ∧ curPtr ≠ 0)⌝ ∗
            m5OwnedBytesRest A c1 p1 e.1 ∗ m5OwnedBytesRest A c2 p2 e.2 ∗
            arrayAt (dirEntryAt A) 48 curPtr done ∗
            arrayAt (dirEntryAt A) 48 (curPtr + BitVec.ofNat 64 ((done.length + 1) * 48)) rest ∗
            (if (0 : BitVec 64) = 0 then emp
             else A.live curPtr ((0 : BitVec 64).toNat * 48) 8 ∗
               memRegion (curPtr + BitVec.ofNat 64 ((done ++ e :: rest).length * 48))
                 (((0 : BitVec 64).toNat - (done ++ e :: rest).length) * 48)) =
          ⌜(e.1.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0) ∧
            (e.2.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0) ∧
            ((done ++ e :: rest).length ≤ (0 : BitVec 64).toNat ∧
              (0 : BitVec 64).toNat * 48 < 2 ^ 63 ∧ curPtr ≠ 0)⌝ ∗
          (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1
              (BitVec.ofNat 64 e.1.length) ∗
            vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
              (BitVec.ofNat 64 e.2.length) ∗
            (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
            m5OwnedBytesRest A c1 p1 e.1 ∗ m5OwnedBytesRest A c2 p2 e.2 ∗
            arrayAt (dirEntryAt A) 48 curPtr done ∗
            arrayAt (dirEntryAt A) 48 (curPtr + BitVec.ofNat 64 ((done.length + 1) * 48)) rest ∗
            (if (0 : BitVec 64) = 0 then emp
             else A.live curPtr ((0 : BitVec 64).toNat * 48) 8 ∗
               memRegion (curPtr + BitVec.ofNat 64 ((done ++ e :: rest).length * 48))
                 (((0 : BitVec 64).toNat - (done ++ e :: rest).length) * 48))) := by
        ac_rfl
      rw [hfront]
      apply Entails.pure_left; rintro ⟨_, _, hle, _, _⟩
      change (done ++ e :: rest).length ≤ 0 at hle; omega
  · unfold vecBuf entryBorrowRest
    simp only [hcap, ↓reduceIte]
    rw [arrayAt_focus (dirEntryAt A) 48 curPtr done e rest]
    simp only [dirEntryAt, vecU8_eq_header_ownedBytes]
    have hpull :
        ⌜(done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63 ∧ curPtr ≠ 0⌝ ∗
          (A.live curPtr (curCap.toNat * 48) 8 ∗
            (((∃∗ cap, ∃∗ ptr,
                vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) cap ptr
                  (BitVec.ofNat 64 e.1.length) ∗
                ownedBytes A cap ptr (BitVec.ofNat 64 e.1.length) e.1) ∗
              (∃∗ cap, ∃∗ ptr,
                vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) cap ptr
                  (BitVec.ofNat 64 e.2.length) ∗
                ownedBytes A cap ptr (BitVec.ofNat 64 e.2.length) e.2)) ∗
              (arrayAt (dirEntryAt A) 48 curPtr done ∗
                arrayAt (dirEntryAt A) 48 (curPtr + BitVec.ofNat 64 ((done.length + 1) * 48)) rest)) ∗
            memRegion (curPtr + BitVec.ofNat 64 ((done ++ e :: rest).length * 48))
              ((curCap.toNat - (done ++ e :: rest).length) * 48)) =
        (((∃∗ c1, ∃∗ p1,
            vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1
              (BitVec.ofNat 64 e.1.length) ∗
            ownedBytes A c1 p1 (BitVec.ofNat 64 e.1.length) e.1) ∗
          (∃∗ c2, ∃∗ p2,
            vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
              (BitVec.ofNat 64 e.2.length) ∗
            ownedBytes A c2 p2 (BitVec.ofNat 64 e.2.length) e.2)) ∗
          ⌜(done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63 ∧ curPtr ≠ 0⌝ ∗
          arrayAt (dirEntryAt A) 48 curPtr done ∗
          arrayAt (dirEntryAt A) 48 (curPtr + BitVec.ofNat 64 ((done.length + 1) * 48)) rest ∗
          A.live curPtr (curCap.toNat * 48) 8 ∗
          memRegion (curPtr + BitVec.ofNat 64 ((done ++ e :: rest).length * 48))
            ((curCap.toNat - (done ++ e :: rest).length) * 48)) := by
      ac_rfl
    rw [hpull]
    simp only [sepExists_sepConj_left]
    congr 1; funext c1; congr 1; funext p1
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    congr 1; funext c2; congr 1; funext p2
    rw [ownedBytes_borrow A c1 p1 (BitVec.ofNat 64 e.1.length) e.1,
        ownedBytes_borrow A c2 p2 (BitVec.ofNat 64 e.2.length) e.2]
    simp only [sepConj_assoc, true_and]
    have hgroupL :
        vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1
            (BitVec.ofNat 64 e.1.length) ∗
          ⌜e.1.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0⌝ ∗
          (p1 ↦ₛ e.1) ∗ m5OwnedBytesRest A c1 p1 e.1 ∗
          vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
            (BitVec.ofNat 64 e.2.length) ∗
          ⌜e.2.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0⌝ ∗
          (p2 ↦ₛ e.2) ∗ m5OwnedBytesRest A c2 p2 e.2 ∗
          ⌜(done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63 ∧ curPtr ≠ 0⌝ ∗
          arrayAt (dirEntryAt A) 48 curPtr done ∗
          arrayAt (dirEntryAt A) 48 (curPtr + BitVec.ofNat 64 ((done.length + 1) * 48)) rest ∗
          A.live curPtr (curCap.toNat * 48) 8 ∗
          memRegion (curPtr + BitVec.ofNat 64 ((done ++ e :: rest).length * 48))
            ((curCap.toNat - (done ++ e :: rest).length) * 48) =
        ⌜e.1.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0⌝ ∗
        (⌜e.2.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0⌝ ∗
          (⌜(done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63 ∧ curPtr ≠ 0⌝ ∗
            (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1
                (BitVec.ofNat 64 e.1.length) ∗
              vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
                (BitVec.ofNat 64 e.2.length) ∗
              (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
              m5OwnedBytesRest A c1 p1 e.1 ∗ m5OwnedBytesRest A c2 p2 e.2 ∗
              arrayAt (dirEntryAt A) 48 curPtr done ∗
              arrayAt (dirEntryAt A) 48 (curPtr + BitVec.ofNat 64 ((done.length + 1) * 48)) rest ∗
              A.live curPtr (curCap.toNat * 48) 8 ∗
              memRegion (curPtr + BitVec.ofNat 64 ((done ++ e :: rest).length * 48))
                ((curCap.toNat - (done ++ e :: rest).length) * 48)))) := by
      ac_rfl
    have hgroupR :
        vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1
            (BitVec.ofNat 64 e.1.length) ∗
          vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
            (BitVec.ofNat 64 e.2.length) ∗
          (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
          ⌜(e.1.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0) ∧
            (e.2.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0) ∧
            ((done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63 ∧ curPtr ≠ 0)⌝ ∗
          m5OwnedBytesRest A c1 p1 e.1 ∗ m5OwnedBytesRest A c2 p2 e.2 ∗
          arrayAt (dirEntryAt A) 48 curPtr done ∗
          arrayAt (dirEntryAt A) 48 (curPtr + BitVec.ofNat 64 ((done.length + 1) * 48)) rest ∗
          A.live curPtr (curCap.toNat * 48) 8 ∗
          memRegion (curPtr + BitVec.ofNat 64 ((done ++ e :: rest).length * 48))
            ((curCap.toNat - (done ++ e :: rest).length) * 48) =
        ⌜(e.1.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0) ∧
          (e.2.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0) ∧
          ((done ++ e :: rest).length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63 ∧ curPtr ≠ 0)⌝ ∗
        (vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1
            (BitVec.ofNat 64 e.1.length) ∗
          vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
            (BitVec.ofNat 64 e.2.length) ∗
          (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
          m5OwnedBytesRest A c1 p1 e.1 ∗ m5OwnedBytesRest A c2 p2 e.2 ∗
          arrayAt (dirEntryAt A) 48 curPtr done ∗
          arrayAt (dirEntryAt A) 48 (curPtr + BitVec.ofNat 64 ((done.length + 1) * 48)) rest ∗
          A.live curPtr (curCap.toNat * 48) 8 ∗
          memRegion (curPtr + BitVec.ofNat 64 ((done ++ e :: rest).length * 48))
            ((curCap.toNat - (done ++ e :: rest).length) * 48)) := by
      ac_rfl
    rw [hgroupL, hgroupR]
    apply Entails.antisymm
    · apply Entails.pure_left; intro h1
      apply Entails.pure_left; intro h2
      apply Entails.pure_left; intro h3
      exact Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _)
    · apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
      exact Entails.pure_right h1 (Entails.pure_right h2 (Entails.pure_right h3 (Entails.refl _)))

theorem vecBuf_unborrow (A : RustAlloc) (curCap curPtr : BitVec 64)
    (done : List (List (BitVec 8) × List (BitVec 8)))
    (e : List (BitVec 8) × List (BitVec 8))
    (rest : List (List (BitVec 8) × List (BitVec 8)))
    (c1 p1 c2 p2 : BitVec 64) :
    vecHeader (curPtr + BitVec.ofNat 64 (done.length * 48)) c1 p1 (BitVec.ofNat 64 e.1.length) ∗
      vecHeader ((curPtr + BitVec.ofNat 64 (done.length * 48)) + 0x18#64) c2 p2
        (BitVec.ofNat 64 e.2.length) ∗
      (p1 ↦ₛ e.1) ∗ (p2 ↦ₛ e.2) ∗
      entryBorrowRest A curCap curPtr done e rest c1 p1 c2 p2 ⊢
      vecBuf A 48 8 (dirEntryAt A) curCap curPtr (done ++ e :: rest) := by
  rw [vecBuf_borrow_eq A curCap curPtr done e rest]
  exact Entails.sepExists_right c1 <| Entails.sepExists_right p1 <|
    Entails.sepExists_right c2 <| Entails.sepExists_right p2 (Entails.refl _)

/-- Unpack `dirAt A d g` into its 5 stack words (`0x00 .. 0x28`), `(dPathPtr ↦ᵣ g.path)`, and
`vecBuf A 48 8 (dirEntryAt A) curCap curPtr g.changed`. -/
theorem dirAt_unpack (A : RustAlloc) (d : BitVec 64) (g : DirGhost) :
    dirAt A d g =
      ∃∗ dPathPtr : BitVec 64, ∃∗ curCap : BitVec 64, ∃∗ curPtr : BitVec 64,
        ((d ↦₆₄ curCap) ∗
          ((d + 0x08#64) ↦₆₄ curPtr) ∗
          ((d + 0x10#64) ↦₆₄ BitVec.ofNat 64 g.changed.length) ∗
          ((d + 0x18#64) ↦₆₄ dPathPtr) ∗
          ((d + 0x20#64) ↦₆₄ BitVec.ofNat 64 g.path.length)) ∗
        (dPathPtr ↦ᵣ g.path) ∗
        vecBuf A 48 8 (dirEntryAt A) curCap curPtr g.changed := by
  unfold dirAt RustHeap.vecOf vecAt vecHeader strRefAt
  have h18 : (d + 0x18#64) + asm64% boxSliceLenOff = d + 0x20#64 := by bv_omega
  simp only [h18, sepExists_sepConj_left, sepExists_sepConj_right]
  congr 1; funext dPathPtr; congr 1; funext curCap; congr 1; funext curPtr
  ac_rfl

/-- Collapse the 5 stack words of a `Dir` header at `d` into `memRegion d 0x28`. -/
theorem dirHeader_entails_memRegion (d w0 w1 w2 w3 w4 : BitVec 64) :
    ((d ↦₆₄ w0) ∗ ((d + 0x08#64) ↦₆₄ w1) ∗ ((d + 0x10#64) ↦₆₄ w2) ∗
      ((d + 0x18#64) ↦₆₄ w3) ∗ ((d + 0x20#64) ↦₆₄ w4)) ⊢ memRegion d 0x28 := by
  have hcell :
      ((d ↦₆₄ w0) ∗ ((d + 0x08#64) ↦₆₄ w1) ∗ ((d + 0x10#64) ↦₆₄ w2) ∗
        ((d + 0x18#64) ↦₆₄ w3) ∗ ((d + 0x20#64) ↦₆₄ w4)) ⊢ cells d 5 := by
    simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w0 <| sepConj_mono_right <|
      Entails.sepExists_right w1 <| sepConj_mono_right <|
      Entails.sepExists_right w2 <| sepConj_mono_right <|
      Entails.sepExists_right w3 <| sepConj_mono_right <|
      Entails.sepExists_right w4 (Entails.refl _)
  rw [show (0x28 : Nat) = 8 * 5 by rfl, ProofLib.memRegion_cells d 5 (by decide)]
  exact hcell

/-- Collapse a `vecHeader` (`24` bytes) into `memRegion a 24`. -/
theorem vecHeader_entails_memRegion (a c p l : BitVec 64) :
    vecHeader a c p l ⊢ memRegion a 24 := by
  unfold vecHeader
  rw [memRegion_24_cells a]
  exact Entails.sepExists_right l <| Entails.sepExists_right p <|
    Entails.sepExists_right c (Entails.refl _)

/-- Collapse two `vecHeader`s at `a` and `a + 0x18` into `memRegion a 48`. -/
theorem entryHeaders_entails_memRegion (a c1 p1 l1 c2 p2 l2 : BitVec 64) :
    vecHeader a c1 p1 l1 ∗ vecHeader (a + 0x18#64) c2 p2 l2 ⊢ memRegion a 48 := by
  rw [show (48 : Nat) = 24 + 24 by rfl, ProofLib.memRegion_split a 24 24 (by decide)]
  exact sepConj_mono (vecHeader_entails_memRegion a c1 p1 l1)
    (vecHeader_entails_memRegion (a + 0x18#64) c2 p2 l2)

/-! ## 3. Shared `pathOf` & `commitFiles` Entry-Stepping Helpers -/

@[simp]
theorem pathOf_nil (name : List (BitVec 8)) : pathOf [] name = name := rfl

theorem pathOf_ne_nil {dir : List (BitVec 8)} (h : dir ≠ []) (name : List (BitVec 8)) :
    pathOf dir name = (dir ++ [0x2f#8]) ++ name := by
  unfold pathOf
  have hslash : utf8 "/" = [0x2f#8] := by decide +kernel
  simp only [h, ↓reduceIte, hslash, List.append_assoc]

theorem dir_entry_path_ok_len {io : IoModel} {g : StoresGhost} {k : Nat} (hk : k < 8)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    {e : List (BitVec 8) × List (BitVec 8)}
    (he : e ∈ ((storesDirs g)[k]'(by simp [hk])).changed) :
    io.pathOk (pathOf ((storesDirs g)[k]'(by simp [hk])).path e.1) ∧
      (pathOf ((storesDirs g)[k]'(by simp [hk])).path e.1).length < 2 ^ 32 :=
  hpaths _ (mem_writes_of_dir_entry hk he)

theorem commitFiles_entry_ok {wr : WriteRule} {F0 F F' : FsFiles}
    {g : StoresGhost} {k : Nat} (hk : k < 8)
    {done : List (List (BitVec 8) × List (BitVec 8))}
    {e : List (BitVec 8) × List (BitVec 8)}
    (hcur : commitFiles wr F0
      (writesBefore g k ++
        done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) = some F)
    (hwr : wr F (pathOf ((storesDirs g)[k]'(by simp [hk])).path e.1) e.2 = some F') :
    commitFiles wr F0
      (writesBefore g k ++
        (done ++ [e]).map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) =
      some F' := by
  simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc]
  exact commitFiles_step_ok hcur hwr

theorem commitFiles_entry_err {wr : WriteRule} {F0 F : FsFiles}
    {g : StoresGhost} {k : Nat} (hk : k < 8)
    {done rest : List (List (BitVec 8) × List (BitVec 8))}
    {e : List (BitVec 8) × List (BitVec 8)}
    (hsplit : ((storesDirs g)[k]'(by simp [hk])).changed = done ++ e :: rest)
    (hcur : commitFiles wr F0
      (writesBefore g k ++
        done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2))) = some F)
    (herr : wr F (pathOf ((storesDirs g)[k]'(by simp [hk])).path e.1) e.2 = none) :
    commitFiles wr F0 g.writes = none := by
  rw [writes_eq_writesBefore_append_writesFrom g k, writesFrom_eq_cons hk]
  unfold DirGhost.writes
  rw [hsplit, List.map_append, List.map_cons]
  simp only [List.append_assoc, List.cons_append]
  rw [← List.append_assoc (writesBefore g k) (List.map _ done)]
  exact commitFiles_step_err
    (pw := (pathOf ((storesDirs g)[k]'(by simp [hk])).path e.1, e.2)) hcur herr

theorem writesBefore_entry_done {g : StoresGhost} {k : Nat} (hk : k < 8)
    {done : List (List (BitVec 8) × List (BitVec 8))}
    (hdone : ((storesDirs g)[k]'(by simp [hk])).changed = done) :
    writesBefore g k ++
      done.map (fun x => (pathOf ((storesDirs g)[k]'(by simp [hk])).path x.1, x.2)) =
      writesBefore g (k + 1) := by
  rw [writesBefore_succ hk]
  unfold DirGhost.writes
  rw [hdone]

end CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
