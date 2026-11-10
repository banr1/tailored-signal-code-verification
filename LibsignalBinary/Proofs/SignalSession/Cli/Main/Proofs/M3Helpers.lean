/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Frame
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# Arithmetic, Heap, and Error-Path Drop Helpers for `main` Hop M3

Bitvector tag-decoding and drop-guard arithmetic lemmas, `ErrHist` trace-invariance helpers,
`ioVecAt` / `ownedBytes` / `mainLits` separation-logic unpackers, and unplaced error-path drop
continuations for `main`'s Hop M3.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops.M3Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops

/-! ## 1. Pure BitVec & Branch Lemmas -/

/-- `zext32 (trunc32 v) = v` when `v.toNat < 2 ^ 32` (`AtCall.x21lo` at `M+0x5b4: orr x21, x28, x21`). -/
theorem zext32_eq_self_of_lt {v : BitVec 64} (h : v.toNat < 2 ^ 32) :
    (v.setWidth 32).setWidth 64 = v := by
  bv_omega

/-- PC-relative `adrp x0, ...; add x0, x0, #0x1a8` at `M+0x5a4 .. M+0x5a8` resolves to
`b + coinsLitOff` for any 4 KiB-aligned image base `b`. -/
theorem adrp_coins_ok {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "main")) :
    (((fnBase + 0x5a4#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% (153 * 4096) - page% (ls_off% "main" + 0x5a4))) +
      0x1a8#64 =
      b + coinsLitOff := by
  subst hfn
  dsimp only [coinsLitOff]
  bv_bits

/-- For any capacity `cap` with `cap.toNat < 2 ^ 63`, `cmn cap, #1` (`adds xzr, cap, #1`) does not set `Z`. -/
theorem cmn_neg1_ne_of_lt {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  bv_omega

/-- Boolean form of `cmn_neg1_ne_of_lt`. -/
theorem beq_add_one_zero_false_of_lt {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact cmn_neg1_ne_of_lt h

/-- For `cap = 0xffffffffffffffff#64` (`Err` niche), `sub x8, cap, #1; cmn x8, #2` sets unsigned carry `C = 1`
(`(cap - 1).toNat + 2 ≥ 2 ^ 64`), skipping `dealloc`. -/
theorem drop_guard_carry_neg1 :
    (0xffffffffffffffff#64 - 1#64).toNat + (2#64).toNat ≥ 2 ^ 64 := by
  decide

/-- For `cap = 0#64` (empty `Vec`), `sub x8, cap, #1; cmn x8, #2` sets unsigned carry `C = 1`,
skipping `dealloc`. -/
theorem drop_guard_carry_zero :
    (0#64 - 1#64).toNat + (2#64).toNat ≥ 2 ^ 64 := by
  decide

/-- For `cap ≠ 0#64` with `cap.toNat < 2 ^ 63` (allocated `Vec`), `sub x8, cap, #1; cmn x8, #2`
clears unsigned carry (`C = 0`, `(cap - 1).toNat + 2 < 2 ^ 64`), taking `dealloc`. -/
theorem drop_guard_no_carry_of_pos {cap : BitVec 64}
    (hne : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    ¬ ((cap - 1#64).toNat + (2#64).toNat ≥ 2 ^ 64) := by
  have hpos : 0 < cap.toNat := by
    cases Nat.eq_zero_or_pos cap.toNat with
    | inl h0 => exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hne
    | inr hp => exact hp
  have hsub : (cap - 1#64).toNat = cap.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]; simp; omega
  rw [hsub]
  change ¬ (cap.toNat - 1 + 2 ≥ 2 ^ 64)
  omega

/-- For `cap.toNat < 2 ^ 63`, `msb cap = false` (used on `Call::Init` at `M+0x564: cmp x25, #0`). -/
theorem msb_false_of_lt {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap - 0#64).msb = false := by
  rw [BitVec.sub_zero, BitVec.msb_eq_toNat]
  simp only [decide_eq_false_iff_not]
  omega

/-! ## 2. Trace & History Helpers -/

/-- Error history invariant carried from `read_file("coins")` `Err` to `free_args`. -/
def ErrHist (i : Inputs) (_s0 s st : State) : Prop :=
  st.fs.files = (initFsState (cliInputs i)).files ∧ ¬ CoinsReadable i ∧ st.trace = s.trace

theorem ErrHist.of_eq {i : Inputs} {s0 s st st' : State}
    (h : ErrHist i s0 s st) (htr : st'.trace = st.trace) (hfs : st'.fs = st.fs) :
    ErrHist i s0 s st' :=
  ⟨by rw [hfs, h.1], h.2.1, htr.trans h.2.2⟩

theorem ErrHist.of_files_eq {i : Inputs} {s0 s st st' : State}
    (h : ErrHist i s0 s st) (htr : st'.trace = st.trace) (hfiles : st'.fs.files = st.fs.files) :
    ErrHist i s0 s st' :=
  ⟨hfiles.trans h.1, h.2.1, htr.trans h.2.2⟩

/-- Parametric error history invariant carried from `read_file("coins")` / `read_stdin` `Err`
to `free_args`. -/
def ErrHistP (P : Prop) (i : Inputs) (_s0 s st : State) : Prop :=
  st.fs.files = (initFsState (cliInputs i)).files ∧ P ∧ st.trace = s.trace

theorem ErrHistP.of_eq {P : Prop} {i : Inputs} {s0 s st st' : State}
    (h : ErrHistP P i s0 s st) (htr : st'.trace = st.trace) (hfs : st'.fs = st.fs) :
    ErrHistP P i s0 s st' :=
  ⟨by rw [hfs, h.1], h.2.1, htr.trans h.2.2⟩

theorem ErrHistP.of_files_eq {P : Prop} {i : Inputs} {s0 s st st' : State}
    (h : ErrHistP P i s0 s st) (htr : st'.trace = st.trace) (hfiles : st'.fs.files = st.fs.files) :
    ErrHistP P i s0 s st' :=
  ⟨hfiles.trans h.1, h.2.1, htr.trans h.2.2⟩

/-! ## 3. Separation-Logic Helpers (`ioVecAt`, `ownedBytes`, `callHeap`, `mainLits`, Stack) -/

/-- Separation-logic pure & existential elimination/introduction helpers. -/
theorem entails_pure_elim_left {p : Prop} {P Q : SepProp} (h : p → (P ⊢ Q)) :
    (⌜p⌝ ∗ P) ⊢ Q :=
  Entails.pure_left h

theorem entails_pure_intro_left {p : Prop} {P Q : SepProp} (hp : p) (h : P ⊢ Q) :
    P ⊢ (⌜p⌝ ∗ Q) := by
  rw [pure_sepConj_of_true hp Q]
  exact h

theorem entails_pure_intro_right {p : Prop} {P Q : SepProp} (hp : p) (h : P ⊢ Q) :
    P ⊢ (Q ∗ ⌜p⌝) := by
  rw [sepConj_comm Q ⌜p⌝]
  exact entails_pure_intro_left hp h

theorem entails_sepExists_left {α : Type _} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, P x ⊢ Q) : (∃∗ x, P x) ⊢ Q :=
  Entails.sepExists_elim h

theorem sepProp_ext {P Q : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P = Q :=
  sepProp_eq_of_entails h1 h2

/-- Focus the `"coins"` read-only literal in `mainLits img`. -/
def mainLitsRest (img : Obj.Image) : SepProp :=
  dirLits.foldr (fun l P => ((img.base + l.1) ↦ᵣ utf8 l.2) ∗ P) emp

theorem mainLits_eq (img : Obj.Image) :
    mainLits img = ((img.base + coinsLitOff) ↦ᵣ utf8 "coins") ∗ mainLitsRest img :=
  rfl

/-- Unpack `vecU8 A v bs` into its 3 header words plus `ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs`. -/
theorem vecU8_to_ownedBytes (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs := by
  dsimp only [vecU8, vecU8At, vecHeader, ownedBytes]
  refine entails_sepExists_left fun cap => Entails.sepExists_right cap <|
    entails_sepExists_left fun ptr => Entails.sepExists_right ptr ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  apply entails_pure_elim_left
  rintro ⟨hle, hlt, hne⟩
  exact entails_pure_intro_left ⟨rfl, hle, hlt, hne⟩ (Entails.refl _)

/-- Split `memRegion (v + 8#64) 16` into two 64-bit cells at `v + 8#64` and `v + 16#64`. -/
theorem memRegion_16_cells (v : BitVec 64) :
    memRegion (v + 8#64) 16 ⊢
      ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
        ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ len) := by
  rw [memRegion_split (v + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight (v + 8#64), ProofLib.memRegion_eight (v + 8#64 + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact entails_sepExists_left fun len => entails_sepExists_left fun ptr =>
    Entails.sepExists_right ptr (Entails.sepExists_right len (Entails.refl _))

/-- Empty `ownedBytes A 0#64 1#64 0#64 []` holds in `emp`. -/
theorem emp_entails_ownedBytes_nil (A : RustAlloc) :
    emp ⊢ ownedBytes A 0#64 1#64 0#64 [] := by
  dsimp only [ownedBytes]
  exact entails_pure_intro_left ⟨rfl, by decide, by decide, by decide⟩ (Entails.refl _)

/-- Extract the pure invariants from `ownedBytes A cap ptr len bs`. -/
theorem ownedBytes_pure (A : RustAlloc) (cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes A cap ptr len bs =
      (⌜len = BitVec.ofNat 64 bs.length ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ownedBytes A cap ptr len bs) := by
  dsimp only [ownedBytes]
  apply sepProp_ext
  · apply entails_pure_elim_left
    intro hp
    exact entails_pure_intro_left hp (entails_pure_intro_left hp (Entails.refl _))
  · apply entails_pure_elim_left
    intro _
    exact Entails.refl _

/-- When `cap = 0#64`, `ownedBytes A cap ptr len bs` carries no spatial heap (`⊢ emp`): the
`cap = 0#64` form of `M4Layout`'s `MainHops.ownedBytes_zero_entails_emp`. -/
theorem ownedBytes_entails_emp_of_cap0 (A : RustAlloc) {cap ptr len : BitVec 64}
    {bs : List (BitVec 8)} (hcap : cap = 0#64) :
    ownedBytes A cap ptr len bs ⊢ emp := by
  subst hcap
  exact MainHops.ownedBytes_zero_entails_emp A ptr len bs

/-- When `cap ≠ 0`, `ownedBytes A cap ptr len bs` supplies `A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat`
for `__rust_dealloc(ptr, cap, 1)`. -/
theorem ownedBytes_to_dealloc (A : RustAlloc) {cap ptr len : BitVec 64} {bs : List (BitVec 8)}
    (hcap : cap ≠ 0#64) :
    ownedBytes A cap ptr len bs ⊢ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  dsimp only [ownedBytes]
  apply entails_pure_elim_left
  rintro ⟨-, hle, hlt, -⟩
  simp only [show (cap = 0) = False from eq_false hcap, ↓reduceIte]
  refine sepConj_mono_right ?_
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
    refine ProofLib.memRegion_split' (b := ptr) (b' := ptr + BitVec.ofNat 64 bs.length)
      (N := cap.toNat) (n := bs.length) (k := cap.toNat - bs.length) (by omega) rfl (by omega)
  rw [hsplit]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

/-- Unified optional owned-buffer predicate for the error-path drop block at `M+0xa50`:
holds either `ownedBytes A cap ptr len bs` (when `ok = true`) or `emp` with `cap = -1` (when `ok = false`). -/
def optOwnedBytes (A : RustAlloc) (ok : Bool) (cap ptr : BitVec 64) : SepProp :=
  if ok then
    ∃∗ len : BitVec 64, ∃∗ bs : List (BitVec 8), ownedBytes A cap ptr len bs
  else
    ⌜cap = 0xffffffffffffffff#64⌝

theorem ownedBytes_entails_optOwned (A : RustAlloc) (cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes A cap ptr len bs ⊢ optOwnedBytes A true cap ptr := by
  dsimp only [optOwnedBytes]
  exact Entails.sepExists_right len (Entails.sepExists_right bs (Entails.refl _))

/-- Split sub-callee stack `stackAt sp sub` for a hook needing `k ≤ sub` bytes (`k ≤ sub`, `sub ≤ 2^64`). -/
theorem stackAt_sub_split (sp : BitVec 64) {k sub : Nat} (hle : k ≤ sub) (h64 : sub ≤ 2 ^ 64) :
    stackAt sp sub = memRegion (sp - BitVec.ofNat 64 sub) (sub - k) ∗ stackAt sp k :=
  stackAt_split_ge sp hle h64

end CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
