/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Model
import ProofLib.SepLogic.WP.StateNorm

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops.Proofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

/-!
# Pure Model Lemmas for `main_m2` Subcommand & `u32` Parsing

Pure arithmetic and byte-slice lemmas connecting little-endian command-word comparisons (`"keygen"`,
`"init"`, `"send"`, `"recv"`) and `<u32 as FromStr>::from_str` (`parseUnsigned (2 ^ 32 - 1)`) across
the unrolled `1..8`-digit fast path and overflow-checked multi-digit loop.
-/

theorem utf8_keygen_eq :
    utf8 "keygen" = [107#8, 101#8, 121#8, 103#8, 101#8, 110#8] := by
  decide +kernel

theorem utf8_init_eq :
    utf8 "init" = [105#8, 110#8, 105#8, 116#8] := by
  decide +kernel

theorem utf8_send_eq :
    utf8 "send" = [115#8, 101#8, 110#8, 100#8] := by
  decide +kernel

theorem utf8_recv_eq :
    utf8 "recv" = [114#8, 101#8, 99#8, 118#8] := by
  decide +kernel

theorem append_inj {m k : Nat} {x1 x2 : BitVec m} {y1 y2 : BitVec k}
    (h : y1 ++ x1 = y2 ++ x2) : x1 = x2 ∧ y1 = y2 := by
  constructor
  · ext j hj
    have hbit := congrArg (fun v => v[j]'(by omega)) h
    simpa [BitVec.getElem_append, hj] using hbit
  · ext j hj
    have hbit := congrArg (fun v => v[m + j]'(by omega)) h
    have hnm : ¬ m + j < m := by omega
    simpa [BitVec.getElem_append, hnm] using hbit

theorem append2_inj {b0 b1 c0 c1 : BitVec 8}
    (h : (b1 ++ b0 : BitVec 16) = (c1 ++ c0 : BitVec 16)) : b0 = c0 ∧ b1 = c1 :=
  append_inj h

theorem append4_inj {b0 b1 b2 b3 c0 c1 c2 c3 : BitVec 8}
    (h : (b3 ++ (b2 ++ (b1 ++ b0)) : BitVec 32) = (c3 ++ (c2 ++ (c1 ++ c0)) : BitVec 32)) :
    b0 = c0 ∧ b1 = c1 ∧ b2 = c2 ∧ b3 = c3 := by
  obtain ⟨h012, h3⟩ := append_inj h
  obtain ⟨h01, h2⟩ := append_inj h012
  obtain ⟨h0, h1⟩ := append_inj h01
  exact ⟨h0, h1, h2, h3⟩

theorem le32_send_iff (b0 b1 b2 b3 : BitVec 8) :
    (b3 ++ (b2 ++ (b1 ++ b0)) : BitVec 32) = 0x646e6573#32 ↔
      [b0, b1, b2, b3] = utf8 "send" := by
  rw [utf8_send_eq]
  constructor
  · intro h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := append4_inj (h.trans (by decide :
      0x646e6573#32 = (100#8 ++ (110#8 ++ (101#8 ++ 115#8)))))
    rfl
  · rintro ⟨rfl, rfl, rfl, rfl⟩; decide

theorem le32_recv_iff (b0 b1 b2 b3 : BitVec 8) :
    (b3 ++ (b2 ++ (b1 ++ b0)) : BitVec 32) = 0x76636572#32 ↔
      [b0, b1, b2, b3] = utf8 "recv" := by
  rw [utf8_recv_eq]
  constructor
  · intro h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := append4_inj (h.trans (by decide :
      0x76636572#32 = (118#8 ++ (99#8 ++ (101#8 ++ 114#8)))))
    rfl
  · rintro ⟨rfl, rfl, rfl, rfl⟩; decide

theorem le32_init_iff (b0 b1 b2 b3 : BitVec 8) :
    (b3 ++ (b2 ++ (b1 ++ b0)) : BitVec 32) = 0x74696e69#32 ↔
      [b0, b1, b2, b3] = utf8 "init" := by
  rw [utf8_init_eq]
  constructor
  · intro h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := append4_inj (h.trans (by decide :
      0x74696e69#32 = (116#8 ++ (105#8 ++ (110#8 ++ 105#8)))))
    rfl
  · rintro ⟨rfl, rfl, rfl, rfl⟩; decide

theorem le48_keygen_iff (b0 b1 b2 b3 b4 b5 : BitVec 8) :
    ((b3 ++ (b2 ++ (b1 ++ b0)) : BitVec 32) = 0x6779656b#32 ∧
      (b5 ++ b4 : BitVec 16) = 0x6e65#16) ↔
      [b0, b1, b2, b3, b4, b5] = utf8 "keygen" := by
  rw [utf8_keygen_eq]
  constructor
  · rintro ⟨hw, hh⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := append4_inj (hw.trans (by decide :
      0x6779656b#32 = (103#8 ++ (121#8 ++ (101#8 ++ 107#8)))))
    obtain ⟨rfl, rfl⟩ := append2_inj (hh.trans (by decide :
      0x6e65#16 = (110#8 ++ 101#8)))
    rfl
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; decide

theorem parseArgs_len_ne (uuidParse : UuidParser) (bs : List (List (BitVec 8)))
    (h2 : bs.length ≠ 2) (h3 : bs.length ≠ 3) :
    parseArgs uuidParse bs = none := by
  match bs with
  | [] => rfl
  | [_] => rfl
  | [_, _] => exact absurd rfl h2
  | [_, _, _] => exact absurd rfl h3
  | _ :: _ :: _ :: _ :: _ => rfl

theorem parseArgs_two_bad_cmd (uuidParse : UuidParser) (c a : List (BitVec 8))
    (hsend : c ≠ utf8 "send") (hrecv : c ≠ utf8 "recv") :
    parseArgs uuidParse [c, a] = none := by
  simp only [parseArgs, hsend, hrecv, ↓reduceIte]

theorem parseArgs_three_bad_cmd (uuidParse : UuidParser) (c a x : List (BitVec 8))
    (hkey : c ≠ utf8 "keygen") (hinit : c ≠ utf8 "init") :
    parseArgs uuidParse [c, a, x] = none := by
  simp only [parseArgs, hkey, hinit, ↓reduceIte]

/-! ### Digit & `parseUnsigned (2 ^ 32 - 1)` characterization -/

/-- Exact ARM64 unsigned range-check `((b.zeroExtend 32) - 48#32) ≤ᵤ 9#32 ↔ isDigit b = true`. -/
theorem sub48_ule_9_iff_isDigit (b : BitVec 8) :
    ((b.setWidth 32 - 48#32) ≤ 9#32) ↔ isDigit b = true := by
  simp only [isDigit, decide_eq_true_eq, BitVec.le_def]
  have hb : b.toNat < 256 := b.isLt
  have hsub : (b.setWidth 32 - 48#32).toNat = (b.toNat + 2 ^ 32 - 48) % 2 ^ 32 := by
    bv_omega
  rw [hsub]
  change (b.toNat + 2 ^ 32 - 48) % 2 ^ 32 ≤ 9 ↔ 48 ≤ b.toNat ∧ b.toNat ≤ 57
  omega

theorem sub48_toNat_eq (b : BitVec 8) (hd : isDigit b = true) :
    (b.setWidth 32 - 48#32).toNat = b.toNat - 48 := by
  simp only [isDigit, decide_eq_true_eq] at hd
  bv_omega

/-- Digits stripped of optional leading `'+'`. -/
def stripPlus (bs : List (BitVec 8)) : List (BitVec 8) :=
  match bs with
  | b :: rest => if b = 43#8 then rest else bs
  | [] => []

theorem parseUnsigned_eq_of_stripPlus (bound : Nat) (bs : List (BitVec 8)) :
    parseUnsigned bound bs =
      let ds := stripPlus bs
      if ds = [] ∨ ds.any (fun b => !isDigit b) then none
      else
        let v := ds.foldl (fun acc b => 10 * acc + (b.toNat - 48)) 0
        if v ≤ bound then some v else none := rfl

theorem parseUnsigned_nil (bound : Nat) : parseUnsigned bound [] = none := rfl

theorem parseUnsigned_singleton_plus (bound : Nat) : parseUnsigned bound [43#8] = none := rfl

theorem parseUnsigned_singleton_minus (bound : Nat) : parseUnsigned bound [45#8] = none := rfl

/-- Monotonicity of the decimal foldl accumulator: `acc ≤ foldl f acc rem`. -/
theorem digitFold_le (acc : Nat) (rem : List (BitVec 8)) :
    acc ≤ rem.foldl (fun a b => 10 * a + (b.toNat - 48)) acc := by
  induction rem generalizing acc with
  | nil => exact Nat.le_refl _
  | cons b rest ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (by omega) (ih (10 * acc + (b.toNat - 48)))

/-- If `acc ≥ 2 ^ 32` at any point in `rem.foldl`, then `ds = pref ++ rem` either fails `isDigit`
or overflows `2 ^ 32 - 1`. -/
theorem parseUnsigned_none_of_overflow {bs pref rem : List (BitVec 8)} {acc : Nat}
    (hds : stripPlus bs = pref ++ rem)
    (hacc : acc = pref.foldl (fun a b => 10 * a + (b.toNat - 48)) 0)
    (hover : 2 ^ 32 ≤ acc) :
    parseUnsigned (2 ^ 32 - 1) bs = none := by
  rw [parseUnsigned_eq_of_stripPlus]
  simp only []
  split
  · rfl
  · rw [hds, List.foldl_append, ← hacc]
    have hbig : 2 ^ 32 ≤ rem.foldl (fun a b => 10 * a + (b.toNat - 48)) acc :=
      Nat.le_trans hover (digitFold_le acc rem)
    have hnle : ¬ rem.foldl (fun a b => 10 * a + (b.toNat - 48)) acc ≤ 2 ^ 32 - 1 := by omega
    simp only [hnle, ↓reduceIte]

/-- Same when `10 * acc ≥ 2 ^ 32` and at least one byte `b :: rest` remains. -/
theorem parseUnsigned_none_of_mul10_overflow {bs pref : List (BitVec 8)}
    {b : BitVec 8} {rest : List (BitVec 8)} {acc : Nat}
    (hds : stripPlus bs = pref ++ (b :: rest))
    (hacc : acc = pref.foldl (fun a x => 10 * a + (x.toNat - 48)) 0)
    (hover : 2 ^ 32 ≤ 10 * acc) :
    parseUnsigned (2 ^ 32 - 1) bs = none := by
  apply parseUnsigned_none_of_overflow (pref := pref ++ [b]) (rem := rest)
    (acc := 10 * acc + (b.toNat - 48))
  · simp [hds]
  · simp [List.foldl_append, hacc]
  · omega

/-- If byte `b ∈ stripPlus bs` fails `isDigit`, `parseUnsigned` returns `none`. -/
theorem parseUnsigned_none_of_nonDigit {bound : Nat} {bs : List (BitVec 8)} {b : BitVec 8}
    (hmem : b ∈ stripPlus bs) (hnd : isDigit b = false) :
    parseUnsigned bound bs = none := by
  rw [parseUnsigned_eq_of_stripPlus]
  have hany : (stripPlus bs).any (fun x => !isDigit x) = true :=
    List.any_eq_true.mpr ⟨b, hmem, by simp [hnd]⟩
  simp only [hany, or_true, ↓reduceIte]

/-- If `stripPlus bs ≠ []`, all bytes satisfy `isDigit`, and `foldl = v ≤ bound`, then
`parseUnsigned bound bs = some v`. -/
theorem parseUnsigned_some_of_digits {bound : Nat} {bs : List (BitVec 8)} {v : Nat}
    (hne : stripPlus bs ≠ [])
    (hdig : ∀ b ∈ stripPlus bs, isDigit b = true)
    (hval : (stripPlus bs).foldl (fun a b => 10 * a + (b.toNat - 48)) 0 = v)
    (hle : v ≤ bound) :
    parseUnsigned bound bs = some v := by
  rw [parseUnsigned_eq_of_stripPlus]
  have hany : (stripPlus bs).any (fun x => !isDigit x) = false := by
    rw [List.any_eq_false]
    intro b hb; simp [hdig b hb]
  simp only [hne, hany, Bool.false_eq_true, or_self, ↓reduceIte, hval, hle]

end CryptoVerification.SignalSession.Cli.MainHops.Proofs
