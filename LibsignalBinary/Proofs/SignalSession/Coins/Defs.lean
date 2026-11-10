/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- shake: keep

/-!
# Coins Tape Predicates and `signal_session_coins_fill` Specification

Defines the two-cell randomness tape (`tapeAt2`, `tapeAfter2`), the image-static instances
`coinsAt` / `coinsAfter` at `signal_session::coins::{NEXT, LEFT}`, and the Hoare contracts
`coinsFillSpec` and `coinsFillAtSpec` for `signal_session_coins_fill(dst, len)`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Coins

open Arm64 ProofLib
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

/-! ## 1. The two-cell tape -/

/-- The tape with cursor cell `nx`, remaining-count cell `lf` and the remaining bytes `rest` at the
cursor `cur`. -/
def tapeAt2 (nx lf cur : BitVec 64) (rest : List (BitVec 8)) : SepProp :=
  ⌜rest.length < 2 ^ 63⌝ ∗ (nx ↦₆₄ cur) ∗ (lf ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (cur ↦ₛ rest)

/-- The tape after `k` bytes were drawn: cursor `cur + k`, remaining count `rest.length - k`. The drawn
bytes stay owned (read-only for the program). -/
def tapeAfter2 (nx lf cur : BitVec 64) (rest : List (BitVec 8)) (k : Nat) : SepProp :=
  (nx ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗ (lf ↦₆₄ BitVec.ofNat 64 (rest.length - k)) ∗ (cur ↦ₛ rest)

theorem tapeAt_eq_tapeAt2 (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest = tapeAt2 ctl (ctl + 8#64) cur rest :=
  rfl

theorem tapeAfter_eq_tapeAfter2 (ctl cur : BitVec 64) (rest : List (BitVec 8)) (k : Nat) :
    tapeAfter ctl cur rest k = tapeAfter2 ctl (ctl + 8#64) cur rest k :=
  rfl

/-- `tapeAfter2 nx lf cur rest 0` is the tape without the `< 2 ^ 63` side condition. -/
theorem tapeAfter2_zero_eq (nx lf cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAfter2 nx lf cur rest 0 =
      (nx ↦₆₄ cur) ∗ (lf ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (cur ↦ₛ rest) := by
  unfold tapeAfter2
  simp only [BitVec.add_zero, Nat.sub_zero]

/-! ## 2. The coins statics of the image loaded at `b` -/

/-- `signal_session::coins::NEXT` (the cursor, `.data`) of the image loaded at `b`. -/
abbrev coinsNext (b : BitVec 64) : BitVec 64 := b + bv% (ls_sym% "libsignal_cli::coins::NEXT.0")

/-- `signal_session::coins::LEFT` (the remaining count, `.bss`) of the image loaded at `b`. -/
abbrev coinsLeft (b : BitVec 64) : BitVec 64 := b + bv% (ls_sym% "libsignal_cli::coins::LEFT.0")

/-- The coins tape of the image loaded at `b`. -/
abbrev coinsAt (b cur : BitVec 64) (rest : List (BitVec 8)) : SepProp :=
  tapeAt2 (coinsNext b) (coinsLeft b) cur rest

/-- The coins tape of the image loaded at `b` after `k` draws. -/
abbrev coinsAfter (b cur : BitVec 64) (rest : List (BitVec 8)) (k : Nat) : SepProp :=
  tapeAfter2 (coinsNext b) (coinsLeft b) cur rest k

/-- The function that draws from the coins tape. -/
abbrev coinsFillName : String := "signal_session_coins_fill"

/-! ## 3. The callee spec -/

/-- Spec of `signal_session_coins_fill` from `coinsAfter b cur rest 0` (no `rest.length < 2 ^ 63`
side condition needed, as for `rngFillAfter0Spec`): fill `dst[0, len)` with the next
`min len rest.length` tape bytes, then zeros; advance the tape. `stk` free stack bytes below the entry
`sp` are lent to the callee (it uses `0x50`) and given back. Ghost: `(dst, len, cur, rest)`. -/
def coinsFillSpec (b : BitVec 64) (stk : Nat) :
    Spec (BitVec 64 × Nat × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, len, cur, rest) s =>
    ⌜s.readReg64 .x0 = dst ∧ (s.readReg64 .x1).toNat = len⌝ ∗
      memRegion dst len ∗ coinsAfter b cur rest 0 ∗ stackAt s.sp stk
  post := fun (dst, len, cur, rest) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ (rest ++ List.replicate len 0#8).take len) ∗
      coinsAfter b cur rest (min len rest.length) ∗ stackAt s0.sp stk

/-- `coinsFillSpec` with the tape ghost `(cur, rest)` fixed (ghost: `(dst, len)`). -/
def coinsFillAtSpec (b : BitVec 64) (stk : Nat) (cur : BitVec 64) (rest : List (BitVec 8)) :
    Spec (BitVec 64 × Nat) where
  pre := fun (dst, len) s =>
    ⌜s.readReg64 .x0 = dst ∧ (s.readReg64 .x1).toNat = len⌝ ∗
      memRegion dst len ∗ coinsAfter b cur rest 0 ∗ stackAt s.sp stk
  post := fun (dst, len) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ (rest ++ List.replicate len 0#8).take len) ∗
      coinsAfter b cur rest (min len rest.length) ∗ stackAt s0.sp stk

theorem coinsFillAt_of_after0 {P : Program} {addr b cur : BitVec 64} {stk : Nat}
    {rest : List (BitVec 8)} (h : subroutine_ok P addr (coinsFillSpec b stk)) :
    subroutine_ok P addr (coinsFillAtSpec b stk cur rest) := by
  refine subroutine_ok_outcome_intro fun ⟨dst, len⟩ R s0 hpc hrun hpre hsp => ?_
  exact h.mono_outcome (dst, len, cur, rest) R s0 hpc hrun hpre hsp fun _ hout => hout

end CryptoVerification.SignalSession.Coins
