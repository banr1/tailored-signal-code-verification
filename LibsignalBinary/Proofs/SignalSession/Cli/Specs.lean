/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Kits
public import LibsignalBinary.Proofs.SpqrV1.Chain.Defs
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Specifications for `signal_session::stores::{path, decimal}`

Defines function-level specifications (`pathSpec`, `decimalSpec`) for `signal_session::stores::path`
and `signal_session::stores::decimal` against the pure path and decimal-formatting operations of
`Cli/Kits.lean`:
- `path(dir: &str, name: &str) -> String`: sret in `x0`, `dir` in `(x1, x2)`, `name` in `(x3, x4)`,
  frame `0x70`, returning a fresh `String` with bytes `dir ++ "/" ++ name` (`pathOf dir name` when
  `dir ≠ []`) while preserving read-only or owned input slices (`ChainProofs.bytesAt ro`).
- `decimal(n: u32) -> String`: sret in `x0`, `n` in `w1`, frame `0x50` (recursion depth `≤ 10` for
  `u32`), returning a fresh `String` with ASCII `decimalText n`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## Symbol names and image offset checks -/

/-- `signal_session::stores::path`. -/
abbrev pathName : String := "libsignal_cli::stores::path"

/-- `signal_session::stores::decimal`. -/
abbrev decimalName : String := "libsignal_cli::stores::decimal"

/-- Symbol name of the CLI crate's `RawVecInner::reserve::do_reserve_and_handle` (`[local#9]`). -/
abbrev cliDoReserveName : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"

theorem path_fnOff :
    libsignalSessionCode.fnOff pathName = num% (ls_off% "libsignal_cli::stores::path") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_cli::stores::path")

theorem decimal_fnOff :
    libsignalSessionCode.fnOff decimalName = num% (ls_off% "libsignal_cli::stores::decimal") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_cli::stores::decimal")

theorem cliDoReserve_fnOff :
    libsignalSessionCode.fnOff cliDoReserveName = num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]")

/-! ## `signal_session::stores::path` -/

/-- Ghost arguments for `signal_session::stores::path`: two input slices (each read-only or owned
according to its `ro` flag), output sret pointer, and `do_reserve_and_handle` stack budget `resStack`. -/
structure PathGhost where
  dirA : BitVec 64
  dir : List (BitVec 8)
  dirRo : Bool
  nameA : BitVec 64
  name : List (BitVec 8)
  nameRo : Bool
  ret : BitVec 64

/-- Specification of `signal_session::stores::path`: writes a fresh owned `String` holding
`dir ++ "/" ++ name` to `x0`, returns both input slices (`bytesAt ro`), and panics only on
allocation failure. -/
def pathSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec PathGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.dirA ∧
          (s.readReg64 .x2).toNat = x.dir.length ∧ s.readReg64 .x3 = x.nameA ∧
          (s.readReg64 .x4).toNat = x.name.length ∧
          x.dir.length < 2 ^ 32 ∧ x.name.length < 2 ^ 32⌝ ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ memRegion x.ret 24 ∗
          stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ vecU8 A x.ret (x.dir ++ [0x2f#8] ++ x.name) ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

theorem utf8_slash : utf8 "/" = [0x2f#8] := by decide +kernel

/-- For non-empty `dir`, `pathOf dir name` equals `dir ++ [0x2f#8] ++ name`. -/
theorem pathOf_eq_path {dir : List (BitVec 8)} (h : dir ≠ []) (name : List (BitVec 8)) :
    pathOf dir name = dir ++ [0x2f#8] ++ name := by
  simp only [pathOf, h, ite_false, utf8_slash]

/-! ## `signal_session::stores::decimal` -/

structure DecimalGhost where
  n : BitVec 32
  ret : BitVec 64

/-- Specification of `signal_session::stores::decimal`: writes a fresh owned `String` holding
`decimalText n` to `x0`, requiring `10 * 0x50 + resStack` stack bytes, and panics only on
allocation failure. -/
def decimalSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec DecimalGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg32 .x1 = x.n⌝ ∗ memRegion x.ret 24 ∗
          stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ vecU8 A x.ret (decimalText x.n.toNat) ∗
          stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

end CryptoVerification.SignalSession.Cli
