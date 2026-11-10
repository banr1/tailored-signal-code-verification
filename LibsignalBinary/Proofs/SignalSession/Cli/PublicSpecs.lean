/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.BV.ReflectROBDD

/-!
# Function Specifications for `signal_session::public` Helpers

Pure models (`splitId`, `splitSigned`), 48-byte `sret` memory layouts (`splitIdResultAt`,
`splitSignedResultAt`), and subroutine specifications (`splitIdSpec`, `splitSignedSpec`,
`bundleReadSpec`) for `split_id`, `split_signed`, and `read_bundle::{closure#0}`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## Pure Models -/

/-- 32-bit unsigned integer assembled from little-endian bytes `b0 b1 b2 b3`. -/
def ofLe32 (b0 b1 b2 b3 : BitVec 8) : BitVec 32 := b3 ++ b2 ++ b1 ++ b0

/-- Pure model of `split_id(file)`: splits a 4-byte little-endian `u32` ID from the remaining slice, returning `none` if `file.length < 4`. -/
def splitId : List (BitVec 8) → Option (BitVec 32 × List (BitVec 8))
  | b0 :: b1 :: b2 :: b3 :: rest => some (ofLe32 b0 b1 b2 b3, rest)
  | _ => none

/-- Pure model of `split_signed(file)`: applies `splitId`, then splits the remaining slice into `(key, sig)` with a 64-byte trailing signature, returning `none` if `file.length < 68`. -/
def splitSigned (file : List (BitVec 8)) :
    Option (BitVec 32 × List (BitVec 8) × List (BitVec 8)) :=
  match splitId file with
  | none => none
  | some (id, rest) =>
    if 64 ≤ rest.length then some (id, rest.take (rest.length - 64), rest.drop (rest.length - 64))
    else none

theorem ofLe32_le32 (v : BitVec 32) :
    (le32 v).length = 4 ∧
      ∀ h : (le32 v).length = 4,
        ofLe32 ((le32 v)[0]'(by omega)) ((le32 v)[1]'(by omega)) ((le32 v)[2]'(by omega))
          ((le32 v)[3]'(by omega)) = v := by
  refine ⟨rfl, fun _ => ?_⟩
  simp only [le32, ofLe32, List.getElem_cons_zero, List.getElem_cons_succ]
  bv_slice

/-- `splitId` inverts `le32 id ++ key`. -/
theorem splitId_le32 (id : BitVec 32) (key : List (BitVec 8)) :
    splitId (le32 id ++ key) = some (id, key) := by
  have h := (ofLe32_le32 id).2 rfl
  simp only [le32, List.getElem_cons_zero, List.getElem_cons_succ] at h
  simp only [le32, List.cons_append, List.nil_append, splitId, h]

/-- `splitSigned` inverts `le32 id ++ key ++ sig` for any 64-byte signature `sig`. -/
theorem splitSigned_le32 (id : BitVec 32) (key sig : List (BitVec 8)) (hs : sig.length = 64) :
    splitSigned (le32 id ++ key ++ sig) = some (id, key, sig) := by
  rw [List.append_assoc, splitSigned, splitId_le32]
  simp only [List.length_append, hs, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel,
    List.take_left', List.drop_left']

/-! ## Symbol Names -/

abbrev splitIdName : String := "libsignal_cli::public::split_id"

abbrev splitSignedName : String := "libsignal_cli::public::split_signed"

abbrev bundleReadName : String := "libsignal_cli::public::read_bundle::{closure#0}"

/-- CLI crate symbol for `drop_glue::<SignalProtocolError> [local#3]`. -/
abbrev cliDropSpeName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"

theorem splitId_fnOff :
    libsignalSessionCode.fnOff splitIdName = num% (ls_off% "libsignal_cli::public::split_id") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_cli::public::split_id")

theorem splitSigned_fnOff :
    libsignalSessionCode.fnOff splitSignedName =
      num% (ls_off% "libsignal_cli::public::split_signed") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_cli::public::split_signed")

theorem bundleRead_fnOff :
    libsignalSessionCode.fnOff bundleReadName =
      num% (ls_off% "libsignal_cli::public::read_bundle::{closure#0}") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_cli::public::read_bundle::{closure#0}")

theorem cliDropSpe_fnOff :
    libsignalSessionCode.fnOff cliDropSpeName =
      num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")

/-! ## Result Layouts -/

/-- Niche `Ok` tag word (`-2`) for `Result<_, SignalProtocolError>` in `split_id` and `split_signed`. -/
def splitOkTag : BitVec 64 := 0xFFFFFFFFFFFFFFFE#64

/-- 48-byte `sret` layout at `r` for `split_id(fp, file)`: `(splitOkTag, id @ +8, fp + 4 @ +16, len - 4 @ +24)` on `Ok`, or `speAt A (utf8 "bundle") r .invalidState` on `Err`. -/
def splitIdResultAt (A : RustAlloc) (r fp : BitVec 64) (file : List (BitVec 8)) : SepProp :=
  match splitId file with
  | some (id, rest) =>
    (r ↦₆₄ splitOkTag) ∗ ((r + 8#64) ↦₃₂ id) ∗ memRegion (r + 0xc#64) 4 ∗
      ((r + 0x10#64) ↦₆₄ (fp + 4#64)) ∗ ((r + 0x18#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
      memRegion (r + 0x20#64) 16
  | none => speAt A (utf8 "bundle") r .invalidState

/-- 48-byte `sret` layout at `r` for `split_signed(fp, file)`: `(splitOkTag, fp + 4 @ +8, key.len @ +16, id @ +24, fp + 4 + key.len @ +32, 64 @ +40)` on `Ok`, or `speAt A (utf8 "bundle") r .invalidState` on `Err`. -/
def splitSignedResultAt (A : RustAlloc) (r fp : BitVec 64) (file : List (BitVec 8)) : SepProp :=
  match splitSigned file with
  | some (id, key, _) =>
    (r ↦₆₄ splitOkTag) ∗ ((r + 8#64) ↦₆₄ (fp + 4#64)) ∗
      ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 key.length) ∗ ((r + 0x18#64) ↦₃₂ id) ∗
      memRegion (r + 0x1c#64) 4 ∗
      ((r + 0x20#64) ↦₆₄ (fp + 4#64 + BitVec.ofNat 64 key.length)) ∗
      ((r + 0x28#64) ↦₆₄ 64#64)
  | none => speAt A (utf8 "bundle") r .invalidState

/-! ## `split_id` and `split_signed` Specifications -/

/-- Ghost state for `split_id` and `split_signed`: 48-byte `sret` pointer `ret` and borrowed input slice `file` at `fp`. -/
structure SplitGhost where
  ret : BitVec 64
  fp : BitVec 64
  file : List (BitVec 8)
  ro : Bool

/-- Subroutine contract for `split_id` (`0x60`-byte frame): writes `splitIdResultAt` to `x.ret`, returns the input slice, and panics only on allocation failure. -/
def splitIdSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec SplitGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.fp ∧
          (s.readReg64 .x2).toNat = x.file.length⌝ ∗
          SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ memRegion x.ret 48 ∗
          stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ splitIdResultAt A x.ret x.fp x.file ∗
          SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Subroutine contract for `split_signed` (`0x60`-byte frame): writes `splitSignedResultAt` to `x.ret`, returns the input slice, and panics only on allocation failure. -/
def splitSignedSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec SplitGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.fp ∧
          (s.readReg64 .x2).toNat = x.file.length⌝ ∗
          SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ memRegion x.ret 48 ∗
          stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ splitSignedResultAt A x.ret x.fp x.file ∗
          SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## `read_bundle::{closure#0}` Specification -/

/-- Ghost state for `read_bundle::{closure#0}`: 48-byte `sret` pointer `ret`, bundle directory slice `dir`, and entry name slice `name`. -/
structure BundleReadGhost where
  ret : BitVec 64
  dirA : BitVec 64
  dir : List (BitVec 8)
  dirRo : Bool
  nameA : BitVec 64
  name : List (BitVec 8)
  nameRo : Bool

/-- Subroutine contract for `read_bundle::{closure#0}` (`0x50`-byte frame): evaluates `rd` on `dir ++ "/" ++ name` into `getResultAt` at `x.ret`, returns the input slices, and panics only on allocation failure. -/
def bundleReadSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec BundleReadGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.dirA ∧
          (s.readReg64 .x2).toNat = x.dir.length ∧ s.readReg64 .x3 = x.nameA ∧
          (s.readReg64 .x4).toNat = x.name.length ∧ x.dir.length < 2 ^ 32 ∧
          x.name.length < 2 ^ 32 ∧ pathOk (x.dir ++ [0x2f#8] ++ x.name)⌝ ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ memRegion x.ret 48 ∗
          stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜r = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ sf.trace = s0.trace⌝ ∗
            getResultAt A x.ret r) ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

end CryptoVerification.SignalSession.Cli
