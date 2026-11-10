/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliRun
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunFixed

@[expose] public section

set_option autoImplicit false

/-!
# Hook-Table and File-Read Lemmas for `CliRun`

**Checked by Lean.** Relates `cliProg W` to the `Rust.withPanics`-wrapped program form used by
function-level proofs (`cliProg_eq_rebase_withPanics`), proves distinctness and lookup properties of
the 46 stub names in `cliHookTable`, and characterizes `readFileHook` and `read_stdin` via
`readView` and `readStdinResult`.
-/

namespace CryptoVerification.SignalSession

open Arm64

/-- `Rust.withPanics` is idempotent on `E2E.withImagePanics`, since every `Rust.isPanicSymbol`
satisfies `E2E.isImagePanicSymbol`. -/
theorem withPanics_withPanicsE (X : String → Option (State → State)) :
    Rust.withPanics (E2E.withImagePanics X) = E2E.withImagePanics X := by
  funext s
  unfold Rust.withPanics E2E.withImagePanics E2E.isImagePanicSymbol
  by_cases h : Rust.isPanicSymbol s <;> simp [h]

theorem withPanics_cliExterns (W : CliHooks) :
    Rust.withPanics (cliExterns W) = cliExterns W :=
  withPanics_withCliPanics _

/-- Rewrites `cliProg W` as `libsignalSessionCode.rebase cliBase (Rust.withPanics (cliExterns W))`,
matching `contractProg` and `tripleRatchetProgAtExt`. -/
theorem cliProg_eq_rebase_withPanics (W : CliHooks) :
    cliProg W = libsignalSessionCode.rebase cliBase (Rust.withPanics (cliExterns W)) := by
  rw [withPanics_cliExterns]
  rfl

/-! ## Hook-Table Keys and Lookup -/

/-- Ordered list of the 46 stub names in `cliHookTable W` (18 from `E2E.pqxdhHookTable` followed by
28 CLI-specific entries, independent of `W`). -/
def cliHookNames : List String :=
  [E2E.compress512Name, E2E.toEdwardsName, E2E.compressName, E2E.edNegName,
   E2E.torsionFreeName, E2E.dsmbName, E2E.scalarModName, E2E.scalarWideName,
   E2E.kemEncapsName, E2E.kemDecapsName,
   LibsignalSpqrV1.mlkemFromSeedName, LibsignalSpqrV1.mlkemPk1Name,
   LibsignalSpqrV1.mlkemPk2Name, LibsignalSpqrV1.mlkemEncaps1Name,
   LibsignalSpqrV1.mlkemEncaps2Name, LibsignalSpqrV1.mlkemDecapsName,
   LibsignalSpqrV1.mlkemValidatePkName, LibsignalSpqrV1.libcruxHmacName,
   "__rustc::__rust_no_alloc_shim_is_unstable_v2",
   "__rustc::__rust_alloc",
   "__rustc::__rust_dealloc",
   "__rustc::__rust_realloc",
   "__rustc::__rust_alloc_zeroed",
   "memset",
   "memmove",
   "memcpy",
   "bcmp",
   "strlen",
   readFileName,
   writeFileName,
   readStdinName,
   writeStdoutName,
   "core::slice::memchr::memrchr",
   "core::str::converts::from_utf8",
   "core::fmt::write",
   "alloc::fmt::format::format_inner",
   "<std::time::SystemTime>::duration_since",
   "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add",
   "subtle::black_box::<u8>",
   "sha2::sha256::compress256",
   "signal_crypto::aes_cbc::aes_256_cbc_encrypt",
   "signal_crypto::aes_cbc::aes_256_cbc_decrypt",
   "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from",
   "<x25519_dalek::x25519::StaticSecret>::diffie_hellman",
   "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop",
   "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop"]

theorem cliHookNames_eq (W : CliHooks) : (cliHookTable W).map Prod.fst = cliHookNames :=
  rfl

theorem cliHookNames_nodup : cliHookNames.Nodup := by
  decide +kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
theorem cliHookNames_notPanic : cliHookNames.all (fun n => !E2E.isImagePanicSymbol n) = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- No name in `cliHookNames` satisfies `isCliPanicSymbol`, so `withCliPanics` shadows no entry of
`cliHookTable`. -/
theorem cliHookNames_notCliPanic : cliHookNames.all (fun n => !isCliPanicSymbol n) = true := by
  rfl_kernel

theorem lookup_of_mem_nodup {β : Type} :
    ∀ (t : List (String × β)) (n : String) (h : β),
      (t.map Prod.fst).Nodup → (n, h) ∈ t → t.lookup n = some h
  | [], _, _, _, hm => absurd hm List.not_mem_nil
  | (k, v) :: t, n, h, hnd, hm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with he | ht
    · cases he
      simp [List.lookup]
    · have hne : n ≠ k := by
        rintro rfl
        exact hnd.1 (List.mem_map.mpr ⟨(n, h), ht, rfl⟩)
      have hb : (n == k) = false := by simpa using hne
      simp only [List.lookup, hb]
      exact lookup_of_mem_nodup t n h hnd.2 ht

theorem lookup_of_not_mem {β : Type} :
    ∀ (t : List (String × β)) (n : String), n ∉ t.map Prod.fst → t.lookup n = none
  | [], _, _ => rfl
  | (k, v) :: t, n, hn => by
    rw [List.map_cons, List.mem_cons, not_or] at hn
    have hb : (n == k) = false := by simpa using hn.1
    simp only [List.lookup, hb]
    exact lookup_of_not_mem t n hn.2

/-- Every entry `(n, h) ∈ cliHookTable W` resolves to `cliExterns W n = some h`. -/
theorem cliExterns_row (W : CliHooks) {n : String} {h : State → State}
    (hm : (n, h) ∈ cliHookTable W) : cliExterns W n = some h := by
  have hn : n ∈ cliHookNames := by
    rw [← cliHookNames_eq W]
    exact List.mem_map.mpr ⟨(n, h), hm, rfl⟩
  have hp : isCliPanicSymbol n = false := by
    have := List.all_eq_true.mp cliHookNames_notCliPanic n hn
    simpa using this
  unfold cliExterns withCliPanics
  simp only [hp, Bool.false_eq_true, ↓reduceIte]
  exact lookup_of_mem_nodup _ n h (by rw [cliHookNames_eq W]; exact cliHookNames_nodup) hm

/-- Any symbol outside `cliHookNames` with `isCliPanicSymbol n = false` maps to
`cliExterns W n = none`. -/
theorem cliExterns_none (W : CliHooks) {n : String} (hn : n ∉ cliHookNames)
    (hp : isCliPanicSymbol n = false) : cliExterns W n = none := by
  unfold cliExterns withCliPanics
  simp only [hp, Bool.false_eq_true, ↓reduceIte]
  exact lookup_of_not_mem _ n (by rw [cliHookNames_eq W]; exact hn)

theorem cliExterns_none_of_not_imagePanic (W : CliHooks) {n : String} (hn : n ∉ cliHookNames)
    (hp : E2E.isImagePanicSymbol n = false) : cliExterns W n = none :=
  cliExterns_none W hn (isCliPanicSymbol_eq_false_of_isImagePanicSymbol_false hp)


/-! ## `read_stdin` and `read_file` Views -/

/-- Pure specification of `read_stdin`: `.ok bs` when `bs.length ≤ stdinCapBytes`, otherwise
`.error ()`. -/
def readStdinResult (bs : List (BitVec 8)) : Except Unit (List (BitVec 8)) :=
  if bs.length ≤ stdinCapBytes then .ok bs else .error ()

private theorem mem_of_mem_intercalate {α : Type} {x : α} {sep : List α} (hsep : x ∉ sep) :
    ∀ ls : List (List α), x ∈ sep.intercalate ls → ∃ l ∈ ls, x ∈ l
  | [], h => by simp at h
  | [l], h => by
    rw [List.intercalate_singleton] at h
    exact ⟨l, List.Mem.head _, h⟩
  | l :: l' :: ls, h => by
    rw [List.intercalate_cons_cons] at h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact ⟨l, List.Mem.head _, h⟩
      · exact (hsep h).elim
    · obtain ⟨seg, hseg, hx⟩ := mem_of_mem_intercalate hsep (l' :: ls) h
      exact ⟨seg, List.Mem.tail _ hseg, hx⟩

/-- Byte sequences whose 1-byte-per-char string satisfies `PathOk` contain no `0` byte. -/
theorem contains_zero_eq_false_of_pathOk {raw : List (BitVec 8)}
    (hp : PathOk (String.ofList (raw.map fun b => Char.ofNat b.toNat)) = true) :
    raw.contains 0#8 = false := by
  cases hc : raw.contains 0#8 with
  | false => rfl
  | true =>
    have h0 : 0#8 ∈ raw := List.contains_iff_mem.mp hc
    let cs := raw.map fun b => Char.ofNat b.toNat
    have hnul : '\x00' ∈ ['/'].intercalate (cs.splitOn '/') := by
      rw [List.intercalate_splitOn]
      exact List.mem_map.mpr ⟨0#8, h0, rfl⟩
    have hsep : '\x00' ∉ ['/'] := by decide
    obtain ⟨seg, hseg, hmem⟩ := mem_of_mem_intercalate hsep (cs.splitOn '/') hnul
    unfold PathOk pathComps at hp
    rw [String.toList_ofList, List.all_eq_true] at hp
    have hgood := hp seg hseg
    simp at hgood
    exact (hgood.1.2 hmem).elim

/-- Pure file-system read view for `read_file(p)`: `none` (`Err`) if blocked by a regular-file
proper ancestor, directory target, or length above `fileCapBytes`; `some []` if missing; and
`some bs` for a regular file within `fileCapBytes`. -/
def readView (fs : FsState) (p : String) : Option (List (BitVec 8)) :=
  match blockingAncestor? fs p with
  | some (some _) => none
  | some none => some []
  | none =>
    match fs.files p with
    | some (.file bs) => if bs.length ≤ fileCapBytes then some bs else none
    | some .dir => none
    | none => some []

theorem readView_congr {fs fs' : FsState} (h : fs'.files = fs.files) (p : String) :
    readView fs' p = readView fs p := by
  simp only [readView, blockingAncestor?, h]

/-- On readable `PathOk` path bytes of length `< cliPathMaxBytes` and writable sret, `readFileHook`
returns `vecErr` when `readView s.fs p = none` and `vecOk bs` when `readView s.fs p = some bs`. -/
theorem readFileHook_eq_readView (s : State)
    (hok : (s.mem.canRead (s.readReg64 .x0) (s.readReg64 .x1).toNat &&
      s.mem.canWrite (s.readReg64 .x8) 24) = true)
    (hp : PathOk (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1)) = true)
    (hlen : (s.readReg64 .x1).toNat < cliPathMaxBytes) :
    readFileHook s =
      match readView s.fs (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1)) with
      | none => vecErr s
      | some bs => vecOk bs s := by
  have hle : decide (cliPathMaxBytes ≤ (s.readReg64 .x1).toNat) = false :=
    decide_eq_false (by omega)
  have hcz : (s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat).contains 0#8 = false :=
    contains_zero_eq_false_of_pathOk hp
  unfold readFileHook
  simp only [hok, hle, hcz, hp, Bool.or_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  generalize readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1) = p
  unfold readView
  rcases blockingAncestor? s.fs p with _ | _ | _
  · rcases hf : s.fs.files p with _ | e
    · simp [vecOk]
    · rcases e with bs | _
      · by_cases hc : bs.length ≤ fileCapBytes <;> simp [hc]
      · rfl
  · simp [vecOk]
  · rfl

end CryptoVerification.SignalSession
