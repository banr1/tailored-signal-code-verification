/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import GeneratedLean.LibsignalSessionObj

/-!
# Rebased Triple-Ratchet Program and Root-Statement Bridge

Defines `contractProg` and `tripleRatchetProgAt` (`libsignalSessionCode` rebased at `b` with
`tripleRatchetExterns`), the extern-stub contract bundle `TRStubsOK`, and
`root_of_tripleRatchetProgAt` bridging `tripleRatchetProgAt` lemmas to `tripleRatchetProg`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr

/-- The contract program rebased at address `b` with hooks `withPanics ext`. -/
noncomputable abbrev contractProg (b : BitVec 64) (ext : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics ext)

/-- Stub offsets in the session binary (relative to `img.base`). -/
noncomputable def stubOff (sym : String) : BitVec 64 :=
  BitVec.ofNat 64 (libsignalSessionCode.fnOff sym)

/-- Predicate asserting that the 11 modelled TripleRatchet extern stubs satisfy their
    `subroutine_ok` contracts on `contractProg b ext`. -/
structure TRStubsOK (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop where
  compress256 : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff "sha2::sha256::compress256") spec
  memcpy : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff "memcpy") spec
  memmove : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff "memmove") spec
  memset : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff "memset") spec
  shim : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff "__rustc::__rust_no_alloc_shim_is_unstable_v2") spec
  blackBox : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff "subtle::black_box::<u8>") spec
  dh : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff dhName) spec
  pubFromSecret : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff pubFromSecretName) spec
  staticDrop : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff staticDropName) spec
  sharedDrop : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff sharedDropName) spec
  rngFill : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff rngFillName) spec

abbrev StubsContractOK := TRStubsOK


/-- `tripleRatchetExterns` is idempotent. -/
theorem tripleRatchetExterns_idem (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    tripleRatchetExterns C ctl (tripleRatchetExterns C ctl abs) =
      tripleRatchetExterns C ctl abs := by
  funext sym
  dsimp only [tripleRatchetExterns]
  cases h : CryptoVerification.LibsignalSession.sessionExterns C.F (fun _ => none) sym with
  | some h0 => rfl
  | none =>
    dsimp only
    split_ifs <;> rfl

/-- Spec-hook environment `tripleRatchetExterns C ctl ext`. -/
noncomputable abbrev selExt (_b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : String → Option (State → State) :=
  tripleRatchetExterns C ctl ext

/-- The triple-ratchet program rebased at `b`: `libsignalSessionCode` with the hooks of `tripleRatchetProg`. -/
noncomputable abbrev tripleRatchetProgAt (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl abs))

theorem selExt_idem (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    selExt b C ctl (tripleRatchetExterns C ctl abs) = tripleRatchetExterns C ctl abs :=
  tripleRatchetExterns_idem C ctl abs

theorem tripleRatchetProg_eq_tripleRatchetProgAt {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    tripleRatchetProg img C ctl abs = tripleRatchetProgAt img.base C ctl abs :=
  libsignalSessionCode_ofImage himg

theorem tripleRatchetProgAt_eq_tripleRatchetProg {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    tripleRatchetProgAt img.base C ctl (tripleRatchetExterns C ctl abs) =
      tripleRatchetProg img C ctl abs := by
  unfold tripleRatchetProgAt tripleRatchetProg
  rw [tripleRatchetExterns_idem]
  exact (libsignalSessionCode_ofImage himg).symm

/-- `entryOf img name` is the function's address in `tripleRatchetProgAt img.base …` (hooks do not move code). -/
theorem entryOf_eq_tripleRatchetProgAt {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (name : String) :
    entryOf img name = (tripleRatchetProgAt img.base C ctl abs).fnAddr name := by
  unfold entryOf tripleRatchetProgAt
  rw [libsignalSessionCode_ofImage himg, Program.fnAddr_rebase, Program.fnAddr_rebase]

/-- From a per-function lemma on `tripleRatchetProgAt` to the shape of the root statements. -/
theorem root_of_tripleRatchetProgAt {α : Type} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String}
    {spec : Spec α} (himg : Obj.Loads libsignalSessionImage img)
    (h : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) ((tripleRatchetProgAt img.base C ctl abs).fnAddr name) spec) :
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img name) spec := by
  rw [tripleRatchetProg_eq_tripleRatchetProgAt himg, entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg name]
  exact h

end CryptoVerification.LibsignalTripleRatchet
