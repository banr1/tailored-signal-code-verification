/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Defs
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `spqr::initial_state` (`0x542d0..0x5447c`, 107 instructions): Definitions and Specifications

Defines the pure model `initialStateValue` (agreeing with `Top.initialState` over `spqrDeps F K`)
and separation-logic specifications `initialStateSpec`, `initialStateSpecX`, and
`initialStateSpecExt` for `spqr::initial_state` (`0x542d0`):
- ABI: `&Params<'a>` (40B) in `x0`, 32B sret `Result<Vec<u8>, Error>` in `x8`, `logOff` at `[b + 0xaa080]`.
- Postcondition: writes `Ok(initialStateValue F p)` (`empty_state()` on `.v0`, or
  `PqRatchetState.encode_to_vec` of `initialStatePB F p` on `.v1`) at `x8`, preserving `Params` and
  `auth_key`, or panicking only on heap allocation failure.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.InitialState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

/-! ## 1. Symbol name and instruction decodes -/

/-- Symbol name of `spqr::initial_state` (`0x542d0..0x5447c`, 107 instructions). -/
abbrev initialStateName : String := "spqr::initial_state"

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x4eed8 → 0x4f080]

/-- Add instruction-fetch hypotheses for a byte range `[k0, k0 + len)` inside
    `spqr::initial_state` (`0x542d0..0x5447c`). -/
macro "initial_state_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic|
    code_fetches_range CryptoVerification.libsignalSessionCode libsignalSessionBin $b $H
      CryptoVerification.libsignalSessionCode_fnOff_0x4eed8 0x4eed8 $k0 $len)

theorem initialState_fnOff : libsignalSessionCode.fnOff initialStateName = 0x4eed8 :=
  libsignalSessionCode_fnOff_0x4eed8

/-! ## 2. Pure model -/

/-- `VersionNegotiationPB` constructed by `spqr::initial_state` from `p`. -/
def initialStateVN (p : CryptoVerification.LibsignalSpqrV1.Params) : VersionNegotiationPB :=
  { authKey := p.authKey
    direction := p.direction.toI32
    minVersion := p.minVersion.toI32
    chainParams := some p.chainParams.intoPb }

/-- V1 `PqRatchetState` constructed by `spqr::initial_state` with `(initV1State F p.direction p.authKey).into_pb`. -/
def initialStatePB (F : ShaCompress) (p : CryptoVerification.LibsignalSpqrV1.Params) :
    PqRatchetState :=
  { versionNegotiation := some (initialStateVN p)
    chain := none
    inner := some (.v1 (initV1State F p.direction p.authKey).into_pb) }

/-- Total value of `initial_state(params)`: `empty_state()` on V0, otherwise the encoding of
`initialStatePB F p`. -/
def initialStateValue (F : ShaCompress) (p : CryptoVerification.LibsignalSpqrV1.Params) : Bytes :=
  match p.version with
  | .v0 => emptyState
  | .v1 => PqRatchetState.encodeRaw (initialStatePB F p)

/-- `Top.initialState` over `spqrDeps F K` never fails and returns `initialStateValue F p`
(for every `K`: `initial_state` does not use ML-KEM). -/
theorem initialState_spqrDeps_eq_ok (F : ShaCompress) (K : MlKem)
    (p : CryptoVerification.LibsignalSpqrV1.Params) :
    initialState (spqrDeps F K) p = .ok (initialStateValue F p) := by
  obtain ⟨d, v, mv, ak, cp⟩ := p
  cases v with
  | v0 => rfl
  | v1 => cases d <;> rfl

/-! ## 3. Stack budget -/

/-- Own frame of `spqr::initial_state`: `sub sp, sp, #0x1f0` (496 bytes). Saved `x29..x19` at
`sp + 0x190 .. sp + 0x1f0`; the `PqRatchetState` (352 bytes) at `sp + 0x28 .. sp + 0x188`, its
`inner` (the `init_inner` sret) at `sp + 0xa8`; the log-argument scratch at `sp + 0x8 .. sp + 0x28`
(dead under `logOff`). -/
abbrev initialStateFrame : Nat := 0x1f0

/-- Largest callee stack: `init_inner` (`initInnerStack`), `encode_to_vec` (`encodeToVecStackX`),
`drop_glue::<PqRatchetState>` (`dropStack96`), and the allocator hooks (`allocHookStack`). -/
abbrev initialStateCalleeStack : Nat :=
  max initInnerStack (max encodeToVecStackX (max dropStack96 allocHookStack))

/-- Stack budget of `spqr::initial_state`. -/
abbrev initialStateStack : Nat := initialStateFrame + initialStateCalleeStack

/-! ## 4. Specification -/

/-- Ghost arguments of `spqr::initial_state` (`0x542d0`). -/
structure InitialStateGhost where
  /-- `&Params` (`x0`; the 40-byte `Params` is passed by reference). -/
  pA : BitVec 64
  /-- sret (`x8`): 32-byte `Result<SerializedState, Error>`. -/
  ret : BitVec 64
  /-- `params.auth_key.as_ptr()` (`[pA + 0]`). -/
  akPtr : BitVec 64
  /-- The `Params` value (`auth_key` bytes, direction, versions, chain parameters). -/
  p : CryptoVerification.LibsignalSpqrV1.Params

/-- Memory layout of `Params<'a>` at `pA` (40 bytes; trailing padding `[pA + 0x24, pA + 0x28)` omitted). -/
def paramsAt (pA akPtr : BitVec 64) (p : CryptoVerification.LibsignalSpqrV1.Params) : SepProp :=
  (pA ↦₆₄ akPtr) ∗
    ((pA + 8#64) ↦₆₄ BitVec.ofNat 64 p.authKey.length) ∗
    ((pA + 0x10#64) ↦₃₂ p.chainParams.maxJump) ∗
    ((pA + 0x14#64) ↦₃₂ p.chainParams.maxOooKeys) ∗
    ((pA + 0x18#64) ↦₃₂ p.direction.toI32) ∗
    ((pA + 0x1c#64) ↦₃₂ p.version.toI32) ∗
    ((pA + 0x20#64) ↦₃₂ p.minVersion.toI32)

/-- The 32-byte sret after `initial_state` returns `Ok(v)`: tag word `0`, then `Vec<u8>` `v`. -/
def initialStateResultAt (A : RustAlloc) (ret : BitVec 64) (v : Bytes) : SepProp :=
  (ret ↦₆₄ 0#64) ∗ vecU8 A (ret + 8#64) v

/-- Panic postcondition: heap allocation failure only. -/
def initialStateOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Specification of `spqr::initial_state` (`0x542d0`), with `(b + 0xaa080) ↦₆₄ 0` (`logOff`)
in the precondition and `.rodata` jump tables supplied via `Spec.inImage`. -/
def initialStateSpec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec InitialStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.pA ∧
      s.readReg64 .x8 = x.ret ∧
      x.akPtr ≠ 0#64 ∧
      x.p.authKey.length < 2 ^ 32⌝ ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      memRegion x.ret 32 ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      A.pool ∗ stackAt s.sp initialStateStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      initialStateResultAt A x.ret (initialStateValue F x.p) ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      A.pool ∗ stackAt s0.sp initialStateStack
  onPanic := fun _ s0 sf => initialStateOnPanic s0 sf

/-- `initialStateSpec` lifted into `img` via `Spec.inImage`. -/
abbrev initialStateSpecX (A : RustAlloc) (F : ShaCompress) (img : Obj.Image) :
    Spec InitialStateGhost :=
  (initialStateSpec A F img.base).inImage img

/-- `spqr::initial_state` meets `initialStateSpec A F b` on `tripleRatchetProgAtExt b ext`. -/
def InitialStateOkExt (b : BitVec 64) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr initialStateName)
    (initialStateSpec A F b)

/-- `spqr::initial_state` meets `initialStateSpecX A F img` on `tripleRatchetProgAtExt img.base ext`. -/
def InitialStateOkX (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr initialStateName)
    (initialStateSpecX A F img)

/-! ## 5. Contract-Parameterized (`*Ext`, `+ 16384` B Hook Stack) Specification -/

/-- Extended largest callee stack: `init_inner` (`initInnerStackExt = 18912` B),
`encode_to_vec` (`encodeToVecStackX`), `drop_glue::<PqRatchetState>` (`dropStack96`),
and the extended extern hooks (`extHookStack = 16384` B). -/
abbrev initialStateCalleeStackExt : Nat :=
  max initInnerStackExt (max encodeToVecStackX (max dropStack96 extHookStack))

/-- Extended stack budget of `spqr::initial_state` (`496 + 18912 = 19408` B). -/
abbrev initialStateStackExt : Nat := initialStateFrame + initialStateCalleeStackExt

theorem initialStateStackExt_eq : initialStateStackExt = 19408 := rfl

theorem initialStateStackExt_eq_add : initialStateStackExt = initialStateStack + 1232 := rfl

/-- Core specification of `spqr::initial_state` (`0x542d0`) at `initialStateStackExt` (`19408` B),
accommodating `initInnerStackExt` (`18912` B) and `extHookStack` (`16384` B). -/
def initialStateSpecExt (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec InitialStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.pA ∧
      s.readReg64 .x8 = x.ret ∧
      x.akPtr ≠ 0#64 ∧
      x.p.authKey.length < 2 ^ 32⌝ ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      memRegion x.ret 32 ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      A.pool ∗ stackAt s.sp initialStateStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      initialStateResultAt A x.ret (initialStateValue F x.p) ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      A.pool ∗ stackAt s0.sp initialStateStackExt
  onPanic := fun _ s0 sf => initialStateOnPanic s0 sf

abbrev initialStateSpecXExt (A : RustAlloc) (F : ShaCompress) (img : Obj.Image) :
    Spec InitialStateGhost :=
  (initialStateSpecExt A F img.base).inImage img

/-- `spqr::initial_state` meets `initialStateSpecExt A F b` on `tripleRatchetProgAtExt b ext`. -/
def InitialStateBaseOkExt (b : BitVec 64) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr initialStateName)
    (initialStateSpecExt A F b)

/-- `spqr::initial_state` meets `initialStateSpecXExt A F img` on `tripleRatchetProgAtExt img.base ext`. -/
def InitialStateOkXExt (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr initialStateName)
    (initialStateSpecXExt A F img)

end CryptoVerification.SpqrV1.Top.InitialState
