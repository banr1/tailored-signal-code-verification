/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StoreEmpty
public import LibsignalBinary.Proofs.E2E.InMem.IdentityKeyStoreImpl.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.InMem.IdentityKeyStoreImpl.Skeleton
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Self-Identity Store Kit (`IdentitySelfStoreSpec`, `IdentitySelfStoreKitOkI`)

Store-kit contracts for the self-identity methods on `dyn IdentityKeyStore` invoked during
`decrypt_prekey`:
* `get_identity_key_pair` (`ikit.id_vt + 0x18`), writing 72-byte
  `Poll::Ready<Result<IdentityKeyPair, SignalProtocolError>>`;
* `get_local_registration_id` (`ikit.id_vt + 0x20`), writing 48-byte niche-encoded
  `Poll::Ready<Result<u32, SignalProtocolError>>`.

Parameterized over an existing `ikit : IdentityStoreSpec A b` so self-identity and peer-identity
operations share `ikit.id_vt`, `ikit.IdState`, `ikit.identityAt`, and `ikit.envOk`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApiRepr (storeHookStr)
open CryptoVerification.LibsignalTripleRatchet
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

/-! ## `IdentitySelfStoreSpec` -/

/-- The self-identity methods (`get_identity_key_pair` at `ikit.id_vt + 0x18`,
`get_local_registration_id` at `ikit.id_vt + 0x20`) of an identity store whose state is
`ikit.IdState`. -/
structure IdentitySelfStoreSpec {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) where
  /-- Point-wise file-descriptor predicate carried across the self-identity ops (`True` by default
      for in-memory stores; `FdsGe3Closed` for the CLI's file-backed store). -/
  fdsOk : FsState → Prop := fun _ => True
  /-- Kit witness type for `get_identity_key_pair` `Err` returns (`PEmpty` when infallible). -/
  KpErr : Type
  /-- Kit witness type for `get_local_registration_id` `Err` returns (`PEmpty` when infallible). -/
  RegIdErr : Type
  /-- 48-byte `SignalProtocolError` layout for `KpErr`. -/
  kpErr : SpeErrSpec KpErr
  /-- 48-byte `SignalProtocolError` layout for `RegIdErr`. -/
  regIdErr : SpeErrSpec RegIdErr
  /-- Pure relation tying `ist0` to the `get_identity_key_pair` answer. -/
  kpRel : ikit.IdState → Except KpErr IdentityKeyPair → Prop
  /-- Pure relation tying `ist0` to the `get_local_registration_id` answer. -/
  regIdRel : ikit.IdState → Except RegIdErr (BitVec 32) → Prop
  /-- Trace events emitted by a `get_identity_key_pair` poll. -/
  kpEvs : Except KpErr IdentityKeyPair → List TraceEvent
  /-- Trace events emitted by a `get_local_registration_id` poll. -/
  regIdEvs : Except RegIdErr (BitVec 32) → List TraceEvent
  /-- Code/vtable offsets for `get_identity_key_pair` shim, future vtable, poll, and drop. -/
  kpShimOff : BitVec 64
  kpFutVtOff : BitVec 64
  kpPollOff : BitVec 64
  kpFutDropOff : BitVec 64
  /-- Code/vtable offsets for `get_local_registration_id` shim, future vtable, poll, and drop. -/
  regIdShimOff : BitVec 64
  regIdFutVtOff : BitVec 64
  regIdPollOff : BitVec 64
  regIdFutDropOff : BitVec 64
  /-- Heap box sizes in bytes for the two futures (`16` in both CLI and InMem). -/
  kpBoxSize : Nat
  regIdBoxSize : Nat
  /-- Stack budgets in bytes for the two shims and two polls. -/
  kpShimStack : Nat
  kpPollStack : Nat
  regIdShimStack : Nat
  regIdPollStack : Nat
  /-- Future box separation-logic predicates (`state = 0#8` before first poll, `1#8` after). -/
  kpBoxAt : (box self : BitVec 64) → (state : BitVec 8) → SepProp
  regIdBoxAt : (box self : BitVec 64) → (state : BitVec 8) → SepProp
  /-- Any `kpBoxAt` state entails raw `memRegion` of `kpBoxSize` bytes for deallocation. -/
  kpBoxAt_memRegion : ∀ box self st, kpBoxAt box self st ⊢ memRegion box kpBoxSize
  /-- Any `regIdBoxAt` state entails raw `memRegion` of `regIdBoxSize` bytes for deallocation. -/
  regIdBoxAt_memRegion : ∀ box self st, regIdBoxAt box self st ⊢ memRegion box regIdBoxSize
  /-- `kpBoxSize` is non-zero as a 64-bit word (so `cbz` before `__rust_dealloc` does not skip). -/
  kpBoxSize_ne_zero : BitVec.ofNat 64 kpBoxSize ≠ 0#64
  /-- `regIdBoxSize` is non-zero as a 64-bit word. -/
  regIdBoxSize_ne_zero : BitVec.ofNat 64 regIdBoxSize ≠ 0#64
  /-- `kpBoxSize` fits in 64 bits. -/
  kpBoxSize_lt : kpBoxSize < 2 ^ 64
  /-- `regIdBoxSize` fits in 64 bits. -/
  regIdBoxSize_lt : regIdBoxSize < 2 ^ 64
  /-- `b + kpFutDropOff` is non-zero for page-aligned `b`. -/
  kpFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + kpFutDropOff ≠ 0#64
  /-- `b + regIdFutDropOff` is non-zero for page-aligned `b`. -/
  regIdFutDrop_ne_zero : b &&& 0xfff#64 = 0#64 → b + regIdFutDropOff ≠ 0#64

/-! ## Poll Output Layouts (`Poll<Result<IdentityKeyPair, SPE>>` / `Poll<Result<u32, SPE>>`) -/

/-- The 72-byte `Poll::Ready<Result<IdentityKeyPair, SignalProtocolError>>` written to `out` by
`get_identity_key_pair`'s future poll:
* `.ok kp`: byte `0#8` at `out`, 32-byte serialized public key at `out + 1`, 32-byte private key
  at `out + 0x21`, and 7 bytes of trailing padding at `out + 0x41` (matching
  `RecordCodecsBinary.identityKeyPairResultAt A out (.ok kp)`);
* `.error e`: byte `1#8` at `out`, 7 bytes of padding at `out + 1`, the 48-byte
  `speErrAt skit.kpErr (out + 8) e`, and 16 bytes of trailing padding at `out + 0x38`. -/
def kpPollOutAt {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) (out : BitVec 64) :
    Except skit.KpErr IdentityKeyPair → SepProp
  | .ok kp =>
      (out ↦₈ 0#8) ∗
        ((out + 1#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((out + 0x21#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        memRegion (out + 0x41#64) 7
  | .error e =>
      (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
        speErrAt skit.kpErr (out + 8#64) e ∗ memRegion (out + 0x38#64) 16

/-- The 48-byte `Poll::Ready<Result<u32, SignalProtocolError>>` written to `out` by
`get_local_registration_id`'s future poll:
* `.ok reg`: word `0xFFFFFFFFFFFFFFFE#64` (`-2`) at `out`, 32-bit registration ID `reg` at
  `out + 8`, and 36 bytes of trailing uninspected payload/padding at `out + 0xc`;
* `.error e`: the 48-byte `SignalProtocolError` `speErrAt skit.regIdErr out e`. -/
def regIdPollOutAt {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) (out : BitVec 64) :
    Except skit.RegIdErr (BitVec 32) → SepProp
  | .ok reg =>
      (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₃₂ reg) ∗
        memRegion (out + 0xc#64) 36
  | .error e => speErrAt skit.regIdErr out e

/-! ## Generic Shim and Poll Contracts -/

/-- Generic `get_identity_key_pair` shim spec parameterized by `skit : IdentitySelfStoreSpec ikit`.
Takes `self` in `x0` and returns `(box, b + skit.kpFutVtOff)` in `(x0, x1)` with `box ≠ 0#64` and
8-aligned. -/
def kitKpShimSpec {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Spec (BitVec 64) where
  pre := fun self s =>
    ⌜s.readReg64 .x0 = self⌝ ∗ A.pool ∗ stackAt s.sp skit.kpShimStack
  post := fun self s0 sf =>
    ⌜sf.readReg64 .x1 = b + skit.kpFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) skit.kpBoxSize 8 ∗
      skit.kpBoxAt (sf.readReg64 .x0) self 0#8 ∗
      A.pool ∗ stackAt s0.sp skit.kpShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `get_local_registration_id` shim spec parameterized by
`skit : IdentitySelfStoreSpec ikit`. Takes `self` in `x0` and returns
`(box, b + skit.regIdFutVtOff)` in `(x0, x1)` with `box ≠ 0#64` and 8-aligned. -/
def kitRegIdShimSpec {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Spec (BitVec 64) where
  pre := fun self s =>
    ⌜s.readReg64 .x0 = self⌝ ∗ A.pool ∗ stackAt s.sp skit.regIdShimStack
  post := fun self s0 sf =>
    ⌜sf.readReg64 .x1 = b + skit.regIdFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) skit.regIdBoxSize 8 ∗
      skit.regIdBoxAt (sf.readReg64 .x0) self 0#8 ∗
      A.pool ∗ stackAt s0.sp skit.regIdShimStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `get_identity_key_pair` poll spec parameterized by `skit : IdentitySelfStoreSpec ikit`.
Ghost state `(fut, out, self, ist0)`: reads `ikit.identityAt self ist0` without modifying `ist0`
and writes `kpPollOutAt skit out ans` (`72` bytes). -/
def kitKpPollSpec {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState) where
  pre := fun (fut, out, self, ist0) s =>
    ⌜s.readReg64 .x0 = fut ∧ s.readReg64 .x8 = out⌝ ∗
      skit.kpBoxAt fut self 0#8 ∗
      ikit.identityAt self ist0 ∗
      memRegion out 72 ∗
      A.pool ∗ stackAt s.sp skit.kpPollStack
  post := fun (fut, out, self, ist0) s0 sf =>
    ∃∗ ans : Except skit.KpErr IdentityKeyPair,
      ⌜skit.kpRel ist0 ans ∧ sf.trace = s0.trace ++ skit.kpEvs ans⌝ ∗
      skit.kpBoxAt fut self 1#8 ∗
      ikit.identityAt self ist0 ∗
      kpPollOutAt skit out ans ∗
      A.pool ∗ stackAt s0.sp skit.kpPollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Generic `get_local_registration_id` poll spec parameterized by
`skit : IdentitySelfStoreSpec ikit`. Ghost state `(fut, out, self, ist0)`: reads
`ikit.identityAt self ist0` without modifying `ist0` and writes `regIdPollOutAt skit out ans`
(`48` bytes). -/
def kitRegIdPollSpec {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState) where
  pre := fun (fut, out, self, ist0) s =>
    ⌜s.readReg64 .x0 = fut ∧ s.readReg64 .x8 = out⌝ ∗
      skit.regIdBoxAt fut self 0#8 ∗
      ikit.identityAt self ist0 ∗
      memRegion out 48 ∗
      A.pool ∗ stackAt s.sp skit.regIdPollStack
  post := fun (fut, out, self, ist0) s0 sf =>
    ∃∗ ans : Except skit.RegIdErr (BitVec 32),
      ⌜skit.regIdRel ist0 ans ∧ sf.trace = s0.trace ++ skit.regIdEvs ans⌝ ∗
      skit.regIdBoxAt fut self 1#8 ∗
      ikit.identityAt self ist0 ∗
      regIdPollOutAt skit out ans ∗
      A.pool ∗ stackAt s0.sp skit.regIdPollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- The `get_identity_key_pair` poll spec with `ikit.envOk` on the entry files. -/
abbrev kitKpPollSpecE {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState) :=
  withEnvPre (kitKpPollSpec skit) fun s => ikit.envOk s.fs.files

/-- The `get_local_registration_id` poll spec with `ikit.envOk` on the entry files. -/
abbrev kitRegIdPollSpecE {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState) :=
  withEnvPre (kitRegIdPollSpec skit) fun s => ikit.envOk s.fs.files

/-! ### In-Image Poll Contracts (`logOff img` and `.inImage img`) -/

/-- The `get_identity_key_pair` poll contract of an in-image identity store: `kitKpPollSpecE`
plus `logOff img`, under the image invariant. -/
abbrev kitKpPollSpecI {A : RustAlloc} {b : BitVec 64} (img : Obj.Image)
    {ikit : IdentityStoreSpec A b} (skit : IdentitySelfStoreSpec ikit) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState) :=
  (withLogOff (kitKpPollSpecE skit) img).inImage img

/-- The `get_local_registration_id` poll contract of an in-image identity store:
`kitRegIdPollSpecE` plus `logOff img`, under the image invariant. -/
abbrev kitRegIdPollSpecI {A : RustAlloc} {b : BitVec 64} (img : Obj.Image)
    {ikit : IdentityStoreSpec A b} (skit : IdentitySelfStoreSpec ikit) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState) :=
  (withLogOff (kitRegIdPollSpecE skit) img).inImage img

/-- The self-identity methods' own trace events contain no file-system event (`FsCtx`'s `Q`). -/
def IdentitySelfStoreSpec.Quiet {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Prop :=
  (∀ ans, NoFsEv (skit.kpEvs ans)) ∧
    (∀ ans, NoFsEv (skit.regIdEvs ans))

/-! ## Vtable and Code Bundles -/

/-- Read-only `.rodata` vtable slots required by `skit : IdentitySelfStoreSpec ikit` under
`img.FrozenLoaded`. -/
structure IdentitySelfVtablesOk {A : RustAlloc} (img : Obj.Image)
    (ikit : IdentityStoreSpec A img.base)
    (skit : IdentitySelfStoreSpec ikit) : Prop where
  kpSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((ikit.id_vt + 0x18#64) ↦₆₄ᵣ (img.base + skit.kpShimOff)) ∗ P
  regIdSlot : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((ikit.id_vt + 0x20#64) ↦₆₄ᵣ (img.base + skit.regIdShimOff)) ∗ P
  kpFutDrop : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + skit.kpFutVtOff) ↦₆₄ᵣ (img.base + skit.kpFutDropOff)) ∗ P
  kpFutSize : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗ P
  kpFutAlign : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  kpFutPoll : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + skit.kpFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + skit.kpPollOff)) ∗ P
  regIdFutDrop : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + skit.regIdFutVtOff) ↦₆₄ᵣ (img.base + skit.regIdFutDropOff)) ∗ P
  regIdFutSize : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗ P
  regIdFutAlign : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  regIdFutPoll : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + skit.regIdFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + skit.regIdPollOff)) ∗ P

/-- Code-contract bundle for `skit : IdentitySelfStoreSpec ikit` at `tripleRatchetProgAtExt b ext`
(without `img.FrozenLoaded` or `logOff img`). -/
structure IdentitySelfStoreKitOk {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit)
    (ext : String → Option (State → State)) : Prop where
  kpShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + skit.kpShimOff)
    (kitKpShimSpec skit)
  kpPoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + skit.kpPollOff)
    (kitKpPollSpecE skit)
  kpFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + skit.kpFutDropOff)
    futDropSpec
  regIdShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + skit.regIdShimOff)
    (kitRegIdShimSpec skit)
  regIdPoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + skit.regIdPollOff)
    (kitRegIdPollSpecE skit)
  regIdFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + skit.regIdFutDropOff)
    futDropSpec

/-- The `IdentitySelfStoreKitOkI` bundle used by Stage P2 of `decrypt_prekey`, stated at
`tripleRatchetProgAtExt b ext`: the shim and poll contracts assume `.inImage img`, and both polls
also require and preserve `logOff img` (`kitKpPollSpecI` / `kitRegIdPollSpecI`). -/
structure IdentitySelfStoreKitOkI {A : RustAlloc} {b : BitVec 64} (img : Obj.Image)
    (ikit : IdentityStoreSpec A b) (skit : IdentitySelfStoreSpec ikit)
    (ext : String → Option (State → State)) : Prop where
  kpShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + skit.kpShimOff)
    ((kitKpShimSpec skit).inImage img)
  kpPoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + skit.kpPollOff)
    (kitKpPollSpecI img skit)
  kpFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + skit.kpFutDropOff)
    futDropSpec
  regIdShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + skit.regIdShimOff)
    ((kitRegIdShimSpec skit).inImage img)
  regIdPoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + skit.regIdPollOff)
    (kitRegIdPollSpecI img skit)
  regIdFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + skit.regIdFutDropOff)
    futDropSpec

/-- A self-identity store that assumes nothing about `img` gives `IdentitySelfStoreKitOkI`. -/
theorem IdentitySelfStoreKitOk.toI {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    {skit : IdentitySelfStoreSpec ikit} {ext : String → Option (State → State)} {img : Obj.Image}
    (h : IdentitySelfStoreKitOk skit ext) :
    IdentitySelfStoreKitOkI img ikit skit ext where
  kpShim := subroutine_ok_inImage_of_subroutine_ok img h.kpShim
  kpPoll := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_withLogOff img h.kpPoll fun _ _ _ => by
      dsimp only [kitKpPollSpecE, withEnvPre, kitKpPollSpec]
      rw [sepConj_assoc]; exact sepConj_mono_right (entails_anyHeap _))
  kpFutDrop := h.kpFutDrop
  regIdShim := subroutine_ok_inImage_of_subroutine_ok img h.regIdShim
  regIdPoll := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_withLogOff img h.regIdPoll fun _ _ _ => by
      dsimp only [kitRegIdPollSpecE, withEnvPre, kitRegIdPollSpec]
      rw [sepConj_assoc]; exact sepConj_mono_right (entails_anyHeap _))
  regIdFutDrop := h.regIdFutDrop

/-- Definitional equality `tripleRatchetProgAt b C ctl abs =
tripleRatchetProgAtExt b (tripleRatchetExterns C ctl abs)`. -/
theorem tripleRatchetProgAt_eq_ext (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    tripleRatchetProgAt b C ctl abs =
      tripleRatchetProgAtExt b (tripleRatchetExterns C ctl abs) := rfl

theorem IdentitySelfStoreKitOk.ofProgAt {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} {skit : IdentitySelfStoreSpec ikit}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (kpShim : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + skit.kpShimOff)
      (kitKpShimSpec skit))
    (kpPoll : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + skit.kpPollOff)
      (kitKpPollSpecE skit))
    (kpFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + skit.kpFutDropOff)
      futDropSpec)
    (regIdShim : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + skit.regIdShimOff)
      (kitRegIdShimSpec skit))
    (regIdPoll : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + skit.regIdPollOff)
      (kitRegIdPollSpecE skit))
    (regIdFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + skit.regIdFutDropOff)
      futDropSpec) :
    IdentitySelfStoreKitOk skit (tripleRatchetExterns C ctl abs) :=
  ⟨kpShim, kpPoll, kpFutDrop, regIdShim, regIdPoll, regIdFutDrop⟩

theorem IdentitySelfStoreKitOkI.ofProgAt {A : RustAlloc} {b : BitVec 64}
    {img : Obj.Image} {ikit : IdentityStoreSpec A b} {skit : IdentitySelfStoreSpec ikit}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (kpShim : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + skit.kpShimOff)
      ((kitKpShimSpec skit).inImage img))
    (kpPoll : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + skit.kpPollOff)
      (kitKpPollSpecI img skit))
    (kpFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + skit.kpFutDropOff)
      futDropSpec)
    (regIdShim : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + skit.regIdShimOff)
      ((kitRegIdShimSpec skit).inImage img))
    (regIdPoll : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + skit.regIdPollOff)
      (kitRegIdPollSpecI img skit))
    (regIdFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + skit.regIdFutDropOff)
      futDropSpec) :
    IdentitySelfStoreKitOkI img ikit skit (tripleRatchetExterns C ctl abs) :=
  ⟨kpShim, kpPoll, kpFutDrop, regIdShim, regIdPoll, regIdFutDrop⟩

/-! ## In-Memory Non-Vacuity Witness -/

/-- Own-identity memory layout (`self + 0x30..0x70` key pair and `self + 0x70` `u32`
registration ID) of `InMemIdentityKeyStore`. -/
def inMemSelfIdentityAt (self : BitVec 64) (st : IdentityKeyPair × BitVec 32) : SepProp :=
  ((self + 0x30#64) ↦ₛ st.1.identityKey.publicKey.bytes.toList) ∗
    ((self + 0x50#64) ↦ₛ st.1.privateKey.bytes.toList) ∗
    ((self + 0x70#64) ↦₃₂ st.2)

/-- Local witness `IdentityStoreSpec` owning `InMemIdentityKeyStore`'s self key pair and local
registration ID cells. -/
def inMemSelfIdentityStoreSpec (A : RustAlloc) (b : BitVec 64) : IdentityStoreSpec A b :=
  { hookIdentityStoreSpec A b with
    IdState := IdentityKeyPair × BitVec 32
    identityAt := inMemSelfIdentityAt
    trustUpdate := fun st _ _ _ _ => st
    saveUpdate := fun st _ _ _ => st
    trustRel := fun _ _ _ _ _ => True
    saveRel := fun _ _ _ _ => True }

/-- `SpeErrSpec` matching the callback `SignalProtocolError` layout on `InMemIdentityKeyStore`'s
unreachable self-identity `Err` branch, parameterized by trailing uninitialized word `w`. -/
def inMemSelfSpeErrSpec (b : BitVec 64) : SpeErrSpec (BitVec 64) where
  w0 := fun _ => 0x800000000000001A#64
  w1 := fun _ =>
    b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
  w2 := fun _ => 10#64
  w3 := fun _ => 1#64
  w4 := fun _ =>
    b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)
  w5 := id
  heap := fun _ =>
    (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ
      storeHookStr
  w0_ne_err := fun _ => by decide
  w0_ne_ok := fun _ => by decide
  w0_ne_pending := fun _ => by decide

/-- Non-vacuity witness `IdentitySelfStoreSpec` for `InMemIdentityKeyStore`. -/
def inMemIdentitySelfStoreSpec (A : RustAlloc) (b : BitVec 64) :
    IdentitySelfStoreSpec (inMemSelfIdentityStoreSpec A b) where
  KpErr := BitVec 64
  RegIdErr := BitVec 64
  kpErr := inMemSelfSpeErrSpec b
  regIdErr := inMemSelfSpeErrSpec b
  kpRel := fun st ans => ans = .ok st.1
  regIdRel := fun st ans => ans = .ok st.2
  kpEvs := fun _ => []
  regIdEvs := fun _ => []
  kpShimOff := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair")
  kpFutVtOff := bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 24)
  kpPollOff := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}")
  kpFutDropOff := CryptoVerification.E2E.InMem.IdentityKeyStoreImpl.inMemFutDropOff
  regIdShimOff := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id")
  regIdFutVtOff := bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 24)
  regIdPollOff := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}")
  regIdFutDropOff := CryptoVerification.E2E.InMem.IdentityKeyStoreImpl.inMemFutDropOff
  kpBoxSize := 16
  regIdBoxSize := 16
  kpShimStack := CryptoVerification.E2E.Pqxdh.ResponderClosure.inMemId16ShimStack
  kpPollStack := 0
  regIdShimStack := CryptoVerification.E2E.Pqxdh.ResponderClosure.inMemId16ShimStack
  regIdPollStack := 0
  kpBoxAt := CryptoVerification.E2E.Pqxdh.ResponderClosure.inMemId16BoxAt
  regIdBoxAt := CryptoVerification.E2E.Pqxdh.ResponderClosure.inMemId16BoxAt
  kpBoxAt_memRegion := CryptoVerification.E2E.Pqxdh.ResponderClosure.inMemId16BoxAt_memRegion
  regIdBoxAt_memRegion := CryptoVerification.E2E.Pqxdh.ResponderClosure.inMemId16BoxAt_memRegion
  kpBoxSize_ne_zero := by decide
  regIdBoxSize_ne_zero := by decide
  kpBoxSize_lt := by decide
  regIdBoxSize_lt := by decide
  kpFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - CryptoVerification.E2E.InMem.IdentityKeyStoreImpl.inMemFutDropOff by
      rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)
  regIdFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - CryptoVerification.E2E.InMem.IdentityKeyStoreImpl.inMemFutDropOff by
      rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)

theorem inMemIdentitySelfStoreSpec_quiet {A : RustAlloc} {b : BitVec 64} :
    (inMemIdentitySelfStoreSpec A b).Quiet :=
  ⟨fun _ => by simp [inMemIdentitySelfStoreSpec, NoFsEv],
    fun _ => by simp [inMemIdentitySelfStoreSpec, NoFsEv]⟩

theorem inMemSelf_kpRel_error_iff {A : RustAlloc} {b : BitVec 64}
    {st : (inMemSelfIdentityStoreSpec A b).IdState}
    {e : (inMemIdentitySelfStoreSpec A b).KpErr} :
    (inMemIdentitySelfStoreSpec A b).kpRel st (.error e) ↔ False := by
  simp [inMemIdentitySelfStoreSpec]

theorem inMemSelf_regIdRel_error_iff {A : RustAlloc} {b : BitVec 64}
    {st : (inMemSelfIdentityStoreSpec A b).IdState}
    {e : (inMemIdentitySelfStoreSpec A b).RegIdErr} :
    (inMemIdentitySelfStoreSpec A b).regIdRel st (.error e) ↔ False := by
  simp [inMemIdentitySelfStoreSpec]

private theorem inMemSelfSpeErrAt_eq (b p : BitVec 64) :
    SepProp.sepExists (fun w => speErrAt (inMemSelfSpeErrSpec b) p w) =
      (p ↦₆₄ 0x800000000000001A#64) ∗
        ((p + 0x08#64) ↦₆₄ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")))) ∗
        errTailAt b p ∗ memRegion (p + 0x28#64) 8 := by
  rw [ProofLib.memRegion_eight (p + 0x28#64)]
  dsimp only [speErrAt, speWordsAt, inMemSelfSpeErrSpec, id, errTailAt]
  simp only [ProofLib.sepExists_sepConj_right]
  exact congrArg SepProp.sepExists (funext fun _ => by ac_rfl)

/-- Existential quantification over `inMemSelfSpeErrSpec b` matches the 64-byte error payload of
`get_identity_key_pair`. -/
theorem inMemSelf_kpErr_layout (b out : BitVec 64) :
    (∃∗ w, speErrAt (inMemSelfSpeErrSpec b) (out + 8#64) w) ∗ memRegion (out + 0x38#64) 16 =
      ((out + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
        ((out + 0x10#64) ↦₆₄ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")))) ∗
        errTailAt b (out + 8#64) ∗ memRegion (out + 0x30#64) 24 := by
  rw [inMemSelfSpeErrAt_eq b (out + 8#64),
    show (24 : Nat) = 8 + 16 from rfl,
    ProofLib.memRegion_split (out + 0x30#64) 8 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-- Existential quantification over `inMemSelfSpeErrSpec b` matches the 48-byte error payload of
`get_local_registration_id`. -/
theorem inMemSelf_regIdErr_layout (b out : BitVec 64) :
    (∃∗ w, speErrAt (inMemSelfSpeErrSpec b) out w) =
      (out ↦₆₄ 0x800000000000001A#64) ∗
        ((out + 8#64) ↦₆₄ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")))) ∗
        errTailAt b out ∗ memRegion (out + 0x28#64) 8 :=
  inMemSelfSpeErrAt_eq b out

section InMemWitness

open CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
open CryptoVerification.E2E.InMem.IdentityKeyStoreImpl
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_inMemSelf (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_inMemSelf (s : Arm64.State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg64_sp_inMemSelf (s : Arm64.State) (v : BitVec 64) :
    (s.writeReg64 .sp v).sp = v := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_inMemSelf (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  Arm64.State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_inMemSelf (s : Arm64.State) (pc : BitVec 64) (m : Memory)
    (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

private theorem memRegion_16_inMemSelf (p : BitVec 64) :
    memRegion p 16 =
      (∃∗ b0 : BitVec 8, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₈ b0) ∗ memRegion (p + 9#64) 7) := by
  rw [memRegion_split p 8 8 (by decide),
    memRegion_split (p + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_inMemSelfShim (sp : BitVec 64) :
    stackAt sp inMemId16ShimStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp allocHookStack 4 (by decide)

private theorem fnAddr_progAt_inMemSelf {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (Arm64.State → Arm64.State)} {name : String} {off : Nat}
    (h : libsignalSessionCode.fnOff name = off) :
    (tripleRatchetProgAt b C ctl abs).fnAddr name = b + BitVec.ofNat 64 off := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, h]

private theorem sepWPp_pure_mid_inMemSelf {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P1 P2 P3 : SepProp} {φ : Prop} {Q Qp : Arm64.State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3) Q Qp) :
    SepWPp prog ret s (P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3) Q Qp := by
  rw [show P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3 = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 by ac_rfl]
  exact SepWPp.pure_elim h

private theorem idKp_shim_adrp_inMemSelf {b : BitVec 64}
    {H : String → Option (Arm64.State → Arm64.State)} (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr getIdentityKeyPairShimName + 36#64) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair" + 36)) := by
  rw [Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"),
    BitVec.add_assoc, ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

private theorem regId_shim_adrp_inMemSelf {b : BitVec 64}
    {H : String → Option (Arm64.State → Arm64.State)} (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr getLocalRegistrationIdShimName + 36#64) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id" + 36)) := by
  rw [Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"),
    BitVec.add_assoc, ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

set_option maxHeartbeats 1200000 in
private theorem inMemKpShim_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (Arm64.State → Arm64.State)}
    (hA : AllocHooks A abs) (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + (inMemIdentitySelfStoreSpec A b).kpShimOff)
      (kitKpShimSpec (inMemIdentitySelfStoreSpec A b)) := by
  have hfn : libsignalSessionCode.fnOff getIdentityKeyPairShimName =
      num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair") :=
    getIdentityKeyPairShim_fnOff
  change subroutine_ok (tripleRatchetProgAt b C ctl abs)
    (b + BitVec.ofNat 64 (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair")))
    (kitKpShimSpec (inMemIdentitySelfStoreSpec A b))
  rw [← fnAddr_progAt_inMemSelf (b := b) (C := C) (ctl := ctl) (abs := abs) hfn]
  simp only [kitKpShimSpec, inMemIdentitySelfStoreSpec, inMemId16BoxAt, inMemId16ShimStack,
    stackAt_inMemSelfShim]
  cells_unfold
  have hshim := noAllocShim_ok_at (b := b) (C := C) (ctl := ctl) (abs := abs)
    (name := getIdentityKeyPairShimName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"))
  have halloc := alloc_ok_at_norm (b := b) (C := C) (ctl := ctl)
    (name := getIdentityKeyPairShimName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair")) hA
  have hpanic : (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr getIdentityKeyPairShimName + BitVec.ofNat 64
        (num% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"))) =
      some Rust.panicked :=
    panic_at_panicSymbol (hname := "alloc::alloc::handle_alloc_error") hfn
      (show (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair")) +
          num% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair") =
        libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
  code_fetches CryptoVerification.libsignalSessionCode storeEmpty b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn
    (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair")) 76
  wpp_init self s0
  have hadrp := idKp_shim_adrp_inMemSelf (H := Rust.withPanics (tripleRatchetExterns C ctl abs)) hb
  examples_generalize_entry
  examples_hide_fetches
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (32))
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (16, 8)
  apply SepWP.done (by simp_all) (by simp_all)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_inMemSelf fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine SepWPp.panic (by simp_all) (by simp_all) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp_all [Rust.panicked])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_inMemSelf, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid_inMemSelf fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

set_option maxHeartbeats 1200000 in
private theorem inMemRegIdShim_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (Arm64.State → Arm64.State)}
    (hA : AllocHooks A abs) (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + (inMemIdentitySelfStoreSpec A b).regIdShimOff)
      (kitRegIdShimSpec (inMemIdentitySelfStoreSpec A b)) := by
  have hfn : libsignalSessionCode.fnOff getLocalRegistrationIdShimName =
      num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id") :=
    getLocalRegistrationIdShim_fnOff
  change subroutine_ok (tripleRatchetProgAt b C ctl abs)
    (b + BitVec.ofNat 64 (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id")))
    (kitRegIdShimSpec (inMemIdentitySelfStoreSpec A b))
  rw [← fnAddr_progAt_inMemSelf (b := b) (C := C) (ctl := ctl) (abs := abs) hfn]
  simp only [kitRegIdShimSpec, inMemIdentitySelfStoreSpec, inMemId16BoxAt, inMemId16ShimStack,
    stackAt_inMemSelfShim]
  cells_unfold
  have hshim := noAllocShim_ok_at (b := b) (C := C) (ctl := ctl) (abs := abs)
    (name := getLocalRegistrationIdShimName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"))
  have halloc := alloc_ok_at_norm (b := b) (C := C) (ctl := ctl)
    (name := getLocalRegistrationIdShimName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id")) hA
  have hpanic : (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr getLocalRegistrationIdShimName + BitVec.ofNat 64
        (num% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"))) =
      some Rust.panicked :=
    panic_at_panicSymbol (hname := "alloc::alloc::handle_alloc_error") hfn
      (show (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id")) +
          num% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id") =
        libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
  code_fetches CryptoVerification.libsignalSessionCode storeEmpty b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn
    (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id")) 76
  wpp_init self s0
  have hadrp := regId_shim_adrp_inMemSelf (H := Rust.withPanics (tripleRatchetExterns C ctl abs)) hb
  examples_generalize_entry
  examples_hide_fetches
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (32))
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (16, 8)
  apply SepWP.done (by simp_all) (by simp_all)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_inMemSelf fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine SepWPp.panic (by simp_all) (by simp_all) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp_all [Rust.panicked])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_inMemSelf, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid_inMemSelf fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

private theorem pointsToBytes_len32_words4 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (w0 w1 w2 w3 : BitVec 64), ∀ a : BitVec 64,
      (a ↦ₛ bs) =
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  have hw0 : (bs.take 8).length = 8 := by simp [h]
  have hw1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have hw2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have hw3 : (bs.drop 24).length = 8 := by simp [h]
  obtain ⟨w0, hw0_eq⟩ := exists_unpack64_of_length_8 hw0
  obtain ⟨w1, hw1_eq⟩ := exists_unpack64_of_length_8 hw1
  obtain ⟨w2, hw2_eq⟩ := exists_unpack64_of_length_8 hw2
  obtain ⟨w3, hw3_eq⟩ := exists_unpack64_of_length_8 hw3
  have hbs : bs = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 := by
    rw [← hw0_eq, ← hw1_eq, ← hw2_eq, ← hw3_eq]
    simp only [List.append_assoc]
    have s2 : (bs.drop 16).take 8 ++ bs.drop 24 = bs.drop 16 := by
      have := List.take_append_drop 8 (bs.drop 16)
      rwa [List.drop_drop] at this
    have s1 : (bs.drop 8).take 8 ++ bs.drop 16 = bs.drop 8 := by
      have := List.take_append_drop 8 (bs.drop 8)
      rwa [List.drop_drop] at this
    rw [s2, s1, List.take_append_drop]
  refine ⟨w0, w1, w2, w3, fun a => ?_⟩
  rw [hbs]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion72_split_kpPoll (out : BitVec 64) :
    memRegion out 72 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
       ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
       ∃∗ b0 : BitVec 8,
        (out ↦₈ b0) ∗
        ((out + 0x01#64) ↦₆₄ u0) ∗ ((out + 0x09#64) ↦₆₄ u1) ∗
        ((out + 0x11#64) ↦₆₄ u2) ∗ ((out + 0x19#64) ↦₆₄ u3) ∗
        ((out + 0x21#64) ↦₆₄ u4) ∗ ((out + 0x29#64) ↦₆₄ u5) ∗
        ((out + 0x31#64) ↦₆₄ u6) ∗ ((out + 0x39#64) ↦₆₄ u7) ∗
        memRegion (out + 0x41#64) 7) := by
  have hc : memRegion (out + 1#64) 64 = cells (out + 1#64) 8 :=
    ProofLib.memRegion_cells (out + 1#64) 8 (by decide)
  rw [show (72 : Nat) = 1 + (64 + 7) from rfl,
      memRegion_split out 1 71 (by decide),
      memRegion_split (out + 1#64) 64 7 (by decide),
      memRegion_one out, hc]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem memRegion48_split_regIdPoll (out : BitVec 64) :
    memRegion out 48 =
      (∃∗ u8 : BitVec 32, ∃∗ u0 : BitVec 64,
        (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₃₂ u8) ∗ memRegion (out + 0xc#64) 36) := by
  rw [show (48 : Nat) = 8 + (4 + 36) from rfl,
      memRegion_split out 8 40 (by decide),
      memRegion_split (out + 8#64) 4 36 (by decide),
      ProofLib.memRegion_eight out,
      ProofLib.memRegion_four (out + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem inMemKpPoll_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (Arm64.State → Arm64.State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + (inMemIdentitySelfStoreSpec A b).kpPollOff)
      (kitKpPollSpecE (inMemIdentitySelfStoreSpec A b)) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨fut, out, self, kp, reg⟩ R s0 hpc hrun hp hsp
  obtain ⟨ik0, ik1, ik2, ik3, hikPub⟩ :=
    pointsToBytes_len32_words4 (List.Vector.toList_length kp.identityKey.publicKey.bytes)
  obtain ⟨ik4, ik5, ik6, ik7, hikPriv⟩ :=
    pointsToBytes_len32_words4 (List.Vector.toList_length kp.privateKey.bytes)
  dsimp only [kitKpPollSpecE, withEnvPre, kitKpPollSpec, inMemIdentitySelfStoreSpec,
    inMemSelfIdentityStoreSpec, inMemSelfIdentityAt, inMemId16BoxAt] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨_, hp⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hx0, hx8⟩, hp⟩
  rw [hikPub (self + 0x30#64), hikPriv (self + 0x50#64), memRegion72_split_kpPoll out] at hp
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc] at hp
  rcases hp with ⟨u0, u1, u2, u3, u4, u5, u6, u7, b0, hp⟩
  let g : GetIdentityKeyPairPollGhost :=
    { futPtr := fut, sret := out, self := self,
      ik0 := ik0, ik1 := ik1, ik2 := ik2, ik3 := ik3,
      ik4 := ik4, ik5 := ik5, ik6 := ik6, ik7 := ik7,
      b_sret0 := b0, u0 := u0, u1 := u1, u2 := u2, u3 := u3,
      u4 := u4, u5 := u5, u6 := u6, u7 := u7 }
  let R' : SepProp :=
    memRegion (fut + 9#64) 7 ∗ ((self + 0x70#64) ↦₃₂ reg) ∗
      memRegion (out + 0x41#64) 7 ∗ A.pool ∗ stackAt s0.sp 0 ∗ R
  have hp' : s0.mem ⊨ getIdentityKeyPairPollSpec.pre g s0 ∗ R' := by
    dsimp only [getIdentityKeyPairPollSpec, g, R']
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8⟩, ?_⟩
    exact Satisfies.congr_prop (by ac_rfl) hp
  refine ((getIdentityKeyPairPoll_ok (b := b) (C := C) (ctl := ctl) (abs := abs)).to_outcome
      g R' s0 hpc hrun hp' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [getIdentityKeyPairPollSpec, g, R'] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    have hpubSelf := hikPub (self + 0x30#64)
    have hprivSelf := hikPriv (self + 0x50#64)
    have hpubOut := hikPub (out + 1#64)
    have hprivOut := hikPriv (out + 0x21#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpubSelf hprivSelf hpubOut hprivOut
    dsimp only [kitKpPollSpecE, withEnvPre, kitKpPollSpec, inMemIdentitySelfStoreSpec,
      inMemSelfIdentityStoreSpec, inMemSelfIdentityAt, inMemId16BoxAt]
    apply Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro (.ok kp)))
    dsimp only [kpPollOutAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨rfl, htrace.trans (List.append_nil _).symm⟩, ?_⟩
    rw [hpubSelf, hprivSelf, hpubOut, hprivOut]
    exact Satisfies.congr_prop (by ac_rfl) hq
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem inMemRegIdPoll_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (Arm64.State → Arm64.State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + (inMemIdentitySelfStoreSpec A b).regIdPollOff)
      (kitRegIdPollSpecE (inMemIdentitySelfStoreSpec A b)) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨fut, out, self, kp, reg⟩ R s0 hpc hrun hp hsp
  dsimp only [kitRegIdPollSpecE, withEnvPre, kitRegIdPollSpec, inMemIdentitySelfStoreSpec,
    inMemSelfIdentityStoreSpec, inMemSelfIdentityAt, inMemId16BoxAt] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨_, hp⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hx0, hx8⟩, hp⟩
  rw [memRegion48_split_regIdPoll out] at hp
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc] at hp
  rcases hp with ⟨u8, u0, hp⟩
  let g : GetLocalRegIdPollGhost :=
    { futPtr := fut, sret := out, self := self, regId := reg, u_sret0 := u0, u_sret8 := u8 }
  let R' : SepProp :=
    memRegion (fut + 9#64) 7 ∗
      ((self + 0x30#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((self + 0x50#64) ↦ₛ kp.privateKey.bytes.toList) ∗
      memRegion (out + 0xc#64) 36 ∗ A.pool ∗ stackAt s0.sp 0 ∗ R
  have hp' : s0.mem ⊨ getLocalRegIdPollSpec.pre g s0 ∗ R' := by
    dsimp only [getLocalRegIdPollSpec, g, R']
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8⟩, ?_⟩
    exact Satisfies.congr_prop (by ac_rfl) hp
  refine ((getLocalRegIdPoll_ok (b := b) (C := C) (ctl := ctl) (abs := abs)).to_outcome
      g R' s0 hpc hrun hp' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [getLocalRegIdPollSpec, g, R'] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    dsimp only [kitRegIdPollSpecE, withEnvPre, kitRegIdPollSpec, inMemIdentitySelfStoreSpec,
      inMemSelfIdentityStoreSpec, inMemSelfIdentityAt, inMemId16BoxAt]
    apply Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro (.ok reg)))
    dsimp only [regIdPollOutAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨rfl, htrace.trans (List.append_nil _).symm⟩, ?_⟩
    exact Satisfies.congr_prop (by ac_rfl) hq
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

end InMemWitness

/-- Non-vacuity witness: `inMemIdentitySelfStoreSpec A b` satisfies `IdentitySelfStoreKitOk` at
`ext := tripleRatchetExterns C ctl abs`. -/
theorem inMemIdentitySelfStoreSpec_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) (hb : b &&& 0xfff#64 = 0#64) :
    IdentitySelfStoreKitOk (inMemIdentitySelfStoreSpec A b)
      (tripleRatchetExterns C ctl abs) :=
  IdentitySelfStoreKitOk.ofProgAt
    (inMemKpShim_ok hA hb)
    inMemKpPoll_ok
    CryptoVerification.E2E.InMem.IdentityKeyStoreImpl.futDrop_ok
    (inMemRegIdShim_ok hA hb)
    inMemRegIdPoll_ok
    CryptoVerification.E2E.InMem.IdentityKeyStoreImpl.futDrop_ok

/-- Non-vacuity witness: `inMemIdentitySelfStoreSpec A b` satisfies `IdentitySelfStoreKitOkI` at
`ext := tripleRatchetExterns C ctl abs` via `.toI`. -/
theorem inMemIdentitySelfStoreSpec_okI {A : RustAlloc} {b : BitVec 64}
    {img : Obj.Image} {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) (hb : b &&& 0xfff#64 = 0#64) :
    IdentitySelfStoreKitOkI img (inMemSelfIdentityStoreSpec A b)
      (inMemIdentitySelfStoreSpec A b) (tripleRatchetExterns C ctl abs) :=
  (inMemIdentitySelfStoreSpec_ok hA hb).toI

end CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf

namespace CryptoVerification.LibsignalPublicApi.StoreKit

export IdentitySelf
  (kpPollOutAt regIdPollOutAt
   IdentitySelfStoreSpec IdentitySelfStoreSpec.Quiet
   kitKpShimSpec kitRegIdShimSpec
   kitKpPollSpec kitRegIdPollSpec
   kitKpPollSpecE kitRegIdPollSpecE
   kitKpPollSpecI kitRegIdPollSpecI
   IdentitySelfVtablesOk
   IdentitySelfStoreKitOk IdentitySelfStoreKitOkI
   IdentitySelfStoreKitOk.toI
   tripleRatchetProgAt_eq_ext
   IdentitySelfStoreKitOk.ofProgAt
   IdentitySelfStoreKitOkI.ofProgAt
   inMemSelfIdentityAt inMemSelfIdentityStoreSpec
   inMemSelfSpeErrSpec inMemIdentitySelfStoreSpec
   inMemIdentitySelfStoreSpec_quiet
   inMemSelf_kpRel_error_iff inMemSelf_regIdRel_error_iff
   inMemSelf_kpErr_layout inMemSelf_regIdErr_layout
   inMemIdentitySelfStoreSpec_ok inMemIdentitySelfStoreSpec_okI)

end CryptoVerification.LibsignalPublicApi.StoreKit
