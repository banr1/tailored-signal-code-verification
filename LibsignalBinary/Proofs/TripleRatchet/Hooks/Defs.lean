/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WPp
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalTripleRatchetProofDefs
public import LibsignalBinary.Proofs.TripleRatchet.Prog
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst

/-!
# Triple-Ratchet Extern Hook Specifications

Separation-logic contracts for allocator/memory shims, X25519 and SHA-256 primitives,
RNG fill, public-key and service-ID parsers, and slow varint decoding, bundled into
`ExtStubsOK` and `HooksOK`.
-/

set_option warningAsError false

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession (blackBoxHook)

abbrev shimName : String := "__rustc::__rust_no_alloc_shim_is_unstable_v2"
abbrev allocName : String := "__rustc::__rust_alloc"
abbrev deallocName : String := "__rustc::__rust_dealloc"
abbrev reallocName : String := "__rustc::__rust_realloc"
abbrev memcpyName : String := "memcpy"
abbrev memmoveName : String := "memmove"
abbrev memsetName : String := "memset"
abbrev vecRemoveAssertFailedName : String := "<alloc::vec::Vec<_, _>>::remove::assert_failed"
abbrev handleErrorName : String := "alloc::raw_vec::handle_error"
abbrev handleAllocErrorName : String := "alloc::alloc::handle_alloc_error"

/-- `__rustc::__rust_no_alloc_shim_is_unstable_v2`: no-op shim (`hookNoop`) preserving memory,
registers, and trace. -/
def sessionShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

/-- Region-only `memcpy(dst = x0, src = x1, len = x2)` contract with trace preservation.
Ghost: `(dst, src, bs)`. -/
def sessionMemcpyRegionSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := memcpyRegionSpec.pre
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs)

/-- Stack-framed `memcpy(dst = x0, src = x1, len = x2)` contract with trace preservation.
Ghost: `(dst, src, bs)`. -/
def sessionMemcpySpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := (libcMemcpySpec hookStack).pre
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp hookStack

/-- In-buffer overlapping `memmove(base + dst = x0, base + src = x1, len = x2)` contract with
trace preservation. Ghost: `(base, buf, dst, src, len)`. -/
def sessionMemmoveSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) where
  pre := (libcMemmoveSpec hookStack).pre
  post := fun (base, buf, dst, src, len) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧ sf.trace = s0.trace⌝ ∗
      (base ↦ₛ listMove buf dst src len) ∗ stackAt s0.sp hookStack

/-- Region-only `memset(ptr = x0, c = w1, len = x2)` contract with trace preservation.
Ghost: `(ptr, c, len)`. -/
def sessionMemsetRegionSpec : Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := memsetRegionSpec.pre
  post := fun (ptr, c, len) s0 sf =>
    ⌜sf.readReg64 .x0 = ptr ∧ sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ List.replicate len c)

/-- Stack-framed `memset(ptr = x0, c = w1, len = x2)` contract with trace preservation.
Ghost: `(ptr, c, len)`. -/
def sessionMemsetSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := (libcMemsetSpec hookStack).pre
  post := fun (ptr, c, len) s0 sf =>
    ⌜sf.readReg64 .x0 = ptr ∧ sf.trace = s0.trace⌝ ∗
      (ptr ↦ₛ List.replicate len c) ∗ stackAt s0.sp hookStack

/-- `<StaticSecret>::diffie_hellman(self = x0, their_public = x1)` (sret `x8`, 32 bytes):
writes `(X sec pub).toList` at `ret`. Ghost: `(secA, sec, pubA, pub, ret)`. -/
def diffieHellmanSpec (X : Ratchet.X25519Fn) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64) where
  pre := fun (secA, sec, pubA, pub, ret) s =>
    ⌜s.readReg64 .x0 = secA ∧ s.readReg64 .x1 = pubA ∧ s.readReg64 .x8 = ret⌝ ∗
      (secA ↦ₛ sec.toList) ∗ (pubA ↦ₛ pub.toList) ∗ memRegion ret 32
  post := fun (secA, sec, pubA, pub, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (secA ↦ₛ sec.toList) ∗ (pubA ↦ₛ pub.toList) ∗ (ret ↦ₛ (X sec pub).toList)

/-- `<x25519_dalek::PublicKey as From<&StaticSecret>>::from(x0 = &secret)` (sret `x8`, 32 bytes):
writes `(pubKey sec).toList` at `ret`. Ghost: `(secA, sec, ret)`. -/
def pubFromSecretSpec (pubKey : PubKeyFn) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64) where
  pre := fun (secA, sec, ret) s =>
    ⌜s.readReg64 .x0 = secA ∧ s.readReg64 .x8 = ret⌝ ∗
      (secA ↦ₛ sec.toList) ∗ memRegion ret 32
  post := fun (secA, sec, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (secA ↦ₛ sec.toList) ∗ (ret ↦ₛ (pubKey sec).toList)

/-- `<StaticSecret as Drop>::drop` / `<SharedSecret as Drop>::drop` (`x0 = self`, 32 bytes):
zeroes the 32 bytes at `a`. Ghost: `a`. -/
def zeroizeSecretSpec : Spec (BitVec 64) where
  pre := fun a s => ⌜s.readReg64 .x0 = a⌝ ∗ memRegion a 32
  post := fun a s0 sf => ⌜sf.trace = s0.trace⌝ ∗ (a ↦ₛ List.replicate 32 0#8)

/-- `libsignal_session_rng_fill(dst = x0, len = x1)`: writes `(rest ++ List.replicate len 0#8).take len`
at `dst` and advances the tape at `ctl` by `min len rest.length`. Ghost: `(dst, len, cur, rest)`. -/
def rngFillSpec (ctl : BitVec 64) : Spec (BitVec 64 × Nat × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, len, cur, rest) s =>
    ⌜s.readReg64 .x0 = dst ∧ (s.readReg64 .x1).toNat = len⌝ ∗
      memRegion dst len ∗ tapeAt ctl cur rest
  post := fun (dst, len, cur, rest) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ (rest ++ List.replicate len 0#8).take len) ∗
      tapeAfter ctl cur rest (min len rest.length)

abbrev blackBoxName : String := "subtle::black_box::<u8>"

/-- `subtle::black_box::<u8>(input = w0) -> u8`: masks `x0` to `(v.setWidth 8).zeroExtend 64`
and preserves memory and trace. -/
def blackBoxSpec : Spec (BitVec 64) where
  pre := fun v s => ⌜s.readReg64 .x0 = v⌝
  post := fun v s0 sf =>
    ⌜sf.readReg64 .x0 = (v.setWidth 8).zeroExtend 64 ∧ sf.trace = s0.trace⌝

abbrev compress256Name : String := "sha2::sha256::compress256"

/-- `sha2::sha256::compress256(state = x0, blocks.ptr = x1, blocks.len = x2)`: folds `n` 64-byte
blocks `bs` at `blkA` into the 8-word LE SHA-256 chaining state `st` at `stA` via `F`.
Ghost: `(stA, st, blkA, bs, n)`. -/
def compress256Spec (F : ShaState → List (BitVec 8) → ShaState) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (stA, st, blkA, bs, n) s =>
    ⌜s.readReg64 .x0 = stA ∧ s.readReg64 .x1 = blkA ∧ (s.readReg64 .x2).toNat = n ∧
      bs.length = 64 * n⌝ ∗
      (stA ↦ₛ LibsignalHmac.shaStateBytes st) ∗ (blkA ↦ₛ bs)
  post := fun (stA, st, blkA, bs, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (stA ↦ₛ LibsignalHmac.shaStateBytes ((chunks64 bs).foldl F st)) ∗ (blkA ↦ₛ bs)

/-- The 40-byte `Result<PublicKey, CurveError>` layout at `out`:
* `.ok k` = tag byte `0` at `+0`, 32 key bytes at `+1..+33`, 7 bytes at `+33..+40`;
* `.error .noKeyTypeIdentifier` = tag byte `1` at `+0`, discriminant `0` at `+8`;
* `.error (.badKeyType t)` = tag byte `1` at `+0`, discriminant `1` at `+8`, type byte `t` at `+9`;
* `.error (.badKeyLength n)` = tag byte `1` at `+0`, discriminant `2` at `+8`, length `n` at `+16`. -/
def pkTryFromResultAt (out : BitVec 64) : Except SignalProtocolError PublicKey → SepProp
  | .ok k => (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ k.bytes.toList) ∗ memRegion (out + 33#64) 7
  | .error .noKeyTypeIdentifier =>
    (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 31
  | .error (.badKeyType t) =>
    (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗ ((out + 8#64) ↦₈ 1#8) ∗ ((out + 9#64) ↦₈ t) ∗
      memRegion (out + 10#64) 30
  | .error (.badKeyLength n) =>
    (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 7 ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (out + 24#64) 16
  | .error _ => ⌜False⌝

/-- `<PublicKey as TryFrom<&[u8]>>::try_from(x0 = ptr, x1 = len)` (sret `x8`, 40 bytes):
writes `pkTryFromResultAt out (PublicKey.deserialize bs)`. Ghost: `(p, bs, out)`. -/
def pkTryFromSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p, bs, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 40
  post := fun (p, bs, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ pkTryFromResultAt out (PublicKey.deserialize bs)

/-- The 17-byte `Option<ServiceId>` layout at `out`:
* `some (pni, uuid)` = tag byte `kindByte pni` at `+0`, 16 UUID bytes at `+1..+17`;
* `none` = tag byte `2` at `+0`, 16 bytes at `+1..+17`. -/
def parseSidResultAt (out : BitVec 64) : Option (Bool × List.Vector (BitVec 8) 16) → SepProp
  | some (pni, uuid) => (out ↦₈ kindByte pni) ∗ ((out + 1#64) ↦ₛ uuid.toList)
  | none => (out ↦₈ 2#8) ∗ memRegion (out + 1#64) 16

/-- `ServiceId::parse_from_service_id_string(x0 = ptr, x1 = len)` (sret `x8`, 17 bytes):
writes `parseSidResultAt out (parse bs)`. Ghost: `(p, bs, out)`. -/
def parseSidSpec (parse : ServiceIdParser) : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p, bs, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 17
  post := fun (p, bs, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ parseSidResultAt out (parse bs)

/-- Stack budget for `decode_varint_slow::<&mut &[u8]>`: its 64-byte scratch frame plus
`decodeErrorHookStack` for the `DecodeError::from` call on the error path. -/
abbrev varintSlowStack : Nat := 64 + decodeErrorHookStack

/-- `prost::encoding::varint::decode_varint_slow::<&mut &[u8]>(x0 = &mut &mut &[u8])`:
decodes up to 10 bytes from the slice `(ptr, bs.length)` at `slot` (`*slotA = slot`):
* `varintSlow bs = some (v, k)`: advances the slice by `k`, returns `x0 = 0`, `x1 = v`;
* `varintSlow bs = none`: advances the slice by `min 10 bs.length`, allocates a fresh
  `decodeErrorAtStackLen A x1 0` via `DecodeError::from`, and returns `x0 = 1`, `x1 ≠ 0`.
Ghost: `(slotA, slot, ptr, bs)`. -/
def decodeVarintSlowSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (slotA, slot, ptr, bs) s =>
    ⌜s.readReg64 .x0 = slotA ∧ bs.length < 2 ^ 64⌝ ∗
      (slotA ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s.sp varintSlowStack
  post := fun (slotA, slot, ptr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp varintSlowStack ∗
      match varintSlow bs with
      | some (v, k) =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝ ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k))
      | none =>
        ⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length))) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length))
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Predicate asserting that the 11 abstract / abs-delegated extern stubs satisfy their
    `subroutine_ok` contracts on `contractProg b ext`, and that `ext` preserves `tpidrEl0`
    and non-executable memory permissions. -/
structure ExtStubsOK (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop where
  alloc : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff allocName) spec
  dealloc : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff deallocName) spec
  realloc : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff reallocName) spec
  aesEnc : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff aesEncName) spec
  aesDec : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff aesDecName) spec
  bcmp : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff "bcmp") spec
  randomKeys : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff "std::sys::random::linux::hashmap_random_keys") spec
  formatInner : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff formatInnerName) spec
  fmtWrite : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff fmtWriteName) spec
  stringClone : ∃ α, ∃ spec : Spec α,
    subroutine_ok (contractProg b ext) (b + stubOff "<alloc::string::String as core::clone::Clone>::clone") spec
  tpidr_preserved : ∀ n f, ext n = some f → ∀ s, (f s).tpidrEl0 = s.tpidrEl0
  perm_x_preserved : ∀ n f, ext n = some f → ∀ s a, ((f s).mem.perm a).x → (s.mem.perm a).x

/-- Full contract hook predicate: both the 11 modelled TripleRatchet stubs and
    the 10 abs-delegated stubs hold. -/
def HooksOK (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  TRStubsOK b C ctl ext ∧ ExtStubsOK b C ctl ext

end CryptoVerification.LibsignalTripleRatchet
