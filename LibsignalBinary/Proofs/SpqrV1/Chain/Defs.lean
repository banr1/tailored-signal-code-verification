/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.Repr
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import ProofLib.BV.WidthNorm

/-!
# Specifications for SPQR V1 Chain (`next_key_internal` and `Chain::new`)

Callee hypotheses (`Concat<u8>::concat [local#2]`, `spqr::kdf::hkdf_to_slice`,
`<VecDeque<ChainEpoch>>::grow`) and target specifications for
`<spqr::chain::ChainEpochDirection>::next_key_internal` (`0x5fd94`, 68 instructions) and
`<spqr::chain::Chain>::new` (`0x5fea4`, 116 instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet

abbrev sliceConcatName : String :=
  "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"

abbrev hkdfToSliceName : String :=
  "spqr::kdf::hkdf_to_slice"

abbrev vecDequeGrowName : String :=
  "<alloc::collections::vec_deque::VecDeque<spqr::chain::ChainEpoch>>::grow"

abbrev nextKeyInternalName : String :=
  "<spqr::chain::ChainEpochDirection>::next_key_internal"

abbrev chainNewName : String :=
  "<spqr::chain::Chain>::new"

/-! ## Stack budgets -/

/-- `<spqr::chain::ChainEpochDirection>::next_key_internal` frame (`0xb0 = 176` B) + `extHookStack`. -/
abbrev nextKeyInternalStackX : Nat := 176 + extHookStack

/-- `<spqr::chain::Chain>::new` frame (`0xe0 = 224` B) + `extHookStack`. -/
abbrev chainNewStackX : Nat := 224 + extHookStack

/-! ## Read-only / read-write byte slice helper -/

/-- Byte slice permission at `p`: read-only (`p ↦ᵣ bs`) when `ro = true`, read-write (`p ↦ₛ bs`)
when `ro = false`. -/
def bytesAt (ro : Bool) (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if ro then p ↦ᵣ bs else p ↦ₛ bs

@[simp] theorem bytesAt_true (p : BitVec 64) (bs : List (BitVec 8)) :
    bytesAt true p bs = (p ↦ᵣ bs) := rfl

@[simp] theorem bytesAt_false (p : BitVec 64) (bs : List (BitVec 8)) :
    bytesAt false p bs = (p ↦ₛ bs) := rfl

/-! ## `Concat<u8>::concat [local#2]` (`0x63eb0`, 124 instructions) -/

/-- Ghost arguments for `<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]` (`0x63eb0`)
called on a 2-element slice array `&[s0, s1]`. -/
structure SliceConcat2Ghost where
  outVec : BitVec 64
  slicesA : BitVec 64
  ro0 : Bool
  p0 : BitVec 64
  bs0 : List (BitVec 8)
  ro1 : Bool
  p1 : BitVec 64
  bs1 : List (BitVec 8)

/-- Spec of `<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]` (`0x63eb0`) for `len = 2`:
* `x0 = outVec` (24-byte `Vec<u8>` sret), `x1 = slicesA` (32-byte `[&[u8]; 2]` header array),
  `x2 = 2#64`.
* Allocates a `Vec<u8>` at `outVec` containing `bs0 ++ bs1`, or panics on OOM. -/
def sliceConcat2Spec (A : RustAlloc) : Spec SliceConcat2Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 2#64 ∧
      x.bs0.length + x.bs1.length < 2 ^ 63⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      bytesAt x.ro0 x.p0 x.bs0 ∗ bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A x.outVec (x.bs0 ++ x.bs1) ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      bytesAt x.ro0 x.p0 x.bs0 ∗ bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def SliceConcat2OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr sliceConcatName)
    ((sliceConcat2Spec A).inImage img)

/-! ## `spqr::kdf::hkdf_to_slice` (`0x63284`, 473 instructions) -/

/-- Ghost arguments for `spqr::kdf::hkdf_to_slice` (`0x63284`). -/
structure HkdfToSliceGhost where
  saltRO : Bool
  saltA : BitVec 64
  salt : List (BitVec 8)
  ikmRO : Bool
  ikmA : BitVec 64
  ikm : List (BitVec 8)
  infoRO : Bool
  infoA : BitVec 64
  info : List (BitVec 8)
  okmA : BitVec 64
  okmLen : Nat

/-- SPQR V1 spec of `spqr::kdf::hkdf_to_slice` (`src/kdf.rs:13–18`, image offset `0x63284`,
473 instructions):
* `x0 = saltA`, `x1 = salt.length` (`salt: &[u8]`, `salt.length < 2 ^ 63`)
* `x2 = ikmA`, `x3 = ikm.length` (`ikm: &[u8]`, `ikm.length < 2 ^ 63`)
* `x4 = infoA`, `x5 = info.length` (`info: &[u8]`, `32 ≤ info.length < 55`)
* `x6 = okmA`, `x7 = okmLen` (`okm: &mut [u8]`, `okmLen ∈ {32, 64, 96}`)
* Writes `hkdf salt ikm info okmLen` (of length `okmLen`) to `[okmA .. okmA + okmLen)`. -/
def hkdfToSliceSpec (hkdf : HkdfFn) : Spec HkdfToSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
      s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
      s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
      s.readReg64 .x6 = x.okmA ∧ s.readReg64 .x7 = BitVec.ofNat 64 x.okmLen ∧
      x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
      32 ≤ x.info.length ∧ x.info.length < 55 ∧
      (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96)⌝ ∗
      bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      memRegion x.okmA x.okmLen ∗
      stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜(hkdf x.salt x.ikm x.info x.okmLen).length = x.okmLen ∧ sf.trace = s0.trace⌝ ∗
      bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      (x.okmA ↦ₛ hkdf x.salt x.ikm x.info x.okmLen) ∗
      stackAt s0.sp extHookStack

abbrev hkdfToSliceSpqrSpec (hkdf : HkdfFn) : Spec HkdfToSliceGhost :=
  hkdfToSliceSpec hkdf

def HkdfToSliceSpqrOkX (img : Obj.Image) (hkdf : HkdfFn)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
    ((hkdfToSliceSpqrSpec hkdf).inImage img)

abbrev HkdfToSliceOkX (img : Obj.Image) (hkdf : HkdfFn)
    (ext : String → Option (State → State)) : Prop :=
  HkdfToSliceSpqrOkX img hkdf ext

/-! ## `<VecDeque<ChainEpoch>>::grow` (`0x5f93c`, 23 instructions) -/

/-- New capacity of `VecDeque<ChainEpoch>` after `grow` (`MIN_NON_ZERO_CAP = 4` for 112-byte
`ChainEpoch`). -/
def newCapChainEpoch (cap : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (max (2 * cap.toNat) 4)

/-- Ghost arguments for `<VecDeque<ChainEpoch>>::grow` (`0x5f93c`). -/
structure VecDequeGrowGhost where
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  head : BitVec 64
  xs : List (ChainEpochGhost × ChainEpoch)

/-- Spec of `<alloc::collections::vec_deque::VecDeque<spqr::chain::ChainEpoch>>::grow` (`0x5f93c`):
* `x0 = v` (`&mut VecDeque<ChainEpoch>`, full: `xs.length = cap.toNat`).
* Reallocates the ring buffer to capacity `newCapChainEpoch cap = max (2 * cap.toNat) 4` at `ptr'`
  (preserving `head' = 0#64` whenever `head = 0#64`), or panics on OOM. -/
def vecDequeGrowSpec (A : RustAlloc) : Spec VecDequeGrowGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.xs.length = x.cap.toNat ∧
      max (2 * x.cap.toNat) 4 * chainEpochSize < 2 ^ 63⌝ ∗
      vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A)
        x.v x.cap x.ptr x.head x.xs ∗
      A.pool ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ (ptr' : BitVec 64), ∃∗ (head' : BitVec 64),
        ⌜x.head = 0#64 → head' = 0#64⌝ ∗
        vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A)
          x.v (newCapChainEpoch x.cap) ptr' head' x.xs) ∗
      A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def VecDequeGrowOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr vecDequeGrowName)
    ((vecDequeGrowSpec A).inImage img)

/-! ## `<spqr::chain::ChainEpochDirection>::next_key_internal` (`0x5fd94`, 68 instructions) -/

/-- Ghost arguments of `<ChainEpochDirection>::next_key_internal` (`0x5fd94`). -/
structure NextKeyInternalGhost where
  /-- Sret pointer (`x0`, 36-byte `(u32, [u8; 32])` output tuple). -/
  out : BitVec 64
  /-- `next: &mut [u8]` pointer (`x1`) and 32-byte contents (`x2 = 32#64`). -/
  nextA : BitVec 64
  next : List (BitVec 8)
  /-- `ctr: &mut u32` pointer (`x3`) and value (`ctr ≠ 0xffffffff#32`). -/
  ctrA : BitVec 64
  ctr : BitVec 32

/-- Next chain key (`genr8r[..32]`) produced by `next_key_internal`. -/
def nextKeyNext (hkdf : HkdfFn) (next : Bytes) (ctr : BitVec 32) : Bytes :=
  (hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64).take 32

/-- Returned message key (`genr8r[32..64]`) produced by `next_key_internal`. -/
def nextKeyOut (hkdf : HkdfFn) (next : Bytes) (ctr : BitVec 32) : Bytes :=
  ((hkdf (List.replicate 32 0#8) next (toBEBytes 4 (ctr + 1#32) ++ chainNextInfo) 64).drop 32).take 32

theorem nextKeyInternal_eq_ok (hkdf : HkdfFn) {next : Bytes} {ctr : BitVec 32}
    (hlen : next.length = 32) (hctr : ctr ≠ 0xffffffff#32) :
    ChainEpochDirection.nextKeyInternal hkdf next ctr =
      .ok (nextKeyNext hkdf next ctr, ctr + 1#32, (ctr + 1#32, nextKeyOut hkdf next ctr)) := by
  unfold ChainEpochDirection.nextKeyInternal nextKeyNext nextKeyOut
  have h1 : (next.length != 32) = false := by simp [hlen]
  have h2 : (ctr == 0xffffffff#32) = false := by simp [hctr]
  simp [h1, h2]

/-- Spec of `<spqr::chain::ChainEpochDirection>::next_key_internal` (`src/chain.rs:229–246`,
image offset `0x5fd94`, 68 instructions):
* Registers: `x0 = out` (36-byte `(u32, [u8; 32])` output), `x1 = nextA` (32-byte `next` slice),
  `x2 = 32#64`, `x3 = ctrA` (`&mut u32` with `ctr ≠ 0xffffffff#32`).
* Increments `*ctrA` to `ctr + 1#32`, derives 64 bytes via `hkdf_to_slice`, updates `*nextA` to
  `nextKeyNext hkdf next ctr` (`genr8r[..32]`), and writes `(ctr + 1#32, nextKeyOut hkdf next ctr)`
  at `out`. -/
def nextKeyInternalSpecX (hkdf : HkdfFn) (A : RustAlloc) : Spec NextKeyInternalGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.nextA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = x.ctrA ∧
      x.next.length = 32 ∧ x.ctr ≠ 0xffffffff#32⌝ ∗
      memRegion x.out 36 ∗ (x.nextA ↦ₛ x.next) ∗ (x.ctrA ↦₃₂ x.ctr) ∗
      A.pool ∗ stackAt s.sp nextKeyInternalStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      nextKeyOutAt x.out (x.ctr + 1#32) (nextKeyOut hkdf x.next x.ctr) ∗
      (x.nextA ↦ₛ nextKeyNext hkdf x.next x.ctr) ∗
      (x.ctrA ↦₃₂ (x.ctr + 1#32)) ∗
      A.pool ∗ stackAt s0.sp nextKeyInternalStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def NextKeyInternalOkX (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr nextKeyInternalName)
    ((nextKeyInternalSpecX hkdf A).inImage img)

/-! ## `<spqr::chain::Chain>::new` (`0x5fea4`, 116 instructions) -/

/-- Pure `Chain` value constructed by `Chain.new hkdf initialKey dir params`. -/
def chainNewVal (hkdf : HkdfFn) (initialKey : Bytes) (dir : Direction) (params : ChainParamsPB) :
    Chain :=
  let salt := List.replicate 32 0#8
  let genr8r := hkdf salt initialKey chainStartInfo 96
  let epoch0 : ChainEpoch :=
    { send := Chain.cedForDirection genr8r dir
      recv := Chain.cedForDirection genr8r dir.switch }
  { dir := dir
    currentEpoch := 0#64
    sendEpoch := 0#64
    links := [epoch0]
    nextRoot := genr8r.take 32
    params := params }

@[simp] theorem chain_new_eq_ok (hkdf : HkdfFn) (initialKey : Bytes) (dir : Direction)
    (params : ChainParamsPB) :
    Chain.new hkdf initialKey dir params = .ok (chainNewVal hkdf initialKey dir params) := rfl

/-- Ghost arguments of `<spqr::chain::Chain>::new` (`0x5fea4`). -/
structure ChainNewGhost where
  /-- Sret pointer (`x0`, 88-byte `Result<Chain, Error>` / `Chain` output). -/
  out : BitVec 64
  /-- `initial_key: &[u8]` pointer (`x1`) and contents (`x2 = initialKey.length`). -/
  ikmRO : Bool
  ikmA : BitVec 64
  initialKey : List (BitVec 8)
  /-- `dir: Direction` (`w3 = dir.toI32`). -/
  dir : Direction
  /-- `params: ChainParamsPB` (`w4 = params.maxJump`, `w5 = params.maxOooKeys`). -/
  params : ChainParamsPB

/-- Spec of `<spqr::chain::Chain>::new` (`src/chain.rs:333–354`, image offset `0x5fea4`, 116 instructions):
* Registers: `x0 = out` (88-byte `Chain` sret), `x1 = ikmA`, `x2 = initialKey.length` (`< 2 ^ 63`),
  `w3 = dir.toI32`, `w4 = params.maxJump`, `w5 = params.maxOooKeys`.
* Derives 96 bytes via `hkdf_to_slice`, allocates the initial `ChainEpoch` and `next_root` buffers,
  grows `links` to capacity 4 (`head = 0, len = 1`), and writes `chainNewVal hkdf initialKey dir params`
  at `out` (`chainAt` with `linksCap = 4#64, linksHead = 0#64`). -/
def chainNewSpecX (hkdf : HkdfFn) (A : RustAlloc) : Spec ChainNewGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.ikmA ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.initialKey.length ∧
      (s.readReg64 .x3).setWidth 32 = x.dir.toI32 ∧
      (s.readReg64 .x4).setWidth 32 = x.params.maxJump ∧
      (s.readReg64 .x5).setWidth 32 = x.params.maxOooKeys ∧
      x.initialKey.length < 2 ^ 63⌝ ∗
      memRegion x.out 88 ∗ bytesAt x.ikmRO x.ikmA x.initialKey ∗
      A.pool ∗ stackAt s.sp chainNewStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ G : ChainGhost,
        ⌜G.linksCap = 4#64 ∧ G.linksHead = 0#64⌝ ∗
        chainAt A x.out G (chainNewVal hkdf x.initialKey x.dir x.params)) ∗
      bytesAt x.ikmRO x.ikmA x.initialKey ∗
      A.pool ∗ stackAt s0.sp chainNewStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def ChainNewOkX (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainNewName)
    ((chainNewSpecX hkdf A).inImage img)

/-! ## Contract-Backed (`*Ext`) Specifications (`hkdfToSliceStackExt = 17616` B) -/

/-- Stack budget of `spqr::kdf::hkdf_to_slice` (`0x63284`) under contract-backed
`CliExt.compress256Spec` (`688 + 544 + extHookStack = 1232 + 16384 = 17616` B). -/
abbrev hkdfToSliceStackExt : Nat := 1232 + extHookStack

/-- Contract-backed SPQR V1 spec of `spqr::kdf::hkdf_to_slice` (`0x63284`) at
`hkdfToSliceStackExt` (`17616` B), requiring RW slices whenever `compress256` is invoked
directly (`salt.length > 64` or `ikm.length ≥ 64`). -/
def hkdfToSliceSpecExt (hkdf : HkdfFn) : Spec HkdfToSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
      s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
      s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
      s.readReg64 .x6 = x.okmA ∧ s.readReg64 .x7 = BitVec.ofNat 64 x.okmLen ∧
      x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
      32 ≤ x.info.length ∧ x.info.length < 55 ∧
      (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96) ∧
      (¬x.saltRO ∨ x.salt.length ≤ 64) ∧ (¬x.ikmRO ∨ x.ikm.length < 64)⌝ ∗
      bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      memRegion x.okmA x.okmLen ∗
      stackAt s.sp hkdfToSliceStackExt
  post := fun x s0 sf =>
    ⌜(hkdf x.salt x.ikm x.info x.okmLen).length = x.okmLen ∧ sf.trace = s0.trace⌝ ∗
      bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      (x.okmA ↦ₛ hkdf x.salt x.ikm x.info x.okmLen) ∗
      stackAt s0.sp hkdfToSliceStackExt

abbrev hkdfToSliceSpqrSpecExt (hkdf : HkdfFn) : Spec HkdfToSliceGhost :=
  hkdfToSliceSpecExt hkdf

def HkdfToSliceSpqrOkExt (img : Obj.Image) (hkdf : HkdfFn)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
    ((hkdfToSliceSpecExt hkdf).inImage img)

abbrev HkdfToSliceOkExt (img : Obj.Image) (hkdf : HkdfFn)
    (ext : String → Option (State → State)) : Prop :=
  HkdfToSliceSpqrOkExt img hkdf ext

/-- `<spqr::chain::ChainEpochDirection>::next_key_internal` frame (`176` B) + `hkdfToSliceStackExt` (`17616` B). -/
abbrev nextKeyInternalStackExt : Nat := 176 + hkdfToSliceStackExt

/-- Contract-backed spec of `<spqr::chain::ChainEpochDirection>::next_key_internal` at
`nextKeyInternalStackExt` (`17792` B). -/
def nextKeyInternalSpecExt (hkdf : HkdfFn) (A : RustAlloc) : Spec NextKeyInternalGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.nextA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = x.ctrA ∧
      x.next.length = 32 ∧ x.ctr ≠ 0xffffffff#32⌝ ∗
      memRegion x.out 36 ∗ (x.nextA ↦ₛ x.next) ∗ (x.ctrA ↦₃₂ x.ctr) ∗
      A.pool ∗ stackAt s.sp nextKeyInternalStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      nextKeyOutAt x.out (x.ctr + 1#32) (nextKeyOut hkdf x.next x.ctr) ∗
      (x.nextA ↦ₛ nextKeyNext hkdf x.next x.ctr) ∗
      (x.ctrA ↦₃₂ (x.ctr + 1#32)) ∗
      A.pool ∗ stackAt s0.sp nextKeyInternalStackExt
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def NextKeyInternalOkExt (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr nextKeyInternalName)
    ((nextKeyInternalSpecExt hkdf A).inImage img)

/-- `<spqr::chain::Chain>::new` frame (`224` B) + `hkdfToSliceStackExt` (`17616` B). -/
abbrev chainNewStackExt : Nat := 224 + hkdfToSliceStackExt

/-- Contract-backed spec of `<spqr::chain::Chain>::new` at `chainNewStackExt` (`17840` B). -/
def chainNewSpecExt (hkdf : HkdfFn) (A : RustAlloc) : Spec ChainNewGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.ikmA ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.initialKey.length ∧
      (s.readReg64 .x3).setWidth 32 = x.dir.toI32 ∧
      (s.readReg64 .x4).setWidth 32 = x.params.maxJump ∧
      (s.readReg64 .x5).setWidth 32 = x.params.maxOooKeys ∧
      x.initialKey.length < 2 ^ 63 ∧
      (¬x.ikmRO ∨ x.initialKey.length < 64)⌝ ∗
      memRegion x.out 88 ∗ bytesAt x.ikmRO x.ikmA x.initialKey ∗
      A.pool ∗ stackAt s.sp chainNewStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ G : ChainGhost,
        ⌜G.linksCap = 4#64 ∧ G.linksHead = 0#64⌝ ∗
        chainAt A x.out G (chainNewVal hkdf x.initialKey x.dir x.params)) ∗
      bytesAt x.ikmRO x.ikmA x.initialKey ∗
      A.pool ∗ stackAt s0.sp chainNewStackExt
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def ChainNewOkExt (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainNewName)
    ((chainNewSpecExt hkdf A).inImage img)

end CryptoVerification.SpqrV1.ChainProofs
