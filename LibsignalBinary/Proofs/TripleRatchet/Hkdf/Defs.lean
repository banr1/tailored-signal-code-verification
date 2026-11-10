/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hmac.Defs

/-!
# Specifications for `finalize_fixed`, `extract`, and `expand_multi_info`

Separation-logic contracts relating the compiled `Hmac<Sha256>::finalize_fixed`,
`GenericHkdf<Hmac<Sha256>>::extract`, and `GenericHkdf<Hmac<Sha256>>::expand_multi_info`
subroutines to `hmacWith`, `hkdfExtract`, and `hkdfExpand`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalHmac (shaStateBytes)

/-! ## Symbol names -/

abbrev finalizeFixedName : String :=
  "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]"

abbrev extractName : String :=
  "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract"

abbrev expandMultiInfoName : String :=
  "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info"

/-! ## Stack budgets (own frame + callee budget) -/

/-- `Hmac<Sha256>::finalize_fixed` frame (`0x30680`: `sub sp, sp, #0x90` = 144 B;
calls only 0-step hooks `memset` and `compress256`). -/
abbrev finalizeFixedStack : Nat := 144

/-- `GenericHkdf<Hmac<Sha256>>::extract` frame (`0x1ad38`: `sub sp, sp, #0x1b0` = 432 B) +
`newFromSliceStack` (544 B, `≥ finalizeFixedStack` = 144 B). -/
abbrev extractStack : Nat := 432 + newFromSliceStack

/-- `GenericHkdf<Hmac<Sha256>>::expand_multi_info` frame (`0x1a874`: `sub sp, sp, #0x1f0` = 496 B) +
`finalizeFixedStack` (144 B). -/
abbrev expandMultiInfoStack : Nat := 496 + finalizeFixedStack

/-! ## `Hmac<Sha256>::finalize_fixed` -/

/-- Ghost arguments of `<Hmac<Sha256> as FixedOutput>::finalize_fixed` (`0x30680`). -/
structure FinalizeFixedGhost where
  /-- 32-byte tag output buffer (`x0`; `+0x01c: mov x19, x0`, `+0x198..+0x1a0: stp q1, q0, [x19]`). -/
  out : BitVec 64
  /-- 144-byte (`0x90`-byte) `Hmac<Sha256>` buffer passed by value (`x1`; `+0x024: mov x20, x1`),
  mutated and zeroized in place (`+0x138..+0x14c`). -/
  hm : BitVec 64
  /-- HMAC key bytes (`|key| ≤ 64`). -/
  key : List (BitVec 8)
  /-- Absorbed message bytes (`|msg| < 56`, so `63 - |msg| > 7` takes the single-block padding
  branch `+0x050: b.hi +0x084`). -/
  msg : List (BitVec 8)

/-- Contract for `<Hmac<Sha256> as FixedOutput>::finalize_fixed` (`x0 = out`, `x1 = hm`)
for keys `|key| ≤ 64` and short messages `|msg| < 56`: pads and compresses the inner and
outer SHA-256 blocks, zeroizes the 144-byte `Hmac<Sha256>` buffer at `hm`, and writes
`hmacWith F key msg` to `[out, out + 32)`. -/
def finalizeFixedSpec (F : ShaCompress) : Spec FinalizeFixedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.hm ∧
      x.key.length ≤ 64 ∧ x.msg.length < 56⌝ ∗
      memRegion x.out 32 ∗ hmacCoreAt F x.hm x.key x.msg ∗
      stackAt s.sp finalizeFixedStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.out ↦ₛ hmacWith F x.key x.msg) ∗ memRegion x.hm 0x90 ∗
      stackAt s0.sp finalizeFixedStack

def FinalizeFixedOk (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr finalizeFixedName)
    (finalizeFixedSpec C.F)

def FinalizeFixedOk_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr finalizeFixedName)
    (finalizeFixedSpec C.F)

/-! ## `GenericHkdf<Hmac<Sha256>>::extract` -/

/-- Optional 32-byte salt slice for `GenericHkdf::extract` (`0x1ad38` `+0x02c..+0x03c:
cmp x1, #0; csel x1, x8, x1, eq; csel x2, x9, x2, eq`):
* `none`: either `saltA = 0#64` (`x1 = 0`, `x2` ignored; `extract` substitutes 32 zero bytes at
  `sp + 0x90`) or `s.readReg64 .x2 = 0#64` (`Some(&[])`, `new_from_slice` zero-pads the 0-byte key
  to 64 zero bytes, identical to 32 zero bytes);
* `some s`: `saltA ≠ 0#64` and `(saltA ↦ₛ s.toList)`. -/
def optSaltAt (saltA : BitVec 64) : Salt → SepProp
  | none => emp
  | some s => ⌜saltA ≠ 0#64⌝ ∗ (saltA ↦ₛ s.toList)

/-- Ghost arguments of `GenericHkdf<Hmac<Sha256>>::extract` (`0x1ad38`). -/
structure ExtractGhost where
  /-- Sret (`x0`, 176 = `0xb0` bytes: `(GenericArray<u8, 32>, GenericHkdf<Hmac<Sha256>>)`;
  `+0x028: mov x19, x0`). -/
  ret : BitVec 64
  /-- `salt: Option<&[u8]>` pointer (`x1`; `0` for `None`, non-null 32-byte slice pointer for
  `Some`). -/
  saltA : BitVec 64
  salt : Salt
  /-- `ikm: &[u8]` pointer (`x3`; `+0x044: mov x20, x3`) and 32-byte contents (`x4 = 32`;
  `+0x040: mov x21, x4`). -/
  ikmA : BitVec 64
  ikm : List (BitVec 8)

/-- The 32-byte pseudorandom key `prk = hkdfExtract F x.salt x.ikm` produced by `extract`. -/
abbrev ExtractGhost.prk (F : ShaCompress) (x : ExtractGhost) : List (BitVec 8) :=
  hkdfExtract F x.salt x.ikm

/-- Contract for `<GenericHkdf<Hmac<Sha256>>>::extract` (`x0 = ret`, optional 32-byte salt
`(x1, x2)`, 32-byte IKM `(x3, x4)`): computes `prk = hkdfExtract F x.salt x.ikm`, writes `prk`
at `ret..ret + 0x20`, and initializes `hmacCoreAt F (ret + 0x20) prk []` at `ret + 0x20..ret + 0xb0`. -/
def extractSpec (F : ShaCompress) : Spec ExtractGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.saltA ∧
      (x.salt.isSome → s.readReg64 .x2 = 32#64) ∧
      (x.salt = none → x.saltA = 0#64 ∨ s.readReg64 .x2 = 0#64) ∧
      s.readReg64 .x3 = x.ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      x.ikm.length = 32⌝ ∗
      memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      stackAt s.sp extractStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ret ↦ₛ x.prk F) ∗ hmacCoreAt F (x.ret + 0x20#64) (x.prk F) [] ∗
      optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      stackAt s0.sp extractStack

def ExtractOk (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr extractName)
    ((extractSpec C.F).inImage img)

def ExtractOk_trap (img : Obj.Image) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr extractName)
    ((extractSpec C.F).inImage img)

/-! ## `GenericHkdf<Hmac<Sha256>>::expand_multi_info` -/

/-- Ghost arguments of `GenericHkdf<Hmac<Sha256>>::expand_multi_info` (`0x1a874`). -/
structure ExpandMultiInfoGhost where
  /-- `&self: &GenericHkdf<Hmac<Sha256>>` (`x0`, 144 = `0x90` bytes; `+0x038: mov x22, x0`). -/
  hkdfA : BitVec 64
  /-- PRK key bytes (`|prk| ≤ 64`, 32 bytes in callers). -/
  prk : List (BitVec 8)
  /-- `info_components: &[&[u8]; 1]` pointer (`x1`; `+0x03c: ldp x25, x26, [x1]`; note that
  `info_components.len() == 1` was constant-propagated by rustc into this specialization). -/
  infoHdrA : BitVec 64
  /-- Single info slice pointer (`[infoHdrA]`) and bytes (`[infoHdrA + 8] = info.length < 23`;
  14 B `"WhisperRatchet"` in `create_chain`, 18 B `"WhisperMessageKeys"` in `generate_keys`). -/
  infoA : BitVec 64
  info : List (BitVec 8)
  /-- `okm: &mut [u8]` pointer (`x2`; `+0x034: mov x19, x2`) and length (`x3 = okmLen`;
  `+0x02c: mov x20, x3`; 64 B in `create_chain`, 80 B in `generate_keys`). -/
  okmA : BitVec 64
  okmLen : Nat

/-- Contract for `<GenericHkdf<Hmac<Sha256>>>::expand_multi_info` (`x0 = hkdfA`, 1-element
slice header `x1 = infoHdrA` with `|info| < 23`, output buffer `(x2, x3) = (okmA, okmLen)`
with `okmLen ∈ {64, 80}`): preserves `hmacCoreAt F hkdfA prk []` and the read-only `info`
slice, and writes `hkdfExpand F prk info okmLen` to `[okmA, okmA + okmLen)`. -/
def expandMultiInfoSpec (F : ShaCompress) : Spec ExpandMultiInfoGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.hkdfA ∧ s.readReg64 .x1 = x.infoHdrA ∧
      s.readReg64 .x2 = x.okmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.okmLen ∧
      x.prk.length ≤ 64 ∧ x.info.length < 23 ∧ (x.okmLen = 64 ∨ x.okmLen = 80)⌝ ∗
      hmacCoreAt F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA x.okmLen ∗
      stackAt s.sp expandMultiInfoStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      hmacCoreAt F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand F x.prk x.info x.okmLen) ∗
      stackAt s0.sp expandMultiInfoStack

def ExpandMultiInfoOk (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr expandMultiInfoName)
    (expandMultiInfoSpec C.F)

def ExpandMultiInfoOk_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr expandMultiInfoName)
    (expandMultiInfoSpec C.F)

end CryptoVerification.LibsignalTripleRatchet
