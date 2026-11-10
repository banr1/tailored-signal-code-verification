/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpers
public import LibsignalBinary.Proofs.SpqrV1.Chain.ChainPbCodeSym
import ProofLib.SepLogic.WPp -- shake: keep

/-!
# Helpers and Specifications for `<spqr::chain::Chain>::recv_key` (`0x608d0`, 312 instructions)

Output representation predicates (`recvKeyOkAt`, `recvKeyErrAt`, `recvKeyPostAt`) for the 32-byte
`Result<Vec<u8>, spqr::Error>` sret slot, target contracts `chainRecvKeySpecX` and
`chainRecvKeySpecExt`, magic-constant division by 36, and `KeyHistory` `Vec<u8>` pack/unpack lemmas.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open AgreeStateSimp NextKeyInternalFacts ChainNewFacts ChainAddEpochFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

abbrev chainRecvKeyName : String :=
  "<spqr::chain::Chain>::recv_key"

/-- `<spqr::chain::Chain>::recv_key` frame (`0x80 = 128` B) + `nextKeyInternalStackX` (`176 + extHookStack`). -/
abbrev chainRecvKeyStackX : Nat := 128 + nextKeyInternalStackX

/-! ## Output Layout for `Result<Vec<u8>, spqr::Error>` (32 Bytes, Align 8) -/

/-- `Ok(outKey)` in the 32-byte `Result<Vec<u8>, spqr::Error>` return slot at `out`:
* `+0x00..+0x08` (8B): `0#64` (`Ok` tag)
* `+0x08..+0x20` (24B): `vecU8 A (out + 0x08#64) outKey` -/
def recvKeyOkAt (A : RustAlloc) (out : BitVec 64) (outKey : Bytes) : SepProp :=
  (out ↦₆₄ 0#64) ∗ vecU8 A (out + 0x08#64) outKey

/-- `Err(err)` in the 32-byte `Result<Vec<u8>, spqr::Error>` return slot at `out`:
* `+0x00..+0x08` (8B): `1#64` (`Err` tag)
* `+0x08` (1B): `Error` discriminant (`4#8` for `EpochOutOfRange`, `9#8` for `KeyJump`,
  `10#8` for `KeyTrimmed`, `11#8` for `KeyAlreadyRequested`)
* Payload fields at `+0x0c` / `+0x10` and uninitialized padding in the remaining bytes of
  `[out + 0x08 .. out + 0x20)`. -/
def recvKeyErrAt (out : BitVec 64) : Error → SepProp
  | .epochOutOfRange epoch =>
    (out ↦₆₄ 1#64) ∗ ((out + 0x08#64) ↦₈ 4#8) ∗ memRegion (out + 0x09#64) 7 ∗
      ((out + 0x10#64) ↦₆₄ epoch) ∗ memRegion (out + 0x18#64) 8
  | .keyJump ctr atIdx =>
    (out ↦₆₄ 1#64) ∗ ((out + 0x08#64) ↦₈ 9#8) ∗ memRegion (out + 0x09#64) 3 ∗
      ((out + 0x0c#64) ↦₃₂ ctr) ∗ ((out + 0x10#64) ↦₃₂ atIdx) ∗ memRegion (out + 0x14#64) 12
  | .keyTrimmed atIdx =>
    (out ↦₆₄ 1#64) ∗ ((out + 0x08#64) ↦₈ 10#8) ∗ memRegion (out + 0x09#64) 3 ∗
      ((out + 0x0c#64) ↦₃₂ atIdx) ∗ memRegion (out + 0x10#64) 16
  | .keyAlreadyRequested atIdx =>
    (out ↦₆₄ 1#64) ∗ ((out + 0x08#64) ↦₈ 11#8) ∗ memRegion (out + 0x09#64) 3 ∗
      ((out + 0x0c#64) ↦₃₂ atIdx) ∗ memRegion (out + 0x10#64) 16
  | _ => ⌜False⌝

/-- Combined postcondition state at `(selfPtr, out)` for a non-panicking `Chain.recvKey` result. -/
def recvKeyPostAt (A : RustAlloc) (selfPtr out : BitVec 64) (self : Chain) :
    ChainResult (Chain × Bytes) → SepProp
  | .ok (self', outKey) =>
    recvKeyOkAt A out outKey ∗ chainRepr A selfPtr self'
  | .error (.err e) =>
    recvKeyErrAt out e ∗ chainRepr A selfPtr self
  | .error (.panic _) =>
    ⌜False⌝

theorem recvKeyOkAt_empty_intro (A : RustAlloc) (out : BitVec 64) :
    (out ↦₆₄ 0#64) ∗ ((out + 0x08#64) ↦₆₄ 0#64) ∗
      ((out + 0x10#64) ↦₆₄ 1#64) ∗ ((out + 0x18#64) ↦₆₄ 0#64) ⊢
      recvKeyOkAt A out [] := by
  unfold recvKeyOkAt vecU8
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right 0#64 ?_
  refine Entails.sepExists_right 1#64 ?_
  unfold vecU8At vecHeader
  simp (config := { decide := true }) only [List.length_nil, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, ↓reduceIte, pure_true,
    sepConj_emp, bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

theorem recvKeyOkAt_alloc_intro (A : RustAlloc) (out p_key : BitVec 64)
    (outKey : Bytes) (hp : p_key ≠ 0#64) (hlen : outKey.length = 32) :
    (out ↦₆₄ 0#64) ∗ ((out + 0x08#64) ↦₆₄ 32#64) ∗
      ((out + 0x10#64) ↦₆₄ p_key) ∗ ((out + 0x18#64) ↦₆₄ 32#64) ∗
      A.live p_key 32 1 ∗ (p_key ↦ₛ outKey) ⊢
      recvKeyOkAt A out outKey := by
  unfold recvKeyOkAt vecU8
  have hvec := ChainNewFacts.vecU8At_32_intro A (out + 0x08#64) p_key hlen hp
  have h16 : out + 0x08#64 + 8#64 = out + 0x10#64 := by bv_kernel
  have h24 : out + 0x08#64 + 16#64 = out + 0x18#64 := by bv_kernel
  rw [h16, h24] at hvec
  refine sepConj_mono_right ?_
  exact Entails.sepExists_right 32#64 (Entails.sepExists_right p_key hvec)

theorem recvKeyErrAt_epochOutOfRange_intro (out epoch : BitVec 64) :
    (out ↦₆₄ 1#64) ∗ ((out + 0x08#64) ↦₈ 4#8) ∗ memRegion (out + 0x09#64) 7 ∗
      ((out + 0x10#64) ↦₆₄ epoch) ∗ memRegion (out + 0x18#64) 8 ⊢
      recvKeyErrAt out (.epochOutOfRange epoch) := by
  unfold recvKeyErrAt; exact Entails.refl _

theorem recvKeyErrAt_keyJump_intro (out : BitVec 64) (ctr atIdx : BitVec 32) :
    (out ↦₆₄ 1#64) ∗ ((out + 0x08#64) ↦₈ 9#8) ∗ memRegion (out + 0x09#64) 3 ∗
      ((out + 0x0c#64) ↦₃₂ ctr) ∗ ((out + 0x10#64) ↦₃₂ atIdx) ∗ memRegion (out + 0x14#64) 12 ⊢
      recvKeyErrAt out (.keyJump ctr atIdx) := by
  unfold recvKeyErrAt; exact Entails.refl _

theorem recvKeyErrAt_keyTrimmed_intro (out : BitVec 64) (atIdx : BitVec 32) :
    (out ↦₆₄ 1#64) ∗ ((out + 0x08#64) ↦₈ 10#8) ∗ memRegion (out + 0x09#64) 3 ∗
      ((out + 0x0c#64) ↦₃₂ atIdx) ∗ memRegion (out + 0x10#64) 16 ⊢
      recvKeyErrAt out (.keyTrimmed atIdx) := by
  unfold recvKeyErrAt; exact Entails.refl _

theorem recvKeyErrAt_keyAlreadyRequested_intro (out : BitVec 64) (atIdx : BitVec 32) :
    (out ↦₆₄ 1#64) ∗ ((out + 0x08#64) ↦₈ 11#8) ∗ memRegion (out + 0x09#64) 3 ∗
      ((out + 0x0c#64) ↦₃₂ atIdx) ∗ memRegion (out + 0x10#64) 16 ⊢
      recvKeyErrAt out (.keyAlreadyRequested atIdx) := by
  unfold recvKeyErrAt; exact Entails.refl _

/-! ## Target Specification: `<spqr::chain::Chain>::recv_key` (`0x608d0`) -/

/-- Ghost arguments of `<spqr::chain::Chain>::recv_key` (`0x608d0`). -/
structure ChainRecvKeyGhost where
  /-- Sret pointer (`x0`, 32-byte `Result<Vec<u8>, spqr::Error>` output). -/
  out : BitVec 64
  /-- `self: &mut Chain` pointer (`x1`). -/
  selfPtr : BitVec 64
  /-- `epoch: Epoch` (`x2`). -/
  epoch : Epoch
  /-- `index: u32` (`w3`). -/
  index : BitVec 32
  /-- Initial `ChainGhost` pins of `*selfPtr`. -/
  G : ChainGhost
  /-- Initial `Chain` value at `*selfPtr`. -/
  self : Chain

/-- Bound on `link.recv.prev.data.length` ensuring that `KeyHistory::add`'s `Vec<u8>` reserve
(`do_reserve_and_handle [local#7]`, adding at most `(index - ctr) * 36 < 36 * 2^32` bytes across
`keyAdvanceLoop`) stays within `isize::MAX` (`< 2^63`).
Discharge source: `StateSizeStep.lean` / `StateSize.lean` (`rawChain self.intoPb < 2^61` from
`DEV-SPQR3` `state.length < 2^32`, or `Chain.new` / `Chain.addEpoch` where `prev.data = []`). -/
def RecvPrevFits (c : Chain) : Prop :=
  ∀ link ∈ c.links, link.recv.prev.data.length < 2 ^ 61

/-- Spec of `<spqr::chain::Chain>::recv_key` (`src/chain.rs:416–422`, image offset `0x608d0`,
312 instructions):
* Registers: `x0 = x.out`, `x1 = x.selfPtr`, `x2 = x.epoch`, `(x3).setWidth 32 = x.index`.
* Bound `RecvPrevFits x.self` (`∀ link ∈ x.self.links, link.recv.prev.data.length < 2 ^ 61`),
  discharged by `StateSize.lean` (`rawChain < 2^61` under `DEV-SPQR3` `state.length < 2^32`).
* Matches `Chain.recvKey hkdf x.self x.epoch x.index`:
  - Returns `Ok(outKey)` and updates `*selfPtr` to `self'` when `Chain.recvKey = .ok (self', outKey)`
    (or panics on OOM).
  - Returns `Err(err)` and leaves `*selfPtr` unchanged when `Chain.recvKey = .error (.err err)`.
  - Panics in Rust with `sf.trace = s0.trace` when `(Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true`. -/
def chainRecvKeySpecX (hkdf : HkdfFn) (A : RustAlloc) : Spec ChainRecvKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.selfPtr ∧
      s.readReg64 .x2 = x.epoch ∧ (s.readReg64 .x3).setWidth 32 = x.index ∧
      RecvPrevFits x.self⌝ ∗
      memRegion x.out 32 ∗
      chainAt A x.selfPtr x.G x.self ∗
      A.pool ∗ stackAt s.sp chainRecvKeyStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      recvKeyPostAt A x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
      A.pool ∗ stackAt s0.sp chainRecvKeyStackX
  onPanic := fun x s0 sf =>
    ⌜((Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap

def ChainRecvKeyOkX (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainRecvKeyName)
    ((chainRecvKeySpecX hkdf A).inImage img)

def ChainRecvKeyPlacedOkX [LibsignalPlacement] (hkdf : HkdfFn) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
    (blkPl_366).base
    (NextKeyInternalFacts.withLsCallInv lsmpl (chainRecvKeySpecX hkdf A))

/-! ## Pure Lemmas for `Chain.recvKey`, `ChainEpochDirection.key`, and `KeyHistory` -/

theorem recvKey_zero_zero (hkdf : HkdfFn) (self : Chain) :
    Chain.recvKey hkdf self 0#64 0#32 = .ok (self, []) := rfl

theorem recvKey_of_ne_zero (hkdf : HkdfFn) (self : Chain) (epoch : Epoch) (index : BitVec 32)
    (hne : ¬ (epoch = 0#64 ∧ index = 0#32)) :
    Chain.recvKey hkdf self epoch index = (do
      let epochIndex ← ChainResult.ofError (self.epochIdx epoch)
      match self.links[epochIndex]? with
      | none => .error (.panic .linksOutOfBounds)
      | some link => do
        let (recv', out) ← link.recv.key hkdf index self.params
        let links' := self.links.set epochIndex { link with recv := recv' }
        return ({ self with links := links' }, out)) := by
  unfold Chain.recvKey
  have hcond : (epoch == 0#64 && index == 0#32) = false := by
    rw [Bool.and_eq_false_iff]
    by_cases he : epoch = 0#64
    · right; rw [beq_eq_false_iff_ne]; exact fun hi => hne ⟨he, hi⟩
    · left; rw [beq_eq_false_iff_ne]; exact he
  simp only [hcond, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem recvKey_of_epochIdx_err (hkdf : HkdfFn) (self : Chain) (epoch : Epoch) (index : BitVec 32)
    (err : Error) (hne : ¬ (epoch = 0#64 ∧ index = 0#32))
    (herr : self.epochIdx epoch = .error err) :
    Chain.recvKey hkdf self epoch index = .error (.err err) := by
  rw [recvKey_of_ne_zero hkdf self epoch index hne, herr]
  rfl

theorem recvKey_of_epochIdx_ok (hkdf : HkdfFn) (self : Chain) (epoch : Epoch) (index : BitVec 32)
    (epochIndex : Nat) (link : ChainEpoch)
    (hne : ¬ (epoch = 0#64 ∧ index = 0#32))
    (hok : self.epochIdx epoch = .ok epochIndex)
    (hlink : self.links[epochIndex]? = some link) :
    Chain.recvKey hkdf self epoch index = (do
      let (recv', out) ← link.recv.key hkdf index self.params
      let links' := self.links.set epochIndex { link with recv := recv' }
      return ({ self with links := links' }, out)) := by
  rw [recvKey_of_ne_zero hkdf self epoch index hne, hok]
  simp only [ChainResult.ofError, bind, Except.bind, hlink]

theorem ced_key_of_lt (hkdf : HkdfFn) (ced : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) (hlt : atIdx < ced.ctr) :
    ced.key hkdf atIdx params = (do
      let (prev', out) ← ced.prev.get atIdx ced.ctr params
      return ({ ced with prev := prev' }, out)) := by
  unfold ChainEpochDirection.key
  simp only [hlt, ↓reduceIte]

theorem ced_key_of_eq (hkdf : HkdfFn) (ced : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) (heq : atIdx = ced.ctr) :
    ced.key hkdf atIdx params = .error (.err (.keyAlreadyRequested atIdx)) := by
  subst heq
  unfold ChainEpochDirection.key
  have hlt : ¬ (ced.ctr < ced.ctr) := BitVec.lt_irrefl ced.ctr
  simp only [hlt, beq_self_eq_true, ↓reduceIte]

theorem ced_key_of_gt_jump (hkdf : HkdfFn) (ced : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) (hgt : ced.ctr < atIdx)
    (hjump : atIdx - ced.ctr > params.maxJumpOrDefault) :
    ced.key hkdf atIdx params = .error (.err (.keyJump ced.ctr atIdx)) := by
  unfold ChainEpochDirection.key
  have hnot_lt : ¬ (atIdx < ced.ctr) := by
    rw [BitVec.lt_def] at hgt ⊢; omega
  have hne : (atIdx == ced.ctr) = false := by
    rw [beq_eq_false_iff_ne]; intro h; subst h; exact hnot_lt hgt
  simp only [hnot_lt, hne, Bool.false_eq_true, hjump, ↓reduceIte]

theorem ced_key_of_gt_overflow (hkdf : HkdfFn) (ced : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) (hgt : ced.ctr < atIdx)
    (hjump : ¬ (atIdx - ced.ctr > params.maxJumpOrDefault))
    (hovf : ced.ctr.toNat + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) :
    ced.key hkdf atIdx params = .error (.panic .ctrOverflow) := by
  unfold ChainEpochDirection.key
  have hnot_lt : ¬ (atIdx < ced.ctr) := by
    rw [BitVec.lt_def] at hgt ⊢; omega
  have hne : (atIdx == ced.ctr) = false := by
    rw [beq_eq_false_iff_ne]; intro h; subst h; exact hnot_lt hgt
  simp only [hnot_lt, hne, Bool.false_eq_true, hjump, hovf, ↓reduceIte]

theorem ced_key_of_gt_ok (hkdf : HkdfFn) (ced : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) (hgt : ced.ctr < atIdx)
    (hjump : ¬ (atIdx - ced.ctr > params.maxJumpOrDefault))
    (hno_ovf : ¬ (ced.ctr.toNat + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32)) :
    ced.key hkdf atIdx params = (do
      let maxOoo := params.maxOooKeysOrDefault
      let self0 :=
        if atIdx > ced.ctr + maxOoo then
          { ced with prev := ced.prev.clear }
        else
          ced
      let self1 ← ChainEpochDirection.keyAdvanceLoop hkdf self0 atIdx params
      let prevGc ← ChainResult.ofPanic (self1.prev.gc self1.ctr params)
      let self2 := { self1 with prev := prevGc }
      let (next', ctr', (_, outKey)) ←
        ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf self2.next self2.ctr)
      return ({ self2 with next := next', ctr := ctr' }, outKey)) := by
  unfold ChainEpochDirection.key
  have hnot_lt : ¬ (atIdx < ced.ctr) := by
    rw [BitVec.lt_def] at hgt ⊢; omega
  have hne : (atIdx == ced.ctr) = false := by
    rw [beq_eq_false_iff_ne]; intro h; subst h; exact hnot_lt hgt
  simp only [hnot_lt, hne, Bool.false_eq_true, hjump, hno_ovf, ↓reduceIte]

theorem keyHistory_get_unaligned (kh : KeyHistory) (atIdx ctr : BitVec 32) (params : ChainParamsPB)
    (h : kh.data.length % KeyHistory.KEY_SIZE ≠ 0) :
    kh.get atIdx ctr params = .error (.panic .keyHistoryUnaligned) := by
  unfold KeyHistory.get
  have hne : (kh.data.length % KeyHistory.KEY_SIZE != 0) = true := by simp [h]
  simp only [hne, ↓reduceIte]

theorem keyHistory_get_addOverflow (kh : KeyHistory) (atIdx ctr : BitVec 32) (params : ChainParamsPB)
    (halign : kh.data.length % KeyHistory.KEY_SIZE = 0)
    (hovf : atIdx.toNat + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) :
    kh.get atIdx ctr params = .error (.panic .keyHistoryAddOverflow) := by
  unfold KeyHistory.get
  have hne : (kh.data.length % KeyHistory.KEY_SIZE != 0) = false := by simp [halign]
  simp only [hne, Bool.false_eq_true, hovf, ↓reduceIte]

theorem keyHistory_get_trimmed (kh : KeyHistory) (atIdx ctr : BitVec 32) (params : ChainParamsPB)
    (halign : kh.data.length % KeyHistory.KEY_SIZE = 0)
    (hno_ovf : ¬ (atIdx.toNat + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32))
    (htrim : atIdx + params.maxOooKeysOrDefault < ctr) :
    kh.get atIdx ctr params = .error (.err (.keyTrimmed atIdx)) := by
  unfold KeyHistory.get
  have hne : (kh.data.length % KeyHistory.KEY_SIZE != 0) = false := by simp [halign]
  simp only [hne, Bool.false_eq_true, hno_ovf, htrim, ↓reduceIte]

theorem keyHistory_get_loop (kh : KeyHistory) (atIdx ctr : BitVec 32) (params : ChainParamsPB)
    (halign : kh.data.length % KeyHistory.KEY_SIZE = 0)
    (hno_ovf : ¬ (atIdx.toNat + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32))
    (hnot_trim : ¬ (atIdx + params.maxOooKeysOrDefault < ctr)) :
    kh.get atIdx ctr params = KeyHistory.getLoop kh atIdx (toBEBytes 4 atIdx) params 0 := by
  unfold KeyHistory.get
  have hne : (kh.data.length % KeyHistory.KEY_SIZE != 0) = false := by simp [halign]
  simp only [hne, Bool.false_eq_true, hno_ovf, hnot_trim, ↓reduceIte]

theorem getLoop_of_ge (kh : KeyHistory) (atIdx : BitVec 32) (want : Bytes) (params : ChainParamsPB)
    (i : Nat) (hge : ¬ (i < kh.data.length)) :
    KeyHistory.getLoop kh atIdx want params i = .error (.err (.keyAlreadyRequested atIdx)) := by
  rw [KeyHistory.getLoop.eq_def]
  simp only [hge, ↓reduceDIte]

theorem getLoop_of_hit (kh : KeyHistory) (atIdx : BitVec 32) (want : Bytes) (params : ChainParamsPB)
    (i : Nat) (hlt : i < kh.data.length) (hhit : ((kh.data.drop i).take 4 == want) = true) :
    KeyHistory.getLoop kh atIdx want params i =
      .ok (kh.remove i params, (kh.data.drop (i + 4)).take 32) := by
  rw [KeyHistory.getLoop.eq_def]
  simp only [hlt, ↓reduceDIte, hhit, ↓reduceIte]

theorem getLoop_of_miss (kh : KeyHistory) (atIdx : BitVec 32) (want : Bytes) (params : ChainParamsPB)
    (i : Nat) (hlt : i < kh.data.length) (hmiss : ((kh.data.drop i).take 4 == want) = false) :
    KeyHistory.getLoop kh atIdx want params i =
      KeyHistory.getLoop kh atIdx want params (i + KeyHistory.KEY_SIZE) := by
  rw [KeyHistory.getLoop.eq_def]
  simp only [hlt, ↓reduceDIte, hmiss, Bool.false_eq_true, ↓reduceIte]

theorem keyHistory_gc_of_lt (kh : KeyHistory) (ctr : BitVec 32) (params : ChainParamsPB)
    (hlt : ¬ (kh.data.length ≥ params.trimSize * KeyHistory.KEY_SIZE)) :
    kh.gc ctr params = .ok kh := by
  unfold KeyHistory.gc
  simp only [hlt, ↓reduceIte]

theorem keyHistory_gc_of_underflow (kh : KeyHistory) (ctr : BitVec 32) (params : ChainParamsPB)
    (hge : kh.data.length ≥ params.trimSize * KeyHistory.KEY_SIZE)
    (huf : ctr < params.maxOooKeysOrDefault) :
    kh.gc ctr params = .error .gcKeyUnderflow := by
  unfold KeyHistory.gc
  simp only [hge, huf, ↓reduceIte]

theorem keyHistory_gc_of_ok (kh : KeyHistory) (ctr : BitVec 32) (params : ChainParamsPB)
    (hge : kh.data.length ≥ params.trimSize * KeyHistory.KEY_SIZE)
    (hnuf : ¬ (ctr < params.maxOooKeysOrDefault)) :
    kh.gc ctr params =
      KeyHistory.gcLoop kh (toBEBytes 4 (ctr - params.maxOooKeysOrDefault)) params 0 := by
  unfold KeyHistory.gc
  simp only [hge, hnuf, ↓reduceIte]

theorem gcLoop_of_ge (kh : KeyHistory) (th : Bytes) (params : ChainParamsPB) (i : Nat)
    (hge : ¬ (i < kh.data.length)) :
    KeyHistory.gcLoop kh th params i = .ok kh := by
  rw [KeyHistory.gcLoop.eq_def]
  simp only [hge, ↓reduceDIte]

theorem gcLoop_of_bounds (kh : KeyHistory) (th : Bytes) (params : ChainParamsPB) (i : Nat)
    (hlt : i < kh.data.length) (hbounds : kh.data.length < i + 4) :
    KeyHistory.gcLoop kh th params i = .error .gcSliceBounds := by
  rw [KeyHistory.gcLoop.eq_def]
  simp only [hlt, ↓reduceDIte, hbounds, ↓reduceIte]

theorem gcLoop_of_remove (kh : KeyHistory) (th : Bytes) (params : ChainParamsPB) (i : Nat)
    (hlt : i < kh.data.length) (hbounds : ¬ (kh.data.length < i + 4))
    (hrem : bytesLt ((kh.data.drop i).take 4) th = true) :
    KeyHistory.gcLoop kh th params i = KeyHistory.gcLoop (kh.remove i params) th params i := by
  rw [KeyHistory.gcLoop.eq_def]
  simp only [hlt, ↓reduceDIte, hbounds, ↓reduceIte, hrem]

theorem gcLoop_of_skip (kh : KeyHistory) (th : Bytes) (params : ChainParamsPB) (i : Nat)
    (hlt : i < kh.data.length) (hbounds : ¬ (kh.data.length < i + 4))
    (hskip : bytesLt ((kh.data.drop i).take 4) th = false) :
    KeyHistory.gcLoop kh th params i =
      KeyHistory.gcLoop kh th params (i + KeyHistory.KEY_SIZE) := by
  rw [KeyHistory.gcLoop.eq_def]
  simp only [hlt, ↓reduceDIte, hbounds, ↓reduceIte, hskip, Bool.false_eq_true]

theorem keyAdvanceLoop_done (hkdf : HkdfFn) (ced : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) (hle : ¬ (ced.ctr.toNat + 1 < atIdx.toNat))
    (hctr : ced.ctr ≠ 0xffffffff#32) :
    ChainEpochDirection.keyAdvanceLoop hkdf ced atIdx params = .ok ced := by
  rw [ChainEpochDirection.keyAdvanceLoop.eq_def]
  have hne : (ced.ctr == 0xffffffff#32) = false := beq_eq_false_iff_ne.mpr hctr
  simp only [hle, ↓reduceDIte, hne, Bool.false_eq_true, ↓reduceIte]

theorem keyAdvanceLoop_step_err (hkdf : HkdfFn) (ced : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) (p : ChainPanic)
    (hlt : ced.ctr.toNat + 1 < atIdx.toNat)
    (herr : ChainEpochDirection.nextKeyInternal hkdf ced.next ced.ctr = .error p) :
    ChainEpochDirection.keyAdvanceLoop hkdf ced atIdx params = .error (.panic p) := by
  rw [ChainEpochDirection.keyAdvanceLoop.eq_def]
  simp only [hlt, ↓reduceDIte]
  split
  · rename_i p' heq
    rw [herr] at heq; injection heq with hp; subst hp; rfl
  · rename_i next' ctr' k heq
    rw [herr] at heq; contradiction

theorem keyAdvanceLoop_step_overflow (hkdf : HkdfFn) (ced : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) (next' : Bytes) (ctr' : BitVec 32) (k : BitVec 32 × Bytes)
    (hlt : ced.ctr.toNat + 1 < atIdx.toNat)
    (hok : ChainEpochDirection.nextKeyInternal hkdf ced.next ced.ctr = .ok (next', ctr', k))
    (hovf : ctr'.toNat + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) :
    ChainEpochDirection.keyAdvanceLoop hkdf ced atIdx params = .error (.panic .ctrOverflow) := by
  rw [ChainEpochDirection.keyAdvanceLoop.eq_def]
  simp only [hlt, ↓reduceDIte]
  split
  · rename_i p' heq
    rw [hok] at heq; contradiction
  · rename_i next1 ctr1 k1 heq
    rw [hok] at heq; injection heq with hprod
    injection hprod with h1 h2; injection h2 with h2 h3
    subst h1; subst h2; subst h3
    simp only [hovf, ↓reduceIte]

theorem keyAdvanceLoop_step_ok (hkdf : HkdfFn) (ced : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) (next' : Bytes) (ctr' : BitVec 32) (k : BitVec 32 × Bytes)
    (hlt : ced.ctr.toNat + 1 < atIdx.toNat)
    (hok : ChainEpochDirection.nextKeyInternal hkdf ced.next ced.ctr = .ok (next', ctr', k))
    (hno_ovf : ¬ (ctr'.toNat + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32)) :
    ChainEpochDirection.keyAdvanceLoop hkdf ced atIdx params =
      ChainEpochDirection.keyAdvanceLoop hkdf
        { ctr := ctr'
          next := next'
          prev :=
            if ctr' + params.maxOooKeysOrDefault ≥ atIdx then
              ced.prev.add k params
            else
              ced.prev }
        atIdx params := by
  rw [ChainEpochDirection.keyAdvanceLoop.eq_def]
  simp only [hlt, ↓reduceDIte]
  split
  · rename_i p' heq
    rw [hok] at heq; contradiction
  · rename_i next1 ctr1 k1 heq
    rw [hok] at heq; injection heq with hprod
    injection hprod with h1 h2; injection h2 with h2 h3
    subst h1; subst h2; subst h3
    simp only [hno_ovf, ↓reduceIte]

/-! ## Arithmetic, Magic-Division, and Big-Endian 4-Byte Lemmas -/

theorem maxJumpOrDefault_eq_ite (params : ChainParamsPB) :
    (if (params.maxJump == 0#32) = true then 25000#32 else params.maxJump) =
      params.maxJumpOrDefault := by
  unfold ChainParamsPB.maxJumpOrDefault DEFAULT_CHAIN_PARAMS
  by_cases h0 : params.maxJump = 0#32
  · simp [h0]
  · have hgt : 0#32 < params.maxJump := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat]
      have hne : params.maxJump.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
      omega
    have hbeq : (params.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr h0
    simp [hbeq, gt_iff_lt, hgt]

theorem maxOooKeysOrDefault_eq_ite (params : ChainParamsPB) :
    (if (params.maxOooKeys == 0#32) = true then 2000#32 else params.maxOooKeys) =
      params.maxOooKeysOrDefault := by
  unfold ChainParamsPB.maxOooKeysOrDefault DEFAULT_CHAIN_PARAMS
  by_cases h0 : params.maxOooKeys = 0#32
  · simp [h0]
  · have hgt : 0#32 < params.maxOooKeys := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat]
      have hne : params.maxOooKeys.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
      omega
    have hbeq : (params.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr h0
    simp [hbeq, gt_iff_lt, hgt]

/-- LLVM magic-number division by 36 (`0x609e4..0x60a08`):
`(umulh(x, 0xe38e38e38e38e38f) >>> 5).toNat = x.toNat / 36` for all `x : BitVec 64`. -/
theorem umulh_div36_toNat (x : BitVec 64) :
    ((BitVec.truncate 64
      ((BitVec.zeroExtend 128 x * BitVec.zeroExtend 128 0xe38e38e38e38e38f#64) >>> 64)) >>> 5).toNat =
      x.toNat / 36 := by
  have hx : x.toNat < 2 ^ 64 := x.isLt
  have hm : (BitVec.zeroExtend 128 0xe38e38e38e38e38f#64).toNat = 16397105843297379215 := rfl
  have hx128 : (BitVec.zeroExtend 128 x).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_mul, hx128, hm,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem mul36_div36_eq (x : BitVec 64) :
    let q := (BitVec.truncate 64
      ((BitVec.zeroExtend 128 x * BitVec.zeroExtend 128 0xe38e38e38e38e38f#64) >>> 64)) >>> 5
    (q + (q <<< 3)) <<< 2 = BitVec.ofNat 64 (x.toNat / 36 * 36) := by
  intro q
  have hq : q.toNat = x.toNat / 36 := umulh_div36_toNat x
  have hx : x.toNat < 2 ^ 64 := x.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, BitVec.toNat_ofNat, hq]
  omega

theorem sub_mul36_div36_eq (x : BitVec 64) :
    let q := (BitVec.truncate 64
      ((BitVec.zeroExtend 128 x * BitVec.zeroExtend 128 0xe38e38e38e38e38f#64) >>> 64)) >>> 5
    x - ((q + (q <<< 3)) <<< 2) = BitVec.ofNat 64 (x.toNat % 36) := by
  intro q
  rw [mul36_div36_eq x]
  have hx : x.toNat < 2 ^ 64 := x.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [BitVec.le_def, BitVec.toNat_ofNat]
    omega

/-- LLVM magic-number calculation of `params.trimSize * 36` (`0x60b38..0x60b58`). -/
theorem trimSize_mul36_eq (params : ChainParamsPB) :
    let maxOoo64 : BitVec 64 := params.maxOooKeysOrDefault.zeroExtend 64
    let prod11 : BitVec 64 := maxOoo64 * 11#64
    let div10 : BitVec 64 :=
      BitVec.truncate 64 ((BitVec.zeroExtend 128 prod11 * BitVec.zeroExtend 128 0x199999999999999a#64) >>> 64)
    36#64 + div10 * 36#64 = BitVec.ofNat 64 (params.trimSize * KeyHistory.KEY_SIZE) := by
  intro maxOoo64 prod11 div10
  have hm : params.maxOooKeysOrDefault.toNat < 2 ^ 32 := params.maxOooKeysOrDefault.isLt
  have hprod : prod11.toNat = params.maxOooKeysOrDefault.toNat * 11 := by
    dsimp only [prod11, maxOoo64]
    rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hc : (BitVec.zeroExtend 128 0x199999999999999a#64).toNat = 1844674407370955162 := rfl
  have hp128 : (BitVec.zeroExtend 128 prod11).toNat = params.maxOooKeysOrDefault.toNat * 11 := by
    rw [BitVec.toNat_setWidth, hprod, Nat.mod_eq_of_lt (by omega)]
  have hdiv : div10.toNat = params.maxOooKeysOrDefault.toNat * 11 / 10 := by
    dsimp only [div10]
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, hp128, hc,
      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
    omega
  apply BitVec.eq_of_toNat_eq
  unfold ChainParamsPB.trimSize KeyHistory.KEY_SIZE
  dsimp only
  rw [BitVec.toNat_add, BitVec.toNat_mul, hdiv, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- 32-bit byte swap (`rev w_dst, w_src`). -/
abbrev rev32Trunc (w : BitVec 32) : BitVec 32 :=
  BitVec.truncate 32 (rev32_64 (w.zeroExtend 64))

/-- Pack a 4-byte list in little-endian order into a `BitVec 32`. -/
def pack32LE (bs : List (BitVec 8)) : BitVec 32 :=
  match bs with
  | [b0, b1, b2, b3] => b3 ++ b2 ++ b1 ++ b0
  | _ => 0#32

theorem unpack32_pack32LE {bs : List (BitVec 8)} (h : bs.length = 4) :
    unpack32 (pack32LE bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at h; done)
  exact unpack32_pack32 b0 b1 b2 b3

theorem pointsToBytes4_eq_pointsTo32_pack32LE (a : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 4) :
    (a ↦ₛ bs) = (a ↦₃₂ pack32LE bs) := by
  rw [pointsTo32_eq_pointsToBytes, unpack32_pack32LE h]

theorem pack32LE_unpack32 (w : BitVec 32) :
    pack32LE (unpack32 w) = w := by
  unfold unpack32 pack32LE
  bv_bits

theorem unpack32_inj {w1 w2 : BitVec 32} :
    (unpack32 w1 == unpack32 w2) = (w1 == w2) := by
  by_cases h : w1 = w2
  · subst h; simp
  · have hne : unpack32 w1 ≠ unpack32 w2 := by
      intro heq; apply h
      rw [← pack32LE_unpack32 w1, ← pack32LE_unpack32 w2, heq]
    simp [h, hne]

theorem pack32LE_beq_rev32Trunc_iff {bs : List (BitVec 8)} (h : bs.length = 4) (v : BitVec 32) :
    (pack32LE bs == rev32Trunc v) = (bs == toBEBytes 4 v) := by
  rw [← unpack32_inj, unpack32_pack32LE h, NextKeyInternalFacts.unpack32_rev32_eq_toBEBytes]

theorem rev32Trunc_eq (w : BitVec 32) :
    rev32Trunc w =
      w.extractLsb' 0 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 24 8 := by
  simp only [rev32Trunc, rev32_64]; bv_bits

theorem rev32Trunc_pack32 (b0 b1 b2 b3 : BitVec 8) :
    rev32Trunc (b3 ++ b2 ++ b1 ++ b0) = b0 ++ b1 ++ b2 ++ b3 := by
  have h := unpack32_pack32 b0 b1 b2 b3
  unfold unpack32 at h
  simp only [List.cons.injEq] at h
  rw [rev32Trunc_eq, h.1, h.2.1, h.2.2.1, h.2.2.2.1]

theorem rev32Trunc_involutive (w : BitVec 32) :
    rev32Trunc (rev32Trunc w) = w := by
  conv_lhs => arg 1; rw [rev32Trunc_eq]
  rw [rev32Trunc_pack32]
  exact pack32LE_unpack32 w

private theorem append4_toNat (b0 b1 b2 b3 : BitVec 8) :
    (b0 ++ b1 ++ b2 ++ b3).toNat =
      b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat := by
  let w : BitVec 32 := b0 ++ b1 ++ b2 ++ b3
  have hw : w.toNat < 4294967296 := w.isLt
  have hu : unpack32 w = [b3, b2, b1, b0] := unpack32_pack32 b3 b2 b1 b0
  unfold unpack32 at hu
  simp only [List.cons.injEq, and_true] at hu
  rcases hu with ⟨h3, h2, h1, h0⟩
  have hb3 := congrArg BitVec.toNat h3
  have hb2 := congrArg BitVec.toNat h2
  have hb1 := congrArg BitVec.toNat h1
  have hb0 := congrArg BitVec.toNat h0
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at hb3 hb2 hb1 hb0
  change w.toNat = _
  omega

/-- Comparing `rev32Trunc` of two 4-byte LE words in unsigned 32-bit arithmetic matches
lexicographical `bytesLt` on the 4-byte slices (`KeyHistory::gc`, `0x60c8c..0x60c98`). -/
theorem bytesLt_4_eq_ult_rev32Trunc {ek : List (BitVec 8)} (hek : ek.length = 4)
    (thVal : BitVec 32) :
    bytesLt ek (toBEBytes 4 thVal) =
      (rev32Trunc (pack32LE ek)).ult (rev32Trunc (rev32Trunc thVal)) := by
  rcases ek with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | _⟩⟩⟩⟩ <;> try (simp at hek; done)
  rw [rev32Trunc_involutive]
  have hth := NextKeyInternalFacts.unpack32_rev32_eq_toBEBytes thVal
  have hth_pack : pack32LE (toBEBytes 4 thVal) = rev32Trunc thVal := by
    rw [← hth, pack32LE_unpack32]
  rcases hbe : toBEBytes 4 thVal with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩
  · have := NextKeyInternalFacts.toBEBytes_4_length thVal; simp [hbe] at this
  · have := NextKeyInternalFacts.toBEBytes_4_length thVal; simp [hbe] at this
  · have := NextKeyInternalFacts.toBEBytes_4_length thVal; simp [hbe] at this
  · have := NextKeyInternalFacts.toBEBytes_4_length thVal; simp [hbe] at this
  · rw [hbe] at hth_pack
    have hth_val : thVal = b0 ++ b1 ++ b2 ++ b3 := by
      rw [← rev32Trunc_involutive thVal, ← hth_pack]
      exact rev32Trunc_pack32 b0 b1 b2 b3
    dsimp only [pack32LE]
    rw [rev32Trunc_pack32, hth_val]
    dsimp only [bytesLt]
    have ha0 := a0.isLt; have ha1 := a1.isLt; have ha2 := a2.isLt; have ha3 := a3.isLt
    have hb0 := b0.isLt; have hb1 := b1.isLt; have hb2 := b2.isLt; have hb3 := b3.isLt
    have hult := append4_toNat a0 a1 a2 a3
    have hult' := append4_toNat b0 b1 b2 b3
    rw [BitVec.ult_eq_decide, eq_comm]
    by_cases h0 : a0 < b0
    · simp only [h0, ↓reduceIte]; rw [decide_eq_true_eq]; rw [BitVec.lt_def] at h0; omega
    · simp only [h0, ↓reduceIte]
      by_cases h0' : b0 < a0
      · simp only [h0', ↓reduceIte]; rw [decide_eq_false_iff_not]; rw [BitVec.lt_def] at h0'; omega
      · have he0 : a0.toNat = b0.toNat := by rw [BitVec.lt_def] at h0 h0'; omega
        simp only [h0', ↓reduceIte]
        by_cases h1 : a1 < b1
        · simp only [h1, ↓reduceIte]; rw [decide_eq_true_eq]; rw [BitVec.lt_def] at h1; omega
        · simp only [h1, ↓reduceIte]
          by_cases h1' : b1 < a1
          · simp only [h1', ↓reduceIte]; rw [decide_eq_false_iff_not]; rw [BitVec.lt_def] at h1'; omega
          · have he1 : a1.toNat = b1.toNat := by rw [BitVec.lt_def] at h1 h1'; omega
            simp only [h1', ↓reduceIte]
            by_cases h2 : a2 < b2
            · simp only [h2, ↓reduceIte]; rw [decide_eq_true_eq]; rw [BitVec.lt_def] at h2; omega
            · simp only [h2, ↓reduceIte]
              by_cases h2' : b2 < a2
              · simp only [h2', ↓reduceIte]; rw [decide_eq_false_iff_not]; rw [BitVec.lt_def] at h2'; omega
              · have he2 : a2.toNat = b2.toNat := by rw [BitVec.lt_def] at h2 h2'; omega
                simp only [h2', ↓reduceIte]
                by_cases h3 : a3 < b3
                · simp only [h3, ↓reduceIte]; rw [decide_eq_true_eq]; rw [BitVec.lt_def] at h3; omega
                · simp only [h3, ↓reduceIte]
                  by_cases h3' : b3 < a3
                  · simp only [h3', ↓reduceIte]; rw [decide_eq_false_iff_not]; rw [BitVec.lt_def] at h3'; omega
                  · simp only [h3', ↓reduceIte]; rw [decide_eq_false_iff_not]; rw [BitVec.lt_def] at h3 h3'; omega
  · have := NextKeyInternalFacts.toBEBytes_4_length thVal; simp [hbe] at this

/-! ## List and Separation-Logic Helpers for `KeyHistory.add` and `KeyHistory.remove` -/

theorem remove_data_eq_of_lt (bs : Bytes) (i : Nat) (params : ChainParamsPB)
    (hlt : i + KeyHistory.KEY_SIZE < bs.length) :
    let newEnd := bs.length - KeyHistory.KEY_SIZE
    let moved := bs.drop newEnd
    (bs.take i ++ moved ++ bs.drop (i + KeyHistory.KEY_SIZE)).take newEnd =
      (KeyHistory.remove ⟨bs⟩ i params).data := by
  intro newEnd moved
  unfold KeyHistory.remove
  simp only [hlt, ↓reduceIte]
  change (bs.take i ++ moved ++ bs.drop (i + KeyHistory.KEY_SIZE)).take newEnd =
    (bs.take i ++ moved ++ (bs.take newEnd).drop (i + KeyHistory.KEY_SIZE)).take newEnd
  have hlenA : (bs.take i ++ moved).length = i + KeyHistory.KEY_SIZE := by
    dsimp [moved, newEnd, KeyHistory.KEY_SIZE] at hlt ⊢
    rw [List.length_append, List.length_take, List.length_drop]
    omega
  rw [List.take_append (l₁ := bs.take i ++ moved),
    List.take_append (l₁ := bs.take i ++ moved), hlenA]
  congr 1
  by_cases hle : i + KeyHistory.KEY_SIZE ≤ newEnd
  · have hadd : i + KeyHistory.KEY_SIZE + (newEnd - (i + KeyHistory.KEY_SIZE)) = newEnd := by omega
    rw [List.take_drop, List.take_drop, hadd, List.take_take, Nat.min_self]
  · have h0 : newEnd - (i + KeyHistory.KEY_SIZE) = 0 := by omega
    rw [h0, List.take_zero, List.take_zero]

theorem remove_data_eq_of_ge (bs : Bytes) (i : Nat) (params : ChainParamsPB)
    (hge : ¬ (i + KeyHistory.KEY_SIZE < bs.length)) :
    bs.take i = (KeyHistory.remove ⟨bs⟩ i params).data := by
  unfold KeyHistory.remove
  simp only [hge, ↓reduceIte]

/-- Unpack `vecU8At A a cap ptr bs` when `bs.length + 4 ≤ cap.toNat` so a 4-byte `str w` at
`ptr + bs.length` can be stepped directly. -/
theorem vecU8At_unpack_for_u32 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : Bytes)
    (hadd4 : bs.length + 4 ≤ cap.toNat) :
    vecU8At A a cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      (∃∗ w0 : BitVec 32, ((ptr + BitVec.ofNat 64 bs.length) ↦₃₂ w0)) ∗
      memRegion (ptr + BitVec.ofNat 64 (bs.length + 4)) (cap.toNat - (bs.length + 4)) := by
  refine Entails.trans (vecU8At_unpack A a cap ptr bs) ?_
  refine Entails.pure_left fun ⟨hle, hcap, hptr⟩ => ?_
  refine Entails.pure_right ⟨hle, hcap, hptr⟩ ?_
  unfold vecU8Rest
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; simp at hadd4
  simp only [hcap_ne, ↓reduceIte]
  rw [ProofLib.memRegion_split' (b := ptr + BitVec.ofNat 64 bs.length)
      (N := cap.toNat - bs.length) (n := 4)
      (k := cap.toNat - (bs.length + 4)) (b' := ptr + BitVec.ofNat 64 (bs.length + 4))
      (by omega) (by bv_omega) (by omega),
    ProofLib.memRegion_four (ptr + BitVec.ofNat 64 bs.length)]
  rw [show (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ (A.live ptr cap.toNat 1 ∗
          ((∃∗ v : BitVec 32, (ptr + BitVec.ofNat 64 bs.length) ↦₃₂ v) ∗
            memRegion (ptr + BitVec.ofNat 64 (bs.length + 4)) (cap.toNat - (bs.length + 4)))) =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        (∃∗ w0 : BitVec 32, (ptr + BitVec.ofNat 64 bs.length) ↦₃₂ w0) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 4)) (cap.toNat - (bs.length + 4)) by ac_rfl]
  exact Entails.refl _

/-- Fold `vecU8At` after appending `toBEBytes 4 ctr'` (`str w11, [ptr, len]; str (len + 4), [a + 16]`). -/
theorem vecU8At_pack_append_u32_be (A : RustAlloc) (a cap ptr : BitVec 64) (bs : Bytes)
    (ctr' : BitVec 32) (hadd4 : bs.length + 4 ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length + 4)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦₃₂ rev32Trunc ctr') ∗
      memRegion (ptr + BitVec.ofNat 64 (bs.length + 4)) (cap.toNat - (bs.length + 4)) ⊢
      vecU8At A a cap ptr (bs ++ toBEBytes 4 ctr') := by
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; simp at hadd4
  have hlen4 : (bs ++ toBEBytes 4 ctr').length = bs.length + 4 := by
    rw [List.length_append, NextKeyInternalFacts.toBEBytes_4_length]
  rw [NextKeyInternalFacts.pointsTo32_rev32_eq_toBEBytes]
  have hjoin :
      (ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ toBEBytes 4 ctr') =
        (ptr ↦ₛ (bs ++ toBEBytes 4 ctr')) :=
    (pointsToBytes_append ptr bs (toBEBytes 4 ctr')).symm
  unfold vecU8At vecHeader
  simp only [hcap_ne, ↓reduceIte, hlen4]
  rw [show (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length + 4)) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ toBEBytes 4 ctr') ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 4)) (cap.toNat - (bs.length + 4)) =
      ((ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ toBEBytes 4 ctr')) ∗
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
         ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length + 4)) ∗
         A.live ptr cap.toNat 1 ∗
         memRegion (ptr + BitVec.ofNat 64 (bs.length + 4)) (cap.toNat - (bs.length + 4))) by ac_rfl,
    hjoin]
  rw [show ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length + 4))) ∗
      ⌜bs.length + 4 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ (bs ++ toBEBytes 4 ctr')) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 4)) (cap.toNat - (bs.length + 4))) =
    ⌜bs.length + 4 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((ptr ↦ₛ (bs ++ toBEBytes 4 ctr')) ∗
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
         ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length + 4)) ∗
         A.live ptr cap.toNat 1 ∗
         memRegion (ptr + BitVec.ofNat 64 (bs.length + 4)) (cap.toNat - (bs.length + 4)))) by ac_rfl]
  exact Entails.pure_right ⟨hadd4, hcap, hptr⟩ (Entails.refl _)

private theorem memRegion_32_cells4 (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ u0 : BitVec 64, p ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (p + 8#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (p + 16#64) ↦₆₄ u2) ∗
      (∃∗ u3 : BitVec 64, (p + 24#64) ↦₆₄ u3) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 24) (b' := p + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 16) (b' := p + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := p + 16#64) (n := 8) (k := 8) (b' := p + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight p,
    ProofLib.memRegion_eight (p + 8#64),
    ProofLib.memRegion_eight (p + 16#64),
    ProofLib.memRegion_eight (p + 24#64)]

/-- Unpack `vecU8At A a cap ptr bs` when `bs.length + 32 ≤ cap.toNat` so two 16-byte `str q0`
stores at `ptr + bs.length` and `ptr + bs.length + 16` can be stepped directly on four 64-bit cells. -/
theorem vecU8At_unpack_for_key32 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : Bytes)
    (hadd32 : bs.length + 32 ≤ cap.toNat) :
    vecU8At A a cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      (∃∗ u0 : BitVec 64, (ptr + BitVec.ofNat 64 bs.length) ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ u2) ∗
      (∃∗ u3 : BitVec 64, (ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ u3) ∗
      memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32)) := by
  refine Entails.trans (vecU8At_unpack A a cap ptr bs) ?_
  refine Entails.pure_left fun ⟨hle, hcap, hptr⟩ => ?_
  refine Entails.pure_right ⟨hle, hcap, hptr⟩ ?_
  unfold vecU8Rest
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; simp at hadd32
  simp only [hcap_ne, ↓reduceIte]
  rw [ProofLib.memRegion_split' (b := ptr + BitVec.ofNat 64 bs.length)
      (N := cap.toNat - bs.length) (n := 32)
      (k := cap.toNat - (bs.length + 32)) (b' := ptr + BitVec.ofNat 64 (bs.length + 32))
      (by omega) (by bv_omega) (by omega),
    memRegion_32_cells4 (ptr + BitVec.ofNat 64 bs.length)]
  rw [show (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ (A.live ptr cap.toNat 1 ∗
          (((∃∗ u0 : BitVec 64, (ptr + BitVec.ofNat 64 bs.length) ↦₆₄ u0) ∗
            (∃∗ u1 : BitVec 64, (ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ u1) ∗
            (∃∗ u2 : BitVec 64, (ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ u2) ∗
            (∃∗ u3 : BitVec 64, (ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ u3)) ∗
            memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32)))) =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        (∃∗ u0 : BitVec 64, (ptr + BitVec.ofNat 64 bs.length) ↦₆₄ u0) ∗
        (∃∗ u1 : BitVec 64, (ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ u1) ∗
        (∃∗ u2 : BitVec 64, (ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ u2) ∗
        (∃∗ u3 : BitVec 64, (ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ u3) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32)) by ac_rfl]
  exact Entails.refl _

/-- Fold `vecU8At` after storing `k0, k1, k2, k3` (`key`, `key.length = 32`) at
`ptr + bs.length` and updating `[a + 16]` to `bs.length + 32`. -/
theorem vecU8At_pack_append_key32 (A : RustAlloc) (a cap ptr : BitVec 64) (bs key : Bytes)
    (k0 k1 k2 k3 : BitVec 64) (hkey_len : key.length = 32)
    (hkey_pack : ∀ p : BitVec 64,
      (p ↦ₛ key) = (p ↦₆₄ k0) ∗ ((p + 8#64) ↦₆₄ k1) ∗ ((p + 16#64) ↦₆₄ k2) ∗ ((p + 24#64) ↦₆₄ k3))
    (hadd32 : bs.length + 32 ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length + 32)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ k0) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ k1) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ k2) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ k3) ∗
      memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32)) ⊢
      vecU8At A a cap ptr (bs ++ key) := by
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; simp at hadd32
  have hlen32 : (bs ++ key).length = bs.length + 32 := by
    rw [List.length_append, hkey_len]
  have hq := (hkey_pack (ptr + BitVec.ofNat 64 bs.length)).symm
  have hjoin :
      (ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ key) = (ptr ↦ₛ (bs ++ key)) :=
    (pointsToBytes_append ptr bs key).symm
  unfold vecU8At vecHeader
  simp only [hcap_ne, ↓reduceIte, hlen32]
  rw [show (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length + 32)) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        ((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ k0) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ k1) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ k2) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ k3) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32)) =
      (ptr ↦ₛ bs) ∗ (((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ k0) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ k1) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ k2) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ k3)) ∗
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
         ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length + 32)) ∗
         A.live ptr cap.toNat 1 ∗
         memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32))) by ac_rfl,
    hq, ← sepConj_assoc, hjoin]
  rw [show ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length + 32))) ∗
      ⌜bs.length + 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ (bs ++ key)) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32))) =
    ⌜bs.length + 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((ptr ↦ₛ (bs ++ key)) ∗
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
         ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length + 32)) ∗
         A.live ptr cap.toNat 1 ∗
         memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32)))) by ac_rfl]
  exact Entails.pure_right ⟨hadd32, hcap, hptr⟩ (Entails.refl _)

/-- Fold `vecU8At` after `KeyHistory::remove` truncates the last entry (`¬ (i + 36 < bs.length)`). -/
theorem vecU8At_pack_remove_last (A : RustAlloc) (a cap ptr : BitVec 64) (bs : Bytes)
    (i : Nat) (params : ChainParamsPB) (hi : i < bs.length)
    (hge : ¬ (i + KeyHistory.KEY_SIZE < bs.length))
    (hle : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 i) ∗
      (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs.length ⊢
      vecU8At A a cap ptr (KeyHistory.remove ⟨bs⟩ i params).data := by
  rw [← remove_data_eq_of_ge bs i params hge]
  have htake_len : (bs.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi)
  have hcap_pos : 0 < cap.toNat := by omega
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; simp at hcap_pos
  unfold vecU8At vecHeader vecU8Rest
  simp only [hcap_ne, ↓reduceIte, htake_len]
  have hbytes_split :
      (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
        (ptr ↦ₛ bs.take i) ∗ memRegion (ptr + BitVec.ofNat 64 i) (cap.toNat - i) := by
    have hbs_eq : (ptr ↦ₛ bs) =
        (ptr ↦ₛ bs.take i) ∗ ((ptr + BitVec.ofNat 64 i) ↦ₛ bs.drop i) := by
      conv_lhs => rw [(List.take_append_drop i bs).symm]
      rw [pointsToBytes_append, htake_len]
    rw [hbs_eq,
      ProofLib.memRegion_split' (b := ptr + BitVec.ofNat 64 i) (n := bs.length - i)
        (k := cap.toNat - bs.length) (b' := ptr + BitVec.ofNat 64 bs.length)
        (by omega) (by bv_omega) (by omega),
      sepConj_assoc]
    refine sepConj_mono_right ?_
    have hdrop_len : (bs.drop i).length = bs.length - i := List.length_drop
    rw [← hdrop_len]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion _ _)
  rw [show (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 i) ∗
        (ptr ↦ₛ bs) ∗ (A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         A.live ptr cap.toNat 1) by ac_rfl]
  refine Entails.trans (sepConj_mono_left hbytes_split) ?_
  rw [show (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 i)) ∗
        ⌜i ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs.take i) ∗
          memRegion (ptr + BitVec.ofNat 64 i) (cap.toNat - i))) =
      ⌜i ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((ptr ↦ₛ bs.take i) ∗ memRegion (ptr + BitVec.ofNat 64 i) (cap.toNat - i)) ∗
         ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 i) ∗
          A.live ptr cap.toNat 1)) by ac_rfl]
  exact Entails.pure_right ⟨by omega, hcap, hptr⟩ (Entails.refl _)

/-- Fold `vecU8At` after `KeyHistory::remove` swap-copies the last 36 bytes into offset `i`
(`i + 36 < bs.length`) and updates `[a + 16]` to `bs.length - 36`. -/
theorem vecU8At_pack_remove_swap (A : RustAlloc) (a cap ptr : BitVec 64) (bs : Bytes)
    (i : Nat) (params : ChainParamsPB)
    (hlt : i + KeyHistory.KEY_SIZE < bs.length)
    (hle : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    let newEnd := bs.length - KeyHistory.KEY_SIZE
    let moved := bs.drop newEnd
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 newEnd) ∗
      (ptr ↦ₛ (bs.take i ++ moved ++ bs.drop (i + KeyHistory.KEY_SIZE))) ∗
      vecU8Rest A cap ptr bs.length ⊢
      vecU8At A a cap ptr (KeyHistory.remove ⟨bs⟩ i params).data := by
  intro newEnd moved
  rw [← remove_data_eq_of_lt bs i params hlt]
  let L := bs.take i ++ moved ++ bs.drop (i + KeyHistory.KEY_SIZE)
  change (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 newEnd) ∗
      (ptr ↦ₛ L) ∗ vecU8Rest A cap ptr bs.length ⊢
      vecU8At A a cap ptr (L.take newEnd)
  have hL_len : L.length = bs.length := by
    dsimp [L, moved, newEnd, KeyHistory.KEY_SIZE] at hlt ⊢
    rw [List.length_append, List.length_append, List.length_take, List.length_drop, List.length_drop]
    omega
  have hnew_le : newEnd ≤ L.length := by dsimp [newEnd]; omega
  have htake_len : (L.take newEnd).length = newEnd := List.length_take_of_le hnew_le
  have hcap_pos : 0 < cap.toNat := by dsimp [KeyHistory.KEY_SIZE] at hlt; omega
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; simp at hcap_pos
  unfold vecU8At vecHeader vecU8Rest
  simp only [hcap_ne, ↓reduceIte, htake_len]
  have hbytes_split :
      (ptr ↦ₛ L) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
        (ptr ↦ₛ L.take newEnd) ∗ memRegion (ptr + BitVec.ofNat 64 newEnd) (cap.toNat - newEnd) := by
    have hL_eq : (ptr ↦ₛ L) =
        (ptr ↦ₛ L.take newEnd) ∗ ((ptr + BitVec.ofNat 64 newEnd) ↦ₛ L.drop newEnd) := by
      conv_lhs => rw [(List.take_append_drop newEnd L).symm]
      rw [pointsToBytes_append, htake_len]
    rw [hL_eq,
      ProofLib.memRegion_split' (b := ptr + BitVec.ofNat 64 newEnd) (n := bs.length - newEnd)
        (k := cap.toNat - bs.length) (b' := ptr + BitVec.ofNat 64 bs.length)
        (by dsimp [newEnd]; omega) (by dsimp [newEnd]; bv_omega) (by dsimp [newEnd]; omega),
      sepConj_assoc]
    refine sepConj_mono_right ?_
    have hdrop_len : (L.drop newEnd).length = bs.length - newEnd := by
      rw [List.length_drop, hL_len]
    rw [← hdrop_len]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion _ _)
  rw [show (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 newEnd) ∗
        (ptr ↦ₛ L) ∗ (A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      ((ptr ↦ₛ L) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 newEnd) ∗
         A.live ptr cap.toNat 1) by ac_rfl]
  refine Entails.trans (sepConj_mono_left hbytes_split) ?_
  rw [show (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 newEnd)) ∗
        ⌜newEnd ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ L.take newEnd) ∗
          memRegion (ptr + BitVec.ofNat 64 newEnd) (cap.toNat - newEnd))) =
      ⌜newEnd ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((ptr ↦ₛ L.take newEnd) ∗ memRegion (ptr + BitVec.ofNat 64 newEnd) (cap.toNat - newEnd)) ∗
         ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 newEnd) ∗
          A.live ptr cap.toNat 1)) by ac_rfl]
  exact Entails.pure_right ⟨by dsimp [newEnd]; omega, hcap, hptr⟩ (Entails.refl _)

/-! ## External-Hook Contract (`*Ext`, `17920` B) and `extra` Frame Helpers -/

/-- `<spqr::chain::Chain>::recv_key` frame (`128` B) + `nextKeyInternalStackExt` (`17792` B) = `17920` B. -/
abbrev chainRecvKeyStackExt : Nat := 128 + nextKeyInternalStackExt

/-- Spec of `<spqr::chain::Chain>::recv_key` (`0x608d0`) under `CliExternsOk` (`17920` B stack). -/
def chainRecvKeySpecExt (hkdf : HkdfFn) (A : RustAlloc) : Spec ChainRecvKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.selfPtr ∧
      s.readReg64 .x2 = x.epoch ∧ (s.readReg64 .x3).setWidth 32 = x.index ∧
      RecvPrevFits x.self⌝ ∗
      memRegion x.out 32 ∗
      chainAt A x.selfPtr x.G x.self ∗
      A.pool ∗ stackAt s.sp chainRecvKeyStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      recvKeyPostAt A x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
      A.pool ∗ stackAt s0.sp chainRecvKeyStackExt
  onPanic := fun x s0 sf =>
    ⌜((Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap

def ChainRecvKeyOkExt (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainRecvKeyName)
    ((chainRecvKeySpecExt hkdf A).inImage img)

def nextKeyInternalSpecRecvCore (hkdf : HkdfFn) (A : RustAlloc) (extra : Nat) :
    Spec NextKeyInternalGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.nextA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = x.ctrA ∧
      x.next.length = 32 ∧ x.ctr ≠ 0xffffffff#32⌝ ∗
      memRegion x.out 36 ∗ (x.nextA ↦ₛ x.next) ∗ (x.ctrA ↦₃₂ x.ctr) ∗
      A.pool ∗ memRegion (s.sp - BitVec.ofNat 64 (extra + nextKeyInternalStackX)) extra ∗
      stackAt s.sp nextKeyInternalStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      nextKeyOutAt x.out (x.ctr + 1#32) (nextKeyOut hkdf x.next x.ctr) ∗
      (x.nextA ↦ₛ nextKeyNext hkdf x.next x.ctr) ∗ (x.ctrA ↦₃₂ (x.ctr + 1#32)) ∗
      A.pool ∗ memRegion (s0.sp - BitVec.ofNat 64 (extra + nextKeyInternalStackX)) extra ∗
      stackAt s0.sp nextKeyInternalStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def chainRecvKeySpecCore (hkdf : HkdfFn) (A : RustAlloc) (extra : Nat) :
    Spec ChainRecvKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.selfPtr ∧
      s.readReg64 .x2 = x.epoch ∧ (s.readReg64 .x3).setWidth 32 = x.index ∧
      RecvPrevFits x.self⌝ ∗
      memRegion x.out 32 ∗
      chainAt A x.selfPtr x.G x.self ∗
      A.pool ∗
      memRegion (s.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra ∗
      stackAt s.sp chainRecvKeyStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      recvKeyPostAt A x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
      A.pool ∗
      memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra ∗
      stackAt s0.sp chainRecvKeyStackX
  onPanic := fun x s0 sf =>
    ⌜((Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap

abbrev recvKeyPostCore (extra : Nat) (hkdf : HkdfFn) (A : RustAlloc)
    (x : ChainRecvKeyGhost) (s0 : State) : State → SepProp → Prop :=
  fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (P' ⊢ (chainRecvKeySpecCore hkdf A extra).post x s0 sf)

theorem stackAt_chainRecvKeyExt_eq (sp : BitVec 64) :
    stackAt sp chainRecvKeyStackExt =
      memRegion (sp - BitVec.ofNat 64 (1232 + chainRecvKeyStackX)) 1232 ∗
        stackAt sp chainRecvKeyStackX := by
  change memRegion (sp - BitVec.ofNat 64 17920) 17920 =
    memRegion (sp - BitVec.ofNat 64 17920) 1232 ∗
      memRegion (sp - BitVec.ofNat 64 16688) 16688
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 17920) (n := 1232) (k := 16688)
    (b' := sp - BitVec.ofNat 64 16688) rfl (by bv_omega) (by decide)

theorem SepWPp.frame_entails_anyHeap {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P P0 F : SepProp} {Q0 Q1 : State → SepProp} {Pp : State → Prop} {R : SepProp}
    (hpre : P ⊢ P0 ∗ F)
    (hpost : ∀ sf, Q0 sf ∗ F ⊢ Q1 sf)
    (h : ∀ {R0 : SepProp}, SepWPp prog ret s P0
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P' ⊢ Q0 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R0) → (sf.mem ⊨ (⌜Pp sf⌝ ∗ anyHeap) ∗ R0))) :
    SepWPp prog ret s P
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P' ⊢ Q1 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (⌜Pp sf⌝ ∗ anyHeap) ∗ R)) := by
  intro R' hm hL
  have hm0 : s.mem ⊨ P0 ∗ (F ∗ R') := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hpre) hm
  obtain ⟨sf, hsteps, hout⟩ := h (R0 := F ∗ R) (F ∗ R') hm0 hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hsp, hcs, hent⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hmo⟩
  · rw [← sepConj_assoc] at hmf
    exact Or.inl ⟨hpcf, hrunf, P_f ∗ F, hmf, hsp, hcs, Entails.trans (sepConj_mono_left hent) (hpost sf)⟩
  · rw [← sepConj_assoc] at hmf
    refine Or.inr (Or.inl ⟨hpan, P_f ∗ F, hmf, fun hmR => ?_⟩)
    rw [sepConj_assoc] at hmR
    have hpanR := hqp hmR
    rw [← sepConj_assoc] at hpanR
    have hdrop : (⌜Pp sf⌝ ∗ anyHeap) ∗ F ⊢ ⌜Pp sf⌝ ∗ anyHeap := by
      rw [sepConj_assoc]
      exact sepConj_mono_right (entails_anyHeap _)
    exact Satisfies.mono (sepConj_mono_left hdrop) hpanR
  · exact (not_satisfies_false_sepConj hmo).elim

theorem recvKey_frame_extra {extra : Nat} {prog : Program} {hkdf : HkdfFn} {A : RustAlloc}
    {x : ChainRecvKeyGhost} {s0 s : State} {P0 P : SepProp} {R : SepProp}
    (hpre : P ⊢ P0 ∗ memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
    (h : ∀ {R0 : SepProp}, SepWPp prog (s0.readReg64 (.gpr 30#5)) s P0
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P' ⊢ (chainRecvKeySpecX hkdf A).post x s0 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R0) → (sf.mem ⊨ (chainRecvKeySpecX hkdf A).onPanic x s0 sf ∗ R0))) :
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s P
      (recvKeyPostCore extra hkdf A x s0)
      (fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (chainRecvKeySpecX hkdf A).onPanic x s0 sf ∗ R)) :=
  SepWPp.frame_entails_anyHeap hpre
    (fun _ => by dsimp only [chainRecvKeySpecX, chainRecvKeySpecCore]; exact Entails.of_eq (by ac_rfl))
    h

end CryptoVerification.SpqrV1.ChainProofs
