/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpers
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Defs
public import LibsignalBinary.Proofs.SpqrV1.Chain.ChainPbCodeSym
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
import ProofLib.SepLogic.WPp

/-!
# Helper Lemmas and Specifications for `<spqr::chain::Chain>::send_key`

Target specifications (`chainSendKeySpecX`, `chainSendKeySpecExt`), `next_key_internal` panic
specification, `VecDeque` front-pop and slot-update lemmas, and `Chain`/`ChainEpoch` unpack/pack
lemmas for `<spqr::chain::Chain>::send_key` (`0x60db0`, 149 instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.CodeLayout
open ChainAddEpochFacts ChainNewFacts AgreeStateSimp

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-- Panic spec of `<ChainEpochDirection>::next_key_internal` (`0x5fd94`). -/
def nextKeyInternalPanicSpecX : Spec NextKeyInternalGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x2 = BitVec.ofNat 64 x.next.length ∧ s.readReg64 .x3 = x.ctrA ∧
      x.next.length < 2 ^ 64 ∧ (x.next.length ≠ 32 ∨ x.ctr = 0xffffffff#32)⌝ ∗
      (x.ctrA ↦₃₂ x.ctr) ∗ stackAt s.sp nextKeyInternalStackX
  post := fun _ _ _ => ⌜False⌝
  onPanic := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ anyHeap

def NextKeyInternalPanicOkX (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr nextKeyInternalName)
    (nextKeyInternalPanicSpecX.inImage img)

def NextKeyInternalPanicPlacedOkX [LibsignalPlacement]
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_362).rebase (blkPl_362).base H)
    (blkPl_362).base
    (NextKeyInternalFacts.withLsCallInv lsmpl nextKeyInternalPanicSpecX)

abbrev chainSendKeyName : String := "<spqr::chain::Chain>::send_key"
abbrev chainSendKeyStackX : Nat := 208 + nextKeyInternalStackX

def sendKeyOkAt (A : RustAlloc) (out : BitVec 64) (ctr : BitVec 32) (key : Bytes) : SepProp :=
  (out ↦₆₄ 0#64) ∗ ((out + 0x08#64) ↦₃₂ ctr) ∗
    memRegion (out + 0x0c#64) 4 ∗ vecU8 A (out + 0x10#64) key

def sendKeyErrAt (out : BitVec 64) (err : Error) : SepProp :=
  (out ↦₆₄ 1#64) ∗ ((out + 0x08#64) ↦₈ spqrErrorTag err) ∗ memRegion (out + 0x09#64) 7 ∗
    (match err with
     | .sendKeyEpochDecreased s e =>
       ((out + 0x10#64) ↦₆₄ s) ∗ ((out + 0x18#64) ↦₆₄ e) ∗ memRegion (out + 0x20#64) 8
     | .epochOutOfRange e =>
       ((out + 0x10#64) ↦₆₄ e) ∗ memRegion (out + 0x18#64) 16
     | _ => memRegion (out + 0x10#64) 24)

def sendKeyPostAt (A : RustAlloc) (selfPtr out : BitVec 64) (self : Chain) :
    ChainResult (Chain × (BitVec 32 × Bytes)) → SepProp
  | .ok (self', (ctr, key)) => chainRepr A selfPtr self' ∗ sendKeyOkAt A out ctr key
  | .error (.err err) => chainRepr A selfPtr self ∗ sendKeyErrAt out err
  | .error (.panic _) => ⌜False⌝

structure ChainSendKeyGhost where
  out : BitVec 64
  selfPtr : BitVec 64
  epoch : Epoch
  G : ChainGhost
  self : Chain

def chainSendKeySpecX (hkdf : HkdfFn) (A : RustAlloc) : Spec ChainSendKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.selfPtr ∧ s.readReg64 .x1 = x.epoch ∧ s.readReg64 .x8 = x.out⌝ ∗
      memRegion x.out 40 ∗ chainAt A x.selfPtr x.G x.self ∗
      A.pool ∗ stackAt s.sp chainSendKeyStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sendKeyPostAt A x.selfPtr x.out x.self (Chain.sendKey hkdf x.self x.epoch) ∗
      A.pool ∗ stackAt s0.sp chainSendKeyStackX
  onPanic := fun x s0 sf =>
    ⌜((Chain.sendKey hkdf x.self x.epoch).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap

def ChainSendKeyOkX (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainSendKeyName)
    ((chainSendKeySpecX hkdf A).inImage img)

def ChainSendKeyPlacedOkX [LibsignalPlacement] (hkdf : HkdfFn) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
    (blkPl_367).base
    (NextKeyInternalFacts.withLsCallInv lsmpl (chainSendKeySpecX hkdf A))

/-- `<spqr::chain::Chain>::send_key` stack under `CliExternsOk` (`208 + nextKeyInternalStackExt = 18000` B). -/
abbrev chainSendKeyStackExt : Nat := 208 + nextKeyInternalStackExt

def chainSendKeySpecExt (hkdf : HkdfFn) (A : RustAlloc) : Spec ChainSendKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.selfPtr ∧ s.readReg64 .x1 = x.epoch ∧ s.readReg64 .x8 = x.out⌝ ∗
      memRegion x.out 40 ∗ chainAt A x.selfPtr x.G x.self ∗
      A.pool ∗ stackAt s.sp chainSendKeyStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sendKeyPostAt A x.selfPtr x.out x.self (Chain.sendKey hkdf x.self x.epoch) ∗
      A.pool ∗ stackAt s0.sp chainSendKeyStackExt
  onPanic := fun x s0 sf =>
    ⌜((Chain.sendKey hkdf x.self x.epoch).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap

def ChainSendKeyOkExt (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainSendKeyName)
    ((chainSendKeySpecExt hkdf A).inImage img)

theorem stackAt_nextKeyInternalExt_eq (sp : BitVec 64) :
    stackAt sp nextKeyInternalStackExt =
      memRegion (sp - BitVec.ofNat 64 (1232 + nextKeyInternalStackX)) 1232 ∗
      stackAt sp nextKeyInternalStackX :=
  ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 17792) (n := 1232) (k := 16560)
    (b' := sp - 16560#64) rfl (by bv_omega) (by decide)

theorem stackAt_chainSendKeyExt_eq (sp : BitVec 64) :
    stackAt sp chainSendKeyStackExt =
      memRegion (sp - BitVec.ofNat 64 (1232 + chainSendKeyStackX)) 1232 ∗
      stackAt sp chainSendKeyStackX :=
  ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 18000) (n := 1232) (k := 16768)
    (b' := sp - 16768#64) rfl (by bv_omega) (by decide)

/-! ## `VecDeque` Slot Indexing, In-Place Update, and Front Popping -/

namespace ChainSendKeyFacts

theorem vecDequeSlotsAt_get_physIdx {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α) {i : Nat}
    (hhead : head < cap) (hlen : xs.length ≤ cap) (hi : i < xs.length) :
    let s := vecDequePhysIdx head cap i
    vecDequeSlotsAt elem stride cap head ptr xs 0 cap =
      elem xs[i] (ptr + BitVec.ofNat 64 (s * stride)) ∗
        vecDequeSlotsExcept elem stride cap head ptr xs s := by
  intro s
  have hi_cap : i < cap := Nat.lt_of_lt_of_le hi hlen
  have hs_lt : s < cap := vecDequePhysIdx_lt hhead hi_cap
  have hlog : vecDequeLogIdx head cap s = i := vecDequeLogIdx_physIdx hhead hi_cap
  have hslots :
      vecDequeSlotsAt elem stride cap head ptr xs 0 cap =
        vecDequeSlotsAt elem stride cap head ptr xs 0 (s + (1 + (cap - 1 - s))) := by
    congr 1; omega
  rw [hslots, vecDequeSlotsAt_add, Nat.zero_add, vecDequeSlotsAt_add]
  have hslot :
      vecDequeSlotsAt elem stride cap head ptr xs s 1 =
        elem xs[i] (ptr + BitVec.ofNat 64 (s * stride)) := by
    simp [vecDequeSlotsAt, hlog, hi]
  rw [hslot]
  unfold vecDequeSlotsExcept
  ac_rfl

theorem vecDequeSlotsAt_set_of_ne {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α) {i : Nat} (x' : α) (s n : Nat)
    (hhead : head < cap) (hi_cap : i < cap)
    (hne : ∀ k < n, s + k < cap ∧ s + k ≠ vecDequePhysIdx head cap i) :
    vecDequeSlotsAt elem stride cap head ptr (xs.set i x') s n =
      vecDequeSlotsAt elem stride cap head ptr xs s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    obtain ⟨hs_lt, hs_ne⟩ := hne 0 (Nat.zero_lt_succ n)
    have hlog_ne : vecDequeLogIdx head cap s ≠ i :=
      vecDequeLogIdx_ne_of_ne_physIdx hhead hi_cap hs_lt (by simpa using hs_ne)
    have ih' := ih (s + 1) fun k hk => by
      have h := hne (k + 1) (by omega)
      have hsk : s + 1 + k = s + (k + 1) := by omega
      rwa [hsk]
    simp only [vecDequeSlotsAt, List.length_set, ih']
    by_cases hlt : vecDequeLogIdx head cap s < xs.length
    · simp only [hlt, ↓reduceDIte, List.getElem_set_ne (Ne.symm hlog_ne)]
    · simp only [hlt, ↓reduceDIte]

theorem vecDequeSlotsAt_set_physIdx {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α) {i : Nat} (x' : α)
    (hhead : head < cap) (hlen : xs.length ≤ cap) (hi : i < xs.length) :
    let s := vecDequePhysIdx head cap i
    elem x' (ptr + BitVec.ofNat 64 (s * stride)) ∗
      vecDequeSlotsExcept elem stride cap head ptr xs s =
      vecDequeSlotsAt elem stride cap head ptr (xs.set i x') 0 cap := by
  intro s
  have hi_cap : i < cap := Nat.lt_of_lt_of_le hi hlen
  have hs_lt : s < cap := vecDequePhysIdx_lt hhead hi_cap
  have hlog : vecDequeLogIdx head cap s = i := vecDequeLogIdx_physIdx hhead hi_cap
  have hslots :
      vecDequeSlotsAt elem stride cap head ptr (xs.set i x') 0 cap =
        vecDequeSlotsAt elem stride cap head ptr (xs.set i x') 0 (s + (1 + (cap - 1 - s))) := by
    congr 1; omega
  rw [hslots, vecDequeSlotsAt_add, Nat.zero_add, vecDequeSlotsAt_add]
  have hpre :
      vecDequeSlotsAt elem stride cap head ptr (xs.set i x') 0 s =
        vecDequeSlotsAt elem stride cap head ptr xs 0 s :=
    vecDequeSlotsAt_set_of_ne elem stride cap head ptr xs x' 0 s hhead hi_cap
      (fun k hk => ⟨by omega, by omega⟩)
  have hpost :
      vecDequeSlotsAt elem stride cap head ptr (xs.set i x') (s + 1) (cap - 1 - s) =
        vecDequeSlotsAt elem stride cap head ptr xs (s + 1) (cap - 1 - s) :=
    vecDequeSlotsAt_set_of_ne elem stride cap head ptr xs x' (s + 1) (cap - 1 - s) hhead hi_cap
      (fun k hk => ⟨by omega, by omega⟩)
  have hslot :
      vecDequeSlotsAt elem stride cap head ptr (xs.set i x') s 1 =
        elem x' (ptr + BitVec.ofNat 64 (s * stride)) := by
    simp [vecDequeSlotsAt, hlog, hi]
  rw [hpre, hpost, hslot]
  unfold vecDequeSlotsExcept
  ac_rfl

theorem vecDequeLogIdx_physIdx_one_self {head cap : Nat} (hhead : head < cap) :
    vecDequeLogIdx (vecDequePhysIdx head cap 1) cap head = cap - 1 := by
  unfold vecDequePhysIdx vecDequeLogIdx
  split_ifs <;> omega

theorem vecDequeLogIdx_eq_succ_physIdx_one {head cap k : Nat}
    (hhead : head < cap) (hk : k < cap) (hne : k ≠ head) :
    vecDequeLogIdx head cap k = vecDequeLogIdx (vecDequePhysIdx head cap 1) cap k + 1 := by
  unfold vecDequePhysIdx vecDequeLogIdx
  split_ifs <;> omega

theorem vecDequeSlotsAt_cons_eq_of_ne_head {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (x0 : α) (xs : List α) (s n : Nat)
    (hhead : head < cap)
    (hne : ∀ k < n, s + k < cap ∧ s + k ≠ head) :
    vecDequeSlotsAt elem stride cap head ptr (x0 :: xs) s n =
      vecDequeSlotsAt elem stride cap (vecDequePhysIdx head cap 1) ptr xs s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    obtain ⟨hs_lt0, hs_ne0⟩ := hne 0 (Nat.zero_lt_succ n)
    have hs_lt : s < cap := by omega
    have hs_ne : s ≠ head := by omega
    have hlog := vecDequeLogIdx_eq_succ_physIdx_one hhead hs_lt hs_ne
    have ih' := ih (s + 1) fun k hk => by
      have h := hne (k + 1) (by omega)
      have hsk : s + 1 + k = s + (k + 1) := by omega
      rwa [hsk]
    simp only [vecDequeSlotsAt, hlog, List.length_cons, ih']
    by_cases hlt : vecDequeLogIdx (vecDequePhysIdx head cap 1) cap s < xs.length
    · have hlt' : vecDequeLogIdx (vecDequePhysIdx head cap 1) cap s + 1 < xs.length + 1 :=
        Nat.succ_lt_succ hlt
      simp only [hlt, hlt', ↓reduceDIte, List.getElem_cons_succ]
    · have hlt' : ¬ vecDequeLogIdx (vecDequePhysIdx head cap 1) cap s + 1 < xs.length + 1 := by
        omega
      simp only [hlt, hlt', ↓reduceDIte]

theorem vecDequeSlotsAt_pop_front {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (x0 : α) (xs : List α)
    (hhead : head < cap) (hlen : (x0 :: xs).length ≤ cap) :
    memRegion (ptr + BitVec.ofNat 64 (head * stride)) stride ∗
      vecDequeSlotsExcept elem stride cap head ptr (x0 :: xs) head =
      vecDequeSlotsAt elem stride cap (vecDequePhysIdx head cap 1) ptr xs 0 cap := by
  have hlog_head : vecDequeLogIdx (vecDequePhysIdx head cap 1) cap head = cap - 1 :=
    vecDequeLogIdx_physIdx_one_self hhead
  have hnot_lt : ¬ vecDequeLogIdx (vecDequePhysIdx head cap 1) cap head < xs.length := by
    rw [hlog_head]; simp only [List.length_cons] at hlen; omega
  have hslots :
      vecDequeSlotsAt elem stride cap (vecDequePhysIdx head cap 1) ptr xs 0 cap =
        vecDequeSlotsAt elem stride cap (vecDequePhysIdx head cap 1) ptr xs 0
          (head + (1 + (cap - 1 - head))) := by
    congr 1; omega
  rw [hslots, vecDequeSlotsAt_add, Nat.zero_add, vecDequeSlotsAt_add]
  have hpre :
      vecDequeSlotsAt elem stride cap head ptr (x0 :: xs) 0 head =
        vecDequeSlotsAt elem stride cap (vecDequePhysIdx head cap 1) ptr xs 0 head :=
    vecDequeSlotsAt_cons_eq_of_ne_head elem stride cap head ptr x0 xs 0 head hhead
      (fun k hk => ⟨by omega, by omega⟩)
  have hpost :
      vecDequeSlotsAt elem stride cap head ptr (x0 :: xs) (head + 1) (cap - 1 - head) =
        vecDequeSlotsAt elem stride cap (vecDequePhysIdx head cap 1) ptr xs (head + 1) (cap - 1 - head) :=
    vecDequeSlotsAt_cons_eq_of_ne_head elem stride cap head ptr x0 xs (head + 1) (cap - 1 - head) hhead
      (fun k hk => ⟨by omega, by omega⟩)
  have hslot :
      vecDequeSlotsAt elem stride cap (vecDequePhysIdx head cap 1) ptr xs head 1 =
        memRegion (ptr + BitVec.ofNat 64 (head * stride)) stride := by
    simp [vecDequeSlotsAt, hnot_lt]
  unfold vecDequeSlotsExcept
  rw [hpre, hpost, hslot]
  ac_rfl

/-! ## Pure Lemmas for `Chain.sendKey` and `Chain.epochIdx` -/

theorem sendKey_of_lt (hkdf : HkdfFn) (self : Chain) (epoch : Epoch)
    (hlt : epoch < self.sendEpoch) :
    Chain.sendKey hkdf self epoch =
      .error (.err (.sendKeyEpochDecreased self.sendEpoch epoch)) := by
  simp [Chain.sendKey, hlt]

theorem epochIdx_of_gt (self : Chain) (epoch : Epoch)
    (hgt : epoch > self.currentEpoch) :
    self.epochIdx epoch = .error (.epochOutOfRange epoch) := by
  unfold Chain.epochIdx
  simp only [hgt, ↓reduceIte]

theorem epochIdx_of_back_ge (self : Chain) (epoch : Epoch)
    (hle : ¬ epoch > self.currentEpoch)
    (hge : (self.currentEpoch - epoch).toNat ≥ self.links.length) :
    self.epochIdx epoch = .error (.epochOutOfRange epoch) := by
  unfold Chain.epochIdx
  simp only [hle, hge, ↓reduceIte]

theorem epochIdx_of_lt (self : Chain) (epoch : Epoch)
    (hle : ¬ epoch > self.currentEpoch)
    (hlt : (self.currentEpoch - epoch).toNat < self.links.length) :
    self.epochIdx epoch =
      .ok (self.links.length - 1 - (self.currentEpoch - epoch).toNat) := by
  have hnot_ge : ¬ (self.currentEpoch - epoch).toNat ≥ self.links.length := by omega
  unfold Chain.epochIdx
  simp only [hle, hnot_ge, ↓reduceIte]

theorem sendKey_of_epochIdx_err (hkdf : HkdfFn) (self : Chain) (epoch : Epoch) (err : Error)
    (hge : ¬ epoch < self.sendEpoch) (herr : self.epochIdx epoch = .error err) :
    Chain.sendKey hkdf self epoch = .error (.err err) := by
  unfold Chain.sendKey
  simp only [hge, ↓reduceIte, herr, ChainResult.ofError]
  rfl

@[simp] theorem clearSendNextPrefix_zero (xs : List ChainEpoch) :
    Chain.clearSendNextPrefix 0 xs = xs := rfl

@[simp] theorem clearSendNextPrefix_one_cons (x : ChainEpoch) (xs : List ChainEpoch) :
    Chain.clearSendNextPrefix 1 (x :: xs) =
      { x with send := x.send.clearNext } :: xs := rfl

@[simp] theorem clearSendNextPrefix_length (n : Nat) (xs : List ChainEpoch) :
    (Chain.clearSendNextPrefix n xs).length = xs.length := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp [Chain.clearSendNextPrefix, ih]

theorem nextKey_isError_of_bad (hkdf : HkdfFn) (ced : ChainEpochDirection)
    (hbad : ced.next.length ≠ 32 ∨ ced.ctr = 0xffffffff#32) :
    ∃ p, ced.nextKey hkdf = .error p := by
  unfold ChainEpochDirection.nextKey ChainEpochDirection.nextKeyInternal
  rcases hbad with hlen | hctr
  · have h1 : (ced.next.length != 32) = true := by simp [hlen]
    exact ⟨.nextKeyBadLen, by simp [h1]⟩
  · by_cases hlen : ced.next.length = 32
    · have h1 : (ced.next.length != 32) = false := by simp [hlen]
      have h2 : (ced.ctr == 0xffffffff#32) = true := by simp [hctr]
      exact ⟨.ctrOverflow, by simp [h1, h2]⟩
    · have h1 : (ced.next.length != 32) = true := by simp [hlen]
      exact ⟨.nextKeyBadLen, by simp [h1]⟩

theorem nextKey_eq_ok (hkdf : HkdfFn) (ced : ChainEpochDirection)
    (hlen : ced.next.length = 32) (hctr : ced.ctr ≠ 0xffffffff#32) :
    ced.nextKey hkdf =
      .ok ({ ced with next := nextKeyNext hkdf ced.next ced.ctr, ctr := ced.ctr + 1#32 },
        (ced.ctr + 1#32, nextKeyOut hkdf ced.next ced.ctr)) := by
  unfold ChainEpochDirection.nextKey
  rw [nextKeyInternal_eq_ok hkdf hlen hctr]
  rfl

/-! ## Separation-Logic Helpers for `vecU8At` Clearing and `ChainEpoch` Popping -/

/-- Setting `len := 0` (`(a + 16#64) ↦₆₄ 0#64`) in an unpacked `vecU8At` yields `vecU8At A a cap ptr []`. -/
theorem vecU8At_clear_intro (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs.length ⊢
      vecU8At A a cap ptr [] := by
  unfold vecU8At vecHeader vecU8Rest
  simp only [Nat.mul_one, List.length_nil]
  have h0_64 : BitVec.ofNat 64 0 = 0#64 := rfl
  rw [h0_64]
  rw [show ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      ⌜0 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (if cap = 0 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ ([] : List (BitVec 8))) ∗
         memRegion (ptr + 0#64) (cap.toNat - 0)) =
    ⌜0 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      (if cap = 0 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ ([] : List (BitVec 8))) ∗
         memRegion (ptr + 0#64) (cap.toNat - 0)) by ac_rfl]
  refine Entails.pure_right ⟨Nat.zero_le _, hcap, hptr⟩ ?_
  by_cases hcap0 : cap = 0
  · subst hcap0
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs0
    simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap0, ↓reduceIte]
    have hbytes_mem :
        (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
          (ptr ↦ₛ ([] : List (BitVec 8))) ∗ memRegion (ptr + 0#64) (cap.toNat - 0) := by
      simp only [pointsToBytes_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
      rw [ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)]
      exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)
    rw [show (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
        (ptr ↦ₛ bs) ∗ (A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
          A.live ptr cap.toNat 1) by ac_rfl]
    refine Entails.trans (sepConj_mono_left hbytes_mem) ?_
    rw [show ((ptr ↦ₛ ([] : List (BitVec 8))) ∗ memRegion (ptr + 0#64) (cap.toNat - 0)) ∗
        (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
          A.live ptr cap.toNat 1) =
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
        (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ ([] : List (BitVec 8))) ∗
          memRegion (ptr + 0#64) (cap.toNat - 0)) by ac_rfl]
    exact Entails.refl _

/-- Unpack `chainEpochDirectionAt A a g ced` for `clear_next` (`str xzr, [a, #16]`) or `next_key_internal`. -/
theorem chainEpochDirectionAt_unpack_next (A : RustAlloc) (a : BitVec 64)
    (g : ChainEpochDirectionGhost) (ced : ChainEpochDirection) :
    chainEpochDirectionAt A a g ced ⊢
      ⌜ced.next.length ≤ g.next.cap.toNat ∧ g.next.cap.toNat < 2 ^ 63 ∧ g.next.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.next.cap) ∗ ((a + 8#64) ↦₆₄ g.next.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ced.next.length) ∗
      (g.next.ptr ↦ₛ ced.next) ∗ vecU8Rest A g.next.cap g.next.ptr ced.next.length ∗
      keyHistoryAt A (a + 24#64) g.prev ced.prev ∗
      ((a + 48#64) ↦₃₂ ced.ctr) ∗
      memRegion (a + 52#64) 4 := by
  unfold chainEpochDirectionAt
  refine Entails.trans (sepConj_mono_left (vecU8At_unpack A a g.next.cap g.next.ptr ced.next)) ?_
  rw [show (⌜ced.next.length ≤ g.next.cap.toNat ∧ g.next.cap.toNat < 2 ^ 63 ∧ g.next.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.next.cap) ∗ ((a + 8#64) ↦₆₄ g.next.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ced.next.length) ∗
      (g.next.ptr ↦ₛ ced.next) ∗ vecU8Rest A g.next.cap g.next.ptr ced.next.length) ∗
      keyHistoryAt A (a + 24#64) g.prev ced.prev ∗ ((a + 48#64) ↦₃₂ ced.ctr) ∗ memRegion (a + 52#64) 4 =
    ⌜ced.next.length ≤ g.next.cap.toNat ∧ g.next.cap.toNat < 2 ^ 63 ∧ g.next.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.next.cap) ∗ ((a + 8#64) ↦₆₄ g.next.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ced.next.length) ∗
      (g.next.ptr ↦ₛ ced.next) ∗ vecU8Rest A g.next.cap g.next.ptr ced.next.length ∗
      keyHistoryAt A (a + 24#64) g.prev ced.prev ∗
      ((a + 48#64) ↦₃₂ ced.ctr) ∗
      memRegion (a + 52#64) 4 by ac_rfl]
  exact Entails.refl _

/-- Fold `chainEpochDirectionAt` after `clear_next` (`[a + 16] := 0`). -/
theorem chainEpochDirectionAt_pack_clearNext (A : RustAlloc) (a : BitVec 64)
    (g : ChainEpochDirectionGhost) (ced : ChainEpochDirection)
    (hle : ced.next.length ≤ g.next.cap.toNat) (hcap : g.next.cap.toNat < 2 ^ 63)
    (hptr : g.next.ptr ≠ 0) :
    (a ↦₆₄ g.next.cap) ∗ ((a + 8#64) ↦₆₄ g.next.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      (g.next.ptr ↦ₛ ced.next) ∗ vecU8Rest A g.next.cap g.next.ptr ced.next.length ∗
      keyHistoryAt A (a + 24#64) g.prev ced.prev ∗
      ((a + 48#64) ↦₃₂ ced.ctr) ∗
      memRegion (a + 52#64) 4 ⊢
      chainEpochDirectionAt A a g ced.clearNext := by
  unfold chainEpochDirectionAt ChainEpochDirection.clearNext
  dsimp only
  rw [show (a ↦₆₄ g.next.cap) ∗ ((a + 8#64) ↦₆₄ g.next.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      (g.next.ptr ↦ₛ ced.next) ∗ vecU8Rest A g.next.cap g.next.ptr ced.next.length ∗
      keyHistoryAt A (a + 24#64) g.prev ced.prev ∗
      ((a + 48#64) ↦₃₂ ced.ctr) ∗ memRegion (a + 52#64) 4 =
    ((a ↦₆₄ g.next.cap) ∗ ((a + 8#64) ↦₆₄ g.next.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      (g.next.ptr ↦ₛ ced.next) ∗ vecU8Rest A g.next.cap g.next.ptr ced.next.length) ∗
      (keyHistoryAt A (a + 24#64) g.prev ced.prev ∗
        ((a + 48#64) ↦₃₂ ced.ctr) ∗ memRegion (a + 52#64) 4) by ac_rfl]
  exact sepConj_mono_left (vecU8At_clear_intro A a g.next.cap g.next.ptr ced.next hle hcap hptr)

/-- Fold `chainEpochDirectionAt` after `next_key_internal` updates `next` (keeping length 32) and `ctr`. -/
theorem chainEpochDirectionAt_pack_nextKey (A : RustAlloc) (a : BitVec 64)
    (g : ChainEpochDirectionGhost) (ced : ChainEpochDirection)
    (next' : List (BitVec 8)) (ctr' : BitVec 32)
    (hlen : ced.next.length = 32) (hlen' : next'.length = 32)
    (hle : ced.next.length ≤ g.next.cap.toNat) (hcap : g.next.cap.toNat < 2 ^ 63)
    (hptr : g.next.ptr ≠ 0) :
    (a ↦₆₄ g.next.cap) ∗ ((a + 8#64) ↦₆₄ g.next.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ced.next.length) ∗
      (g.next.ptr ↦ₛ next') ∗ vecU8Rest A g.next.cap g.next.ptr ced.next.length ∗
      keyHistoryAt A (a + 24#64) g.prev ced.prev ∗
      ((a + 48#64) ↦₃₂ ctr') ∗
      memRegion (a + 52#64) 4 ⊢
      chainEpochDirectionAt A a g { ced with next := next', ctr := ctr' } := by
  have hlen_eq : ced.next.length = next'.length := by omega
  have hle' : next'.length ≤ g.next.cap.toNat := by omega
  rw [hlen_eq]
  unfold chainEpochDirectionAt vecU8At vecHeader vecU8Rest
  dsimp only
  have hcap_ne : g.next.cap ≠ 0 := by
    intro h0
    have h0' : g.next.cap.toNat = 0 := congrArg BitVec.toNat h0
    omega
  simp only [hcap_ne, ↓reduceIte]
  rw [show (((a ↦₆₄ g.next.cap) ∗ ((a + 8#64) ↦₆₄ g.next.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 next'.length)) ∗
      ⌜next'.length ≤ g.next.cap.toNat ∧ g.next.cap.toNat < 2 ^ 63 ∧ g.next.ptr ≠ 0⌝ ∗
      (A.live g.next.ptr g.next.cap.toNat 1 ∗ (g.next.ptr ↦ₛ next') ∗
        memRegion (g.next.ptr + BitVec.ofNat 64 next'.length) (g.next.cap.toNat - next'.length))) ∗
      keyHistoryAt A (a + 24#64) g.prev ced.prev ∗
      ((a + 48#64) ↦₃₂ ctr') ∗ memRegion (a + 52#64) 4 =
    ⌜next'.length ≤ g.next.cap.toNat ∧ g.next.cap.toNat < 2 ^ 63 ∧ g.next.ptr ≠ 0⌝ ∗
      ((a ↦₆₄ g.next.cap) ∗ ((a + 8#64) ↦₆₄ g.next.ptr) ∗
       ((a + 16#64) ↦₆₄ BitVec.ofNat 64 next'.length) ∗
       (g.next.ptr ↦ₛ next') ∗
       (A.live g.next.ptr g.next.cap.toNat 1 ∗
         memRegion (g.next.ptr + BitVec.ofNat 64 next'.length) (g.next.cap.toNat - next'.length)) ∗
       keyHistoryAt A (a + 24#64) g.prev ced.prev ∗
       ((a + 48#64) ↦₃₂ ctr') ∗ memRegion (a + 52#64) 4) by ac_rfl]
  exact Entails.pure_right ⟨hle', hcap, hptr⟩ (Entails.refl _)

/-! ## Stack, Sret, and `ChainEpoch` Unpack/Dealloc Helpers -/

/-- Split `stackAt sp chainSendKeyStackX` (`208 + nextKeyInternalStackX` = `16768` bytes)
into the sub-frame `stackAt (sp - 208#64) nextKeyInternalStackX` and the local/callee-saved slots. -/
theorem stackAt_chainSendKeyX_split (sp : BitVec 64) :
    stackAt sp chainSendKeyStackX =
      stackAt (sp - 208#64) nextKeyInternalStackX ∗
      memRegion (sp - 208#64) 8 ∗
      (∃∗ l0 : BitVec 64, ∃∗ l1 : BitVec 64, ∃∗ l2 : BitVec 64,
       ∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64,
        ((sp - 200#64) ↦₆₄ l0) ∗ ((sp - 192#64) ↦₆₄ l1) ∗ ((sp - 184#64) ↦₆₄ l2) ∗
        ((sp - 176#64) ↦₆₄ q0) ∗ ((sp - 168#64) ↦₆₄ q1) ∗ ((sp - 160#64) ↦₆₄ q2) ∗ ((sp - 152#64) ↦₆₄ q3)) ∗
      memRegion (sp - 144#64) 12 ∗
      memRegion (sp - 132#64) 36 ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗ ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗ ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗ ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  change memRegion (sp - BitVec.ofNat 64 16768) 16768 =
    memRegion (sp - 208#64 - BitVec.ofNat 64 16560) 16560 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16768) (n := 16560) (k := 208)
      (b' := sp - 208#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 208#64) (n := 8) (k := 200)
      (b' := sp - 200#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 200#64) (n := 56) (k := 144)
      (b' := sp - 144#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 144#64) (n := 12) (k := 132)
      (b' := sp - 132#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 132#64) (n := 36) (k := 96)
      (b' := sp - 96#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - BitVec.ofNat 64 16768) 16560 ∗
    (memRegion (sp - 208#64) 8 ∗
      (memRegion (sp - 200#64) (8 * 7) ∗
        (memRegion (sp - 144#64) 12 ∗
          (memRegion (sp - 132#64) 36 ∗ memRegion (sp - 96#64) (8 * 12))))) = _
  rw [ProofLib.memRegion_cells (sp - 200#64) 7 (by decide),
    ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  have hsub : sp - 208#64 - BitVec.ofNat 64 16560 = sp - BitVec.ofNat 64 16768 := by bv_kernel
  have hc7 : cells (sp - 200#64) 7 =
      (∃∗ l0 : BitVec 64, ∃∗ l1 : BitVec 64, ∃∗ l2 : BitVec 64,
       ∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64,
        ((sp - 200#64) ↦₆₄ l0) ∗ ((sp - 192#64) ↦₆₄ l1) ∗ ((sp - 184#64) ↦₆₄ l2) ∗
        ((sp - 176#64) ↦₆₄ q0) ∗ ((sp - 168#64) ↦₆₄ q1) ∗ ((sp - 160#64) ↦₆₄ q2) ∗ ((sp - 152#64) ↦₆₄ q3)) := by
    cells_unfold
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗ ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗ ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗ ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
    cells_unfold
  rw [hsub, hc7, hc12]

/-- Rejoin the `send_key` stack slots into `stackAt sp chainSendKeyStackX`. -/
theorem rejoin_stack_chainSendKeyX (sp : BitVec 64)
    (l0 l1 l2 q0 q1 q2 q3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64) :
    stackAt (sp - 208#64) nextKeyInternalStackX ∗
      memRegion (sp - 208#64) 8 ∗
      ((sp - 200#64) ↦₆₄ l0) ∗ ((sp - 192#64) ↦₆₄ l1) ∗ ((sp - 184#64) ↦₆₄ l2) ∗
      ((sp - 176#64) ↦₆₄ q0) ∗ ((sp - 168#64) ↦₆₄ q1) ∗ ((sp - 160#64) ↦₆₄ q2) ∗ ((sp - 152#64) ↦₆₄ q3) ∗
      memRegion (sp - 144#64) 12 ∗
      memRegion (sp - 132#64) 36 ∗
      ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗ ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
      ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗ ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
      ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗ ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11) ⊢
      stackAt sp chainSendKeyStackX := by
  rw [stackAt_chainSendKeyX_split sp]
  have h7 :
      ((sp - 200#64) ↦₆₄ l0) ∗ ((sp - 192#64) ↦₆₄ l1) ∗ ((sp - 184#64) ↦₆₄ l2) ∗
      ((sp - 176#64) ↦₆₄ q0) ∗ ((sp - 168#64) ↦₆₄ q1) ∗ ((sp - 160#64) ↦₆₄ q2) ∗ ((sp - 152#64) ↦₆₄ q3) ⊢
      (∃∗ l0 : BitVec 64, ∃∗ l1 : BitVec 64, ∃∗ l2 : BitVec 64,
       ∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64,
        ((sp - 200#64) ↦₆₄ l0) ∗ ((sp - 192#64) ↦₆₄ l1) ∗ ((sp - 184#64) ↦₆₄ l2) ∗
        ((sp - 176#64) ↦₆₄ q0) ∗ ((sp - 168#64) ↦₆₄ q1) ∗ ((sp - 160#64) ↦₆₄ q2) ∗ ((sp - 152#64) ↦₆₄ q3)) :=
    Entails.sepExists_right l0 (Entails.sepExists_right l1 (Entails.sepExists_right l2
      (Entails.sepExists_right q0 (Entails.sepExists_right q1 (Entails.sepExists_right q2
        (Entails.sepExists_right q3 (Entails.refl _)))))))
  have h12 :
      ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗ ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
      ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗ ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
      ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗ ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11) ⊢
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗ ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗ ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗ ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) :=
    Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
      (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
        (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
          (Entails.sepExists_right c9 (Entails.sepExists_right c10
            (Entails.sepExists_right c11 (Entails.refl _))))))))))))
  rw [show stackAt (sp - 208#64) nextKeyInternalStackX ∗
      memRegion (sp - 208#64) 8 ∗
      ((sp - 200#64) ↦₆₄ l0) ∗ ((sp - 192#64) ↦₆₄ l1) ∗ ((sp - 184#64) ↦₆₄ l2) ∗
      ((sp - 176#64) ↦₆₄ q0) ∗ ((sp - 168#64) ↦₆₄ q1) ∗ ((sp - 160#64) ↦₆₄ q2) ∗ ((sp - 152#64) ↦₆₄ q3) ∗
      memRegion (sp - 144#64) 12 ∗
      memRegion (sp - 132#64) 36 ∗
      ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗ ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
      ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗ ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
      ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗ ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11) =
    stackAt (sp - 208#64) nextKeyInternalStackX ∗
      memRegion (sp - 208#64) 8 ∗
      (((sp - 200#64) ↦₆₄ l0) ∗ ((sp - 192#64) ↦₆₄ l1) ∗ ((sp - 184#64) ↦₆₄ l2) ∗
       ((sp - 176#64) ↦₆₄ q0) ∗ ((sp - 168#64) ↦₆₄ q1) ∗ ((sp - 160#64) ↦₆₄ q2) ∗ ((sp - 152#64) ↦₆₄ q3)) ∗
      memRegion (sp - 144#64) 12 ∗
      memRegion (sp - 132#64) 36 ∗
      (((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗ ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
       ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗ ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
       ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗ ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) by ac_rfl]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono h7
    (sepConj_mono_right (sepConj_mono_right h12))))

/-- Split `stackAt sp nextKeyInternalStackX` (`176 + extHookStack`) into the bottom 176B and `stackAt sp extHookStack`. -/
theorem stackAt_nextKeyInternalX_top_split (sp : BitVec 64) :
    stackAt sp nextKeyInternalStackX =
      memRegion (sp - BitVec.ofNat 64 nextKeyInternalStackX) 176 ∗ stackAt sp extHookStack := by
  change memRegion (sp - BitVec.ofNat 64 16560) 16560 =
    memRegion (sp - BitVec.ofNat 64 16560) 176 ∗ memRegion (sp - BitVec.ofNat 64 16384) 16384
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16560) (n := 176) (k := 16384)
    (b' := sp - BitVec.ofNat 64 16384) rfl (by bv_omega) (by decide)

/-- Fold `((sp - 132#64) ↦₃₂ ctr) ∗ ((sp - 128#64) ↦₆₄ k0) ∗ ... ∗ ((sp - 104#64) ↦₆₄ k3)` into
`memRegion (sp - 132#64) 36`. -/
theorem pointsTo32_cells4_entails_memRegion_36 (sp : BitVec 64) (ctr : BitVec 32)
    (k0 k1 k2 k3 : BitVec 64) :
    ((sp - 132#64) ↦₃₂ ctr) ∗
      ((sp - 128#64) ↦₆₄ k0) ∗ ((sp - 120#64) ↦₆₄ k1) ∗
      ((sp - 112#64) ↦₆₄ k2) ∗ ((sp - 104#64) ↦₆₄ k3) ⊢
      memRegion (sp - 132#64) 36 := by
  rw [ProofLib.memRegion_split' (b := sp - 132#64) (n := 4) (k := 32)
    (b' := sp - 128#64) rfl (by bv_omega) (by decide)]
  have h4 : ((sp - 132#64) ↦₃₂ ctr) ⊢ memRegion (sp - 132#64) 4 := by
    rw [ProofLib.memRegion_four (sp - 132#64)]
    exact Entails.sepExists_right ctr (Entails.refl _)
  have h32 := cells4_entails_memRegion_32 (sp - 128#64) k0 k1 k2 k3
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at h32
  rw [show ((sp - 132#64) ↦₃₂ ctr) ∗
      ((sp - 128#64) ↦₆₄ k0) ∗ ((sp - 120#64) ↦₆₄ k1) ∗
      ((sp - 112#64) ↦₆₄ k2) ∗ ((sp - 104#64) ↦₆₄ k3) =
    ((sp - 132#64) ↦₃₂ ctr) ∗
      (((sp - 128#64) ↦₆₄ k0) ∗ ((sp - 120#64) ↦₆₄ k1) ∗
       ((sp - 112#64) ↦₆₄ k2) ∗ ((sp - 104#64) ↦₆₄ k3)) by ac_rfl]
  exact sepConj_mono h4 h32

/-- Split `memRegion out 40` for the error return paths of `send_key`. -/
theorem memRegion_40_err_split (out : BitVec 64) :
    memRegion out 40 =
      (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗
      (∃∗ b0 : BitVec 8, (out + 8#64) ↦₈ b0) ∗
      memRegion (out + 9#64) 7 ∗
      (∃∗ w2 : BitVec 64, (out + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (out + 24#64) ↦₆₄ w3) ∗
      memRegion (out + 32#64) 8 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 32) (b' := out + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 31) (b' := out + 9#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 9#64) (n := 7) (k := 24) (b' := out + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 16) (b' := out + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 8) (b' := out + 32#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight out,
    ProofLib.memRegion_one (out + 8#64),
    ProofLib.memRegion_eight (out + 16#64),
    ProofLib.memRegion_eight (out + 24#64)]

/-- Split `memRegion out 40` for the `Ok` return path of `send_key`. -/
theorem memRegion_40_ok_split (out : BitVec 64) :
    memRegion out 40 =
      (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗
      (∃∗ d0 : BitVec 32, (out + 8#64) ↦₃₂ d0) ∗
      memRegion (out + 12#64) 4 ∗
      (∃∗ w2 : BitVec 64, (out + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (out + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (out + 32#64) ↦₆₄ w4) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 32) (b' := out + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 8#64) (n := 4) (k := 28) (b' := out + 12#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 12#64) (n := 4) (k := 24) (b' := out + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 16) (b' := out + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 8) (b' := out + 32#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight out,
    ProofLib.memRegion_four (out + 8#64),
    ProofLib.memRegion_eight (out + 16#64),
    ProofLib.memRegion_eight (out + 24#64),
    ProofLib.memRegion_eight (out + 32#64)]

theorem pointsTo64_memRegion_8_entails_16 (a v : BitVec 64) :
    (a ↦₆₄ v) ∗ memRegion (a + 8#64) 8 ⊢ memRegion a 16 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 8) (b' := a + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight a]
  exact sepConj_mono_left (Entails.sepExists_right v (Entails.refl _))

theorem sendKeyErrAt_epochOutOfRange_intro (out epoch w3 : BitVec 64) :
    (out ↦₆₄ 1#64) ∗ ((out + 8#64) ↦₈ 4#8) ∗ memRegion (out + 9#64) 7 ∗
      ((out + 16#64) ↦₆₄ epoch) ∗ ((out + 24#64) ↦₆₄ w3) ∗ memRegion (out + 32#64) 8 ⊢
      sendKeyErrAt out (.epochOutOfRange epoch) := by
  unfold sendKeyErrAt spqrErrorTag
  dsimp only
  have hm := pointsTo64_memRegion_8_entails_16 (out + 24#64) w3
  have haddr : out + 24#64 + 8#64 = out + 32#64 := by bv_kernel
  rw [haddr] at hm
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm)))

theorem sendKeyErrAt_sendKeyEpochDecreased_intro (out sendEpoch epoch : BitVec 64) :
    (out ↦₆₄ 1#64) ∗ ((out + 8#64) ↦₈ 13#8) ∗ memRegion (out + 9#64) 7 ∗
      ((out + 16#64) ↦₆₄ sendEpoch) ∗ ((out + 24#64) ↦₆₄ epoch) ∗ memRegion (out + 32#64) 8 ⊢
      sendKeyErrAt out (.sendKeyEpochDecreased sendEpoch epoch) := by
  unfold sendKeyErrAt spqrErrorTag
  exact Entails.refl _

theorem sendKeyOkAt_intro (A : RustAlloc) (out : BitVec 64) (ctr : BitVec 32)
    (p_key : BitVec 64) (key : Bytes) (hlen : key.length = 32) (hp : p_key ≠ 0#64) :
    (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₃₂ ctr) ∗ memRegion (out + 12#64) 4 ∗
      ((out + 16#64) ↦₆₄ 32#64) ∗ ((out + 24#64) ↦₆₄ p_key) ∗ ((out + 32#64) ↦₆₄ 32#64) ∗
      A.live p_key 32 1 ∗ (p_key ↦ₛ key) ⊢
      sendKeyOkAt A out ctr key := by
  unfold sendKeyOkAt vecU8
  have hvec := ChainNewFacts.vecU8At_32_intro A (out + 16#64) p_key hlen hp
  have h24 : out + 16#64 + 8#64 = out + 24#64 := by bv_kernel
  have h32 : out + 16#64 + 16#64 = out + 32#64 := by bv_kernel
  rw [h24, h32] at hvec
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  exact Entails.sepExists_right 32#64 (Entails.sepExists_right p_key hvec)

/-- Common tail expression of `Chain.sendKey` once `sendEpoch1`, `links2`, and `epochIndex` are resolved. -/
def sendKeyTail (hkdf : HkdfFn) (self : Chain) (sendEpoch1 : Epoch)
    (links2 : List ChainEpoch) (epochIndex : Nat) (hi : epochIndex < links2.length) :
    ChainResult (Chain × (BitVec 32 × Bytes)) := do
  let link := links2[epochIndex]
  let (send', out) ← ChainResult.ofPanic (link.send.nextKey hkdf)
  let links' := links2.set epochIndex { link with send := send' }
  return ({ self with sendEpoch := sendEpoch1, links := links' }, out)

theorem sendKey_eq_tail_of_eq (hkdf : HkdfFn) (self : Chain) (epoch : Epoch) (epochIndex0 : Nat)
    (hge : ¬ epoch < self.sendEpoch) (hidx : self.epochIdx epoch = .ok epochIndex0)
    (hi : epochIndex0 < self.links.length) (heq : self.sendEpoch = epoch) :
    Chain.sendKey hkdf self epoch =
      sendKeyTail hkdf self self.sendEpoch self.links epochIndex0 hi := by
  have hne : (self.sendEpoch != epoch) = false := by simp [heq]
  have hget : self.links[epochIndex0]? = some self.links[epochIndex0] :=
    List.getElem?_eq_getElem hi
  unfold Chain.sendKey sendKeyTail
  simp only [hge, ↓reduceIte, hidx, ChainResult.ofError, Bind.bind, Except.bind,
    hne, Bool.false_eq_true, hget]

theorem sendKey_eq_tail_of_ne_zero (hkdf : HkdfFn) (self : Chain) (epoch : Epoch)
    (hge : ¬ epoch < self.sendEpoch) (hidx : self.epochIdx epoch = .ok 0)
    (hi : 0 < self.links.length) (hne : self.sendEpoch ≠ epoch) :
    Chain.sendKey hkdf self epoch =
      sendKeyTail hkdf self epoch self.links 0 hi := by
  have hne' : (self.sendEpoch != epoch) = true := by simp [hne]
  have hget : self.links[0]? = some self.links[0] := List.getElem?_eq_getElem hi
  unfold Chain.sendKey sendKeyTail EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
  simp only [hge, ↓reduceIte, hidx, ChainResult.ofError, Bind.bind, Except.bind,
    hne', Nat.zero_sub, List.drop_zero, clearSendNextPrefix_zero, hget]

theorem clearSendNextPrefix_one_eq_set (links1 : List ChainEpoch) (h0 : 0 < links1.length) :
    Chain.clearSendNextPrefix 1 links1 =
      links1.set 0 { links1[0] with send := links1[0].send.clearNext } := by
  cases links1 with
  | nil => simp at h0
  | cons x xs => rfl

theorem sendKey_eq_tail_of_ne_pos (hkdf : HkdfFn) (self : Chain) (epoch : Epoch) (epochIndex0 : Nat)
    (hge : ¬ epoch < self.sendEpoch) (hidx : self.epochIdx epoch = .ok epochIndex0)
    (hi : epochIndex0 < self.links.length) (hne : self.sendEpoch ≠ epoch)
    (hpos : 1 ≤ epochIndex0) :
    let links1 := self.links.drop (epochIndex0 - 1)
    have h0 : 0 < links1.length := by simp [links1]; omega
    let links2 := links1.set 0 { links1[0] with send := links1[0].send.clearNext }
    have h1 : 1 < links2.length := by simp [links2, links1]; omega
    Chain.sendKey hkdf self epoch =
      sendKeyTail hkdf self epoch links2 1 h1 := by
  intro links1 h0 links2 h1
  have hne' : (self.sendEpoch != epoch) = true := by simp [hne]
  have hsub : epochIndex0 - (epochIndex0 - 1) = 1 := by omega
  have hclear : Chain.clearSendNextPrefix 1 (self.links.drop (epochIndex0 - 1)) = links2 :=
    clearSendNextPrefix_one_eq_set links1 h0
  have hget : links2[1]? = some links2[1] := List.getElem?_eq_getElem h1
  unfold Chain.sendKey sendKeyTail EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
  simp only [hge, ↓reduceIte, hidx, ChainResult.ofError, Bind.bind, Except.bind,
    hne', hsub, hclear, hget]

theorem sendKeyTail_isPanic_of_bad (hkdf : HkdfFn) (self : Chain) (sendEpoch1 : Epoch)
    (links2 : List ChainEpoch) (epochIndex : Nat) (hi : epochIndex < links2.length)
    (hbad : links2[epochIndex].send.next.length ≠ 32 ∨ links2[epochIndex].send.ctr = 0xffffffff#32) :
    (sendKeyTail hkdf self sendEpoch1 links2 epochIndex hi).isPanic = true := by
  obtain ⟨p, hp⟩ := nextKey_isError_of_bad hkdf links2[epochIndex].send hbad
  unfold sendKeyTail
  simp [hp, ChainResult.ofPanic, ChainResult.isPanic, ChainError.isPanic]

theorem sendKeyTail_eq_ok (hkdf : HkdfFn) (self : Chain) (sendEpoch1 : Epoch)
    (links2 : List ChainEpoch) (epochIndex : Nat) (hi : epochIndex < links2.length)
    (hlen : links2[epochIndex].send.next.length = 32)
    (hctr : links2[epochIndex].send.ctr ≠ 0xffffffff#32) :
    let link := links2[epochIndex]
    let send' : ChainEpochDirection :=
      { link.send with
        next := nextKeyNext hkdf link.send.next link.send.ctr
        ctr := link.send.ctr + 1#32 }
    let outKey := nextKeyOut hkdf link.send.next link.send.ctr
    let links' := links2.set epochIndex { link with send := send' }
    sendKeyTail hkdf self sendEpoch1 links2 epochIndex hi =
      .ok ({ self with sendEpoch := sendEpoch1, links := links' }, (link.send.ctr + 1#32, outKey)) := by
  intro link send' outKey links'
  unfold sendKeyTail
  dsimp only
  rw [nextKey_eq_ok hkdf links2[epochIndex].send hlen hctr]
  rfl

/-! ## `BitVec` Arithmetic and `VecDeque` Physical Index Helpers -/

theorem add_not_eq_ofNat_sub {len : Nat} {b : BitVec 64}
    (hlt : b.toNat < len) :
    BitVec.ofNat 64 len + ~~~b = BitVec.ofNat 64 (len - 1 - b.toNat) := by
  have hk : len = (len - 1 - b.toNat) + 1 + b.toNat := by omega
  conv => lhs; rw [hk]
  rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_kernel


theorem physIdx_madd_eq {head cap ptr : BitVec 64} {len : Nat}
    (hhead : head.toNat < cap.toNat) (hlen : len < cap.toNat) (hcap : cap.toNat * 112 < 2 ^ 63) :
    ptr + (head + BitVec.ofNat 64 len -
      if BitVec.ult (head + BitVec.ofNat 64 len) cap = true then 0#64 else cap) * 112#64 =
      ptr + BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat len * 112) := by
  apply congrArg (ptr + ·)
  have hsum_lt : head.toNat + len < 18446744073709551616 := by omega
  have hlen_lt : len < 18446744073709551616 := by omega
  have hsum_toNat : (head + BitVec.ofNat 64 len).toNat = head.toNat + len := by
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt, Nat.mod_eq_of_lt hsum_lt]
  have hult : BitVec.ult (head + BitVec.ofNat 64 len) cap = decide (head.toNat + len < cap.toNat) := by
    simp [BitVec.ult, hsum_toNat]
  rw [hult]; unfold vecDequePhysIdx
  by_cases hlt : head.toNat + len < cap.toNat
  · simp only [hlt, decide_true, ↓reduceIte, BitVec.sub_zero]; apply BitVec.eq_of_toNat_eq
    have hmul_lt : (head.toNat + len) * 112 < 18446744073709551616 := by omega
    simp [BitVec.toNat_mul, hsum_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmul_lt]
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]; apply BitVec.eq_of_toNat_eq
    have hsub_toNat : (head + BitVec.ofNat 64 len - cap).toNat = head.toNat + len - cap.toNat := by
      rw [BitVec.toNat_sub, hsum_toNat]; have : cap.toNat < 18446744073709551616 := by omega
      omega
    have hmul_lt : (head.toNat + len - cap.toNat) * 112 < 18446744073709551616 := by omega
    simp [BitVec.toNat_mul, hsub_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmul_lt]

theorem physIdx_zero_madd_eq {head cap ptr : BitVec 64}
    (hhead : head.toNat < cap.toNat) (hcap : cap.toNat * 112 < 2 ^ 63) :
    ptr + (head - if BitVec.ult head cap = true then 0#64 else cap) * 112#64 =
      ptr + BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 0 * 112) := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    physIdx_madd_eq (head := head) (cap := cap) (ptr := ptr) (len := 0) hhead (by omega) hcap

theorem head_mul_112_eq {head cap ptr : BitVec 64}
    (hhead : head.toNat < cap.toNat) (hcap : cap.toNat * 112 < 2 ^ 63) :
    ptr + head * 112#64 =
      ptr + BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 0 * 112) := by
  have hult : BitVec.ult head cap = true := by simp [BitVec.ult, hhead]
  simpa only [hult, ↓reduceIte, BitVec.sub_zero] using physIdx_zero_madd_eq (ptr := ptr) hhead hcap

theorem physIdx_one_eq {head cap : BitVec 64}
    (hhead : head.toNat < cap.toNat) (hcap : cap.toNat * 112 < 2 ^ 63) :
    head + 1#64 - (if BitVec.ult (head + 1#64) cap = true then 0#64 else cap) =
      BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1) := by
  have hsum_lt : head.toNat + 1 < 18446744073709551616 := by omega
  have hsum_toNat : (head + 1#64).toNat = head.toNat + 1 := by
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt hsum_lt]
  have hult : BitVec.ult (head + 1#64) cap = decide (head.toNat + 1 < cap.toNat) := by
    simp [BitVec.ult, hsum_toNat]
  rw [hult]; unfold vecDequePhysIdx
  by_cases hlt : head.toNat + 1 < cap.toNat
  · simp only [hlt, decide_true, ↓reduceIte, BitVec.sub_zero]; apply BitVec.eq_of_toNat_eq
    simp [hsum_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum_lt]
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]; apply BitVec.eq_of_toNat_eq
    have hsub_toNat : (head + 1#64 - cap).toNat = head.toNat + 1 - cap.toNat := by
      rw [BitVec.toNat_sub, hsum_toNat]; have : cap.toNat < 18446744073709551616 := by omega
      omega
    have hlt' : head.toNat + 1 - cap.toNat < 18446744073709551616 := by omega
    simp [hsub_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt']

/-! ## `chainAt` and `chainEpochAt` Unpack/Pack Lemmas -/

/-- Untouched fields of `Chain` during `send_key`: `next_root`, `params`, `dir`, and 4B tail padding. -/
def chainRestSendKeyAt (A : RustAlloc) (a : BitVec 64) (G : ChainGhost) (c : Chain) : SepProp :=
  vecU8At A (a + 0x20#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
    chainParamsAt (a + 0x48#64) c.params ∗ directionAt (a + 0x50#64) c.dir ∗ memRegion (a + 0x54#64) 4

theorem chainAt_unpack_sendKey (A : RustAlloc) (a : BitVec 64) (G : ChainGhost) (c : Chain) :
    chainAt A a G c ⊢
      ⌜G.epochs.length = c.links.length ∧ c.links.length ≤ G.linksCap.toNat ∧
        G.linksCap.toNat * 112 < 2 ^ 63 ∧ G.linksPtr ≠ 0⌝ ∗
      (a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗
      ((a + 16#64) ↦₆₄ G.linksHead) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 c.links.length) ∗
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
        G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
      ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
      chainRestSendKeyAt A a G c := by
  have hring :
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
        G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ⊢
      ⌜(G.epochs.zip c.links).length ≤ G.linksCap.toNat ∧
        G.linksCap.toNat * 112 < 2 ^ 63 ∧ G.linksPtr ≠ 0⌝ ∗
        vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
          G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) := by
    unfold vecDequeRingBuf chainEpochSize
    refine Entails.pure_left fun ⟨hle, hcap, hptr, hhead⟩ =>
      Entails.pure_right ⟨hle, hcap, hptr⟩ (Entails.pure_right ⟨hle, hcap, hptr, hhead⟩ (Entails.refl _))
  unfold chainAt vecDequeAt vecDequeHeader chainRestSendKeyAt
  rw [show ⌜G.epochs.length = c.links.length⌝ ∗
      (((a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗ ((a + 16#64) ↦₆₄ G.linksHead) ∗
        ((a + 24#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length)) ∗
       vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
         G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links)) ∗
      vecU8At A (a + 32#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
      ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
      chainParamsAt (a + 72#64) c.params ∗ directionAt (a + 80#64) c.dir ∗ memRegion (a + 84#64) 4 =
    ⌜G.epochs.length = c.links.length⌝ ∗
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
        G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
      ((a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗ ((a + 16#64) ↦₆₄ G.linksHead) ∗
       ((a + 24#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
       ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
       (vecU8At A (a + 32#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
        chainParamsAt (a + 72#64) c.params ∗ directionAt (a + 80#64) c.dir ∗ memRegion (a + 84#64) 4)) by ac_rfl]
  refine Entails.pure_left fun hlen_eq => ?_
  refine Entails.trans (sepConj_mono_left hring) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  have hzip_len : (G.epochs.zip c.links).length = c.links.length := by simp [hlen_eq]
  rw [hzip_len] at hlen_le ⊢
  refine Entails.pure_right ⟨hlen_eq, hlen_le, hcap_lt, hptr⟩ ?_
  rw [show vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
        G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
      ((a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗ ((a + 16#64) ↦₆₄ G.linksHead) ∗
       ((a + 24#64) ↦₆₄ BitVec.ofNat 64 c.links.length) ∗
       ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
       (vecU8At A (a + 32#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
        chainParamsAt (a + 72#64) c.params ∗ directionAt (a + 80#64) c.dir ∗ memRegion (a + 84#64) 4)) =
    (a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗ ((a + 16#64) ↦₆₄ G.linksHead) ∗
      ((a + 24#64) ↦₆₄ BitVec.ofNat 64 c.links.length) ∗
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
        G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
      ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
      (vecU8At A (a + 32#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
       chainParamsAt (a + 72#64) c.params ∗ directionAt (a + 80#64) c.dir ∗ memRegion (a + 84#64) 4) by ac_rfl]
  exact Entails.refl _

theorem chainRepr_pack_sendKey (A : RustAlloc) (a : BitVec 64) (G : ChainGhost) (c : Chain)
    (head' : BitVec 64) (epochs' : List ChainEpochGhost) (links' : List ChainEpoch)
    (sendEpoch' : Epoch) (hlen_eq : epochs'.length = links'.length) :
    (a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗
      ((a + 16#64) ↦₆₄ head') ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 links'.length) ∗
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
        G.linksCap G.linksPtr head' (epochs'.zip links') ∗
      ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ sendEpoch') ∗
      chainRestSendKeyAt A a G c ⊢
      chainRepr A a { c with sendEpoch := sendEpoch', links := links' } := by
  refine Entails.sepExists_right
    { linksCap := G.linksCap, linksPtr := G.linksPtr, linksHead := head',
      epochs := epochs', nextRoot := G.nextRoot } ?_
  have hzip_len : (epochs'.zip links').length = links'.length := by simp [hlen_eq]
  unfold chainAt vecDequeAt vecDequeHeader chainRestSendKeyAt; dsimp only; rw [hzip_len]
  refine Entails.pure_right hlen_eq ?_
  rw [show (a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗
      ((a + 16#64) ↦₆₄ head') ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 links'.length) ∗
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
        G.linksCap G.linksPtr head' (epochs'.zip links') ∗
      ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ sendEpoch') ∗
      (vecU8At A (a + 32#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
       chainParamsAt (a + 72#64) c.params ∗ directionAt (a + 80#64) c.dir ∗ memRegion (a + 84#64) 4) =
    (((a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗
      ((a + 16#64) ↦₆₄ head') ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 links'.length)) ∗
     vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
       G.linksCap G.linksPtr head' (epochs'.zip links')) ∗
    vecU8At A (a + 32#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
    ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ sendEpoch') ∗
    chainParamsAt (a + 72#64) c.params ∗ directionAt (a + 80#64) c.dir ∗ memRegion (a + 84#64) 4 by ac_rfl]
  exact Entails.refl _

/-- Unpack `chainEpochAt A (gce, ce) a` into its 4 `Vec<u8>`s and two `(ctr, pad)` regions for
popping and deallocating in `send_key`. -/
theorem chainEpochAt_unpack_pop (A : RustAlloc) (gce : ChainEpochGhost) (ce : ChainEpoch)
    (a : BitVec 64) :
    chainEpochAt A (gce, ce) a ⊢
      ⌜ce.send.next.length ≤ gce.send.next.cap.toNat ∧ gce.send.next.cap.toNat < 2 ^ 63 ∧ gce.send.next.ptr ≠ 0 ∧
        ce.send.prev.data.length ≤ gce.send.prev.cap.toNat ∧ gce.send.prev.cap.toNat < 2 ^ 63 ∧ gce.send.prev.ptr ≠ 0 ∧
        ce.recv.next.length ≤ gce.recv.next.cap.toNat ∧ gce.recv.next.cap.toNat < 2 ^ 63 ∧ gce.recv.next.ptr ≠ 0 ∧
        ce.recv.prev.data.length ≤ gce.recv.prev.cap.toNat ∧ gce.recv.prev.cap.toNat < 2 ^ 63 ∧ gce.recv.prev.ptr ≠ 0⌝ ∗
      (a ↦₆₄ gce.send.next.cap) ∗ ((a + 8#64) ↦₆₄ gce.send.next.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ce.send.next.length) ∗
      (gce.send.next.ptr ↦ₛ ce.send.next) ∗ vecU8Rest A gce.send.next.cap gce.send.next.ptr ce.send.next.length ∗
      ((a + 24#64) ↦₆₄ gce.send.prev.cap) ∗ ((a + 32#64) ↦₆₄ gce.send.prev.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 ce.send.prev.data.length) ∗
      (gce.send.prev.ptr ↦ₛ ce.send.prev.data) ∗ vecU8Rest A gce.send.prev.cap gce.send.prev.ptr ce.send.prev.data.length ∗
      ((a + 48#64) ↦₃₂ ce.send.ctr) ∗ memRegion (a + 52#64) 4 ∗
      ((a + 56#64) ↦₆₄ gce.recv.next.cap) ∗ ((a + 64#64) ↦₆₄ gce.recv.next.ptr) ∗
      ((a + 72#64) ↦₆₄ BitVec.ofNat 64 ce.recv.next.length) ∗
      (gce.recv.next.ptr ↦ₛ ce.recv.next) ∗ vecU8Rest A gce.recv.next.cap gce.recv.next.ptr ce.recv.next.length ∗
      ((a + 80#64) ↦₆₄ gce.recv.prev.cap) ∗ ((a + 88#64) ↦₆₄ gce.recv.prev.ptr) ∗
      ((a + 96#64) ↦₆₄ BitVec.ofNat 64 ce.recv.prev.data.length) ∗
      (gce.recv.prev.ptr ↦ₛ ce.recv.prev.data) ∗ vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data.length ∗
      ((a + 104#64) ↦₃₂ ce.recv.ctr) ∗ memRegion (a + 108#64) 4 := by
  unfold chainEpochAt chainEpochDirectionAt keyHistoryAt
  dsimp only
  have h1 := vecU8At_unpack A a gce.send.next.cap gce.send.next.ptr ce.send.next
  have h2 := vecU8At_unpack A (a + 24#64) gce.send.prev.cap gce.send.prev.ptr ce.send.prev.data
  have h3 := vecU8At_unpack A (a + 56#64) gce.recv.next.cap gce.recv.next.ptr ce.recv.next
  have h4 := vecU8At_unpack A (a + 56#64 + 24#64) gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2 h3 h4 ⊢
  refine Entails.trans (sepConj_mono
    (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))
    (sepConj_mono h3 (sepConj_mono h4 (Entails.refl _)))) ?_
  simp only [sepConj_assoc]
  refine Entails.pure_left fun ⟨hs_n_le, hs_n_lt, hs_n_ptr⟩ => ?_
  rw [show (a ↦₆₄ gce.send.next.cap) ∗ ((a + 8#64) ↦₆₄ gce.send.next.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ce.send.next.length) ∗
      (gce.send.next.ptr ↦ₛ ce.send.next) ∗ vecU8Rest A gce.send.next.cap gce.send.next.ptr ce.send.next.length ∗
      ⌜ce.send.prev.data.length ≤ gce.send.prev.cap.toNat ∧ gce.send.prev.cap.toNat < 2 ^ 63 ∧ gce.send.prev.ptr ≠ 0⌝ ∗
      ((a + 24#64) ↦₆₄ gce.send.prev.cap) ∗ ((a + 32#64) ↦₆₄ gce.send.prev.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 ce.send.prev.data.length) ∗
      (gce.send.prev.ptr ↦ₛ ce.send.prev.data) ∗ vecU8Rest A gce.send.prev.cap gce.send.prev.ptr ce.send.prev.data.length ∗
      ((a + 48#64) ↦₃₂ ce.send.ctr) ∗ memRegion (a + 52#64) 4 ∗
      ⌜ce.recv.next.length ≤ gce.recv.next.cap.toNat ∧ gce.recv.next.cap.toNat < 2 ^ 63 ∧ gce.recv.next.ptr ≠ 0⌝ ∗
      ((a + 56#64) ↦₆₄ gce.recv.next.cap) ∗ ((a + 64#64) ↦₆₄ gce.recv.next.ptr) ∗
      ((a + 72#64) ↦₆₄ BitVec.ofNat 64 ce.recv.next.length) ∗
      (gce.recv.next.ptr ↦ₛ ce.recv.next) ∗ vecU8Rest A gce.recv.next.cap gce.recv.next.ptr ce.recv.next.length ∗
      ⌜ce.recv.prev.data.length ≤ gce.recv.prev.cap.toNat ∧ gce.recv.prev.cap.toNat < 2 ^ 63 ∧ gce.recv.prev.ptr ≠ 0⌝ ∗
      ((a + 80#64) ↦₆₄ gce.recv.prev.cap) ∗ ((a + 88#64) ↦₆₄ gce.recv.prev.ptr) ∗
      ((a + 96#64) ↦₆₄ BitVec.ofNat 64 ce.recv.prev.data.length) ∗
      (gce.recv.prev.ptr ↦ₛ ce.recv.prev.data) ∗ vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data.length ∗
      ((a + 104#64) ↦₃₂ ce.recv.ctr) ∗ memRegion (a + 108#64) 4 =
    ⌜ce.send.prev.data.length ≤ gce.send.prev.cap.toNat ∧ gce.send.prev.cap.toNat < 2 ^ 63 ∧ gce.send.prev.ptr ≠ 0⌝ ∗
    ⌜ce.recv.next.length ≤ gce.recv.next.cap.toNat ∧ gce.recv.next.cap.toNat < 2 ^ 63 ∧ gce.recv.next.ptr ≠ 0⌝ ∗
    ⌜ce.recv.prev.data.length ≤ gce.recv.prev.cap.toNat ∧ gce.recv.prev.cap.toNat < 2 ^ 63 ∧ gce.recv.prev.ptr ≠ 0⌝ ∗
      ((a ↦₆₄ gce.send.next.cap) ∗ ((a + 8#64) ↦₆₄ gce.send.next.ptr) ∗
       ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ce.send.next.length) ∗
       (gce.send.next.ptr ↦ₛ ce.send.next) ∗ vecU8Rest A gce.send.next.cap gce.send.next.ptr ce.send.next.length ∗
       ((a + 24#64) ↦₆₄ gce.send.prev.cap) ∗ ((a + 32#64) ↦₆₄ gce.send.prev.ptr) ∗
       ((a + 40#64) ↦₆₄ BitVec.ofNat 64 ce.send.prev.data.length) ∗
       (gce.send.prev.ptr ↦ₛ ce.send.prev.data) ∗ vecU8Rest A gce.send.prev.cap gce.send.prev.ptr ce.send.prev.data.length ∗
       ((a + 48#64) ↦₃₂ ce.send.ctr) ∗ memRegion (a + 52#64) 4 ∗
       ((a + 56#64) ↦₆₄ gce.recv.next.cap) ∗ ((a + 64#64) ↦₆₄ gce.recv.next.ptr) ∗
       ((a + 72#64) ↦₆₄ BitVec.ofNat 64 ce.recv.next.length) ∗
       (gce.recv.next.ptr ↦ₛ ce.recv.next) ∗ vecU8Rest A gce.recv.next.cap gce.recv.next.ptr ce.recv.next.length ∗
       ((a + 80#64) ↦₆₄ gce.recv.prev.cap) ∗ ((a + 88#64) ↦₆₄ gce.recv.prev.ptr) ∗
       ((a + 96#64) ↦₆₄ BitVec.ofNat 64 ce.recv.prev.data.length) ∗
       (gce.recv.prev.ptr ↦ₛ ce.recv.prev.data) ∗ vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data.length ∗
       ((a + 104#64) ↦₃₂ ce.recv.ctr) ∗ memRegion (a + 108#64) 4) by ac_rfl]
  refine Entails.pure_left fun ⟨hs_p_le, hs_p_lt, hs_p_ptr⟩ =>
    Entails.pure_left fun ⟨hr_n_le, hr_n_lt, hr_n_ptr⟩ =>
    Entails.pure_left fun ⟨hr_p_le, hr_p_lt, hr_p_ptr⟩ =>
      Entails.pure_right ⟨hs_n_le, hs_n_lt, hs_n_ptr, hs_p_le, hs_p_lt, hs_p_ptr,
        hr_n_le, hr_n_lt, hr_n_ptr, hr_p_le, hr_p_lt, hr_p_ptr⟩ (Entails.refl _)

/-- Fold a `ChainEpochDirection` slot (6 64-bit header cells + `ctr` + 4B padding) into `memRegion a 56`. -/
theorem chainEpochDirSlot_entails_memRegion_56 (a u0 u1 u2 u3 u4 u5 : BitVec 64) (d0 : BitVec 32) :
    (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
      ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5) ∗
      ((a + 48#64) ↦₃₂ d0) ∗ memRegion (a + 52#64) 4 ⊢
      memRegion a 56 := by
  rw [ChainNewFacts.memRegion_56_ced_split a]
  exact Entails.sepExists_right d0 (Entails.sepExists_right u0 (Entails.sepExists_right u1
    (Entails.sepExists_right u2 (Entails.sepExists_right u3 (Entails.sepExists_right u4
      (Entails.sepExists_right u5 (Entails.refl _)))))))

/-- Fold a popped `ChainEpoch` slot (after deallocating its 4 `Vec<u8>` buffers) into `memRegion a 112`. -/
theorem chainEpochSlot_entails_memRegion_112 (a u0 u1 u2 u3 u4 u5 w0 w1 w2 w3 w4 w5 : BitVec 64)
    (d0 d1 : BitVec 32) :
    (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
      ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5) ∗
      ((a + 48#64) ↦₃₂ d0) ∗ memRegion (a + 52#64) 4 ∗
      ((a + 56#64) ↦₆₄ w0) ∗ ((a + 64#64) ↦₆₄ w1) ∗ ((a + 72#64) ↦₆₄ w2) ∗
      ((a + 80#64) ↦₆₄ w3) ∗ ((a + 88#64) ↦₆₄ w4) ∗ ((a + 96#64) ↦₆₄ w5) ∗
      ((a + 104#64) ↦₃₂ d1) ∗ memRegion (a + 108#64) 4 ⊢
      memRegion a 112 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 56) (k := 56) (b' := a + 56#64) rfl (by bv_omega) (by decide)]
  have h1 := chainEpochDirSlot_entails_memRegion_56 a u0 u1 u2 u3 u4 u5 d0
  have h2 := chainEpochDirSlot_entails_memRegion_56 (a + 56#64) w0 w1 w2 w3 w4 w5 d1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2
  rw [show (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
      ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5) ∗
      ((a + 48#64) ↦₃₂ d0) ∗ memRegion (a + 52#64) 4 ∗
      ((a + 56#64) ↦₆₄ w0) ∗ ((a + 64#64) ↦₆₄ w1) ∗ ((a + 72#64) ↦₆₄ w2) ∗
      ((a + 80#64) ↦₆₄ w3) ∗ ((a + 88#64) ↦₆₄ w4) ∗ ((a + 96#64) ↦₆₄ w5) ∗
      ((a + 104#64) ↦₃₂ d1) ∗ memRegion (a + 108#64) 4 =
    ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
     ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5) ∗
     ((a + 48#64) ↦₃₂ d0) ∗ memRegion (a + 52#64) 4) ∗
    (((a + 56#64) ↦₆₄ w0) ∗ ((a + 64#64) ↦₆₄ w1) ∗ ((a + 72#64) ↦₆₄ w2) ∗
     ((a + 80#64) ↦₆₄ w3) ∗ ((a + 88#64) ↦₆₄ w4) ∗ ((a + 96#64) ↦₆₄ w5) ∗
     ((a + 104#64) ↦₃₂ d1) ∗ memRegion (a + 108#64) 4) by ac_rfl]
  exact sepConj_mono h1 h2

theorem vecDequeRingBuf_get_physIdx (A : RustAlloc) (cap ptr head : BitVec 64)
    (xs : List (ChainEpochGhost × ChainEpoch)) {i : Nat}
    (hlen : xs.length ≤ cap.toNat) (hi : i < xs.length) :
    let s := vecDequePhysIdx head.toNat cap.toNat i
    vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head xs ⊢
      ⌜head.toNat < cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      A.live ptr (cap.toNat * 112) 8 ∗
      chainEpochAt A xs[i] (ptr + BitVec.ofNat 64 (s * 112)) ∗
      vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr xs s := by
  intro s
  have hcap_ne : cap ≠ 0 := by
    intro h0; subst h0; have : i < 0 := Nat.lt_of_lt_of_le hi hlen; omega
  unfold vecDequeRingBuf chainEpochSize chainEpochAlign
  simp only [hcap_ne, ↓reduceIte]
  refine Entails.pure_left fun ⟨_, hcap_lt, hptr, hhead⟩ => ?_
  rw [vecDequeSlotsAt_get_physIdx (chainEpochAt A) 112 cap.toNat head.toNat ptr xs hhead hlen hi]
  rw [show A.live ptr (cap.toNat * 112) 8 ∗
      (chainEpochAt A xs[i] (ptr + BitVec.ofNat 64 (s * 112)) ∗
        vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr xs s) =
    A.live ptr (cap.toNat * 112) 8 ∗
      chainEpochAt A xs[i] (ptr + BitVec.ofNat 64 (s * 112)) ∗
      vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr xs s by ac_rfl]
  exact Entails.pure_right ⟨hhead, hcap_lt, hptr⟩ (Entails.refl _)

theorem vecDequeRingBuf_set_physIdx (A : RustAlloc) (cap ptr head : BitVec 64)
    (xs : List (ChainEpochGhost × ChainEpoch)) {i : Nat} (x' : ChainEpochGhost × ChainEpoch)
    (hhead : head.toNat < cap.toNat) (hcap_lt : cap.toNat * 112 < 2 ^ 63)
    (hptr : ptr ≠ 0#64) (hlen : xs.length ≤ cap.toNat) (hi : i < xs.length) :
    let s := vecDequePhysIdx head.toNat cap.toNat i
    A.live ptr (cap.toNat * 112) 8 ∗
      chainEpochAt A x' (ptr + BitVec.ofNat 64 (s * 112)) ∗
      vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr xs s ⊢
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head (xs.set i x') := by
  intro s
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; simp at hhead
  have hlen_set : (xs.set i x').length ≤ cap.toNat := by simp [hlen]
  unfold vecDequeRingBuf chainEpochSize chainEpochAlign
  simp only [hcap_ne, ↓reduceIte]
  refine Entails.pure_right ⟨hlen_set, hcap_lt, hptr, hhead⟩ ?_
  rw [← vecDequeSlotsAt_set_physIdx (chainEpochAt A) 112 cap.toNat head.toNat ptr xs x' hhead hlen hi]
  exact Entails.refl _

theorem vecDequePhysIdx_one_lt {head cap : Nat} (hhead : head < cap) :
    vecDequePhysIdx head cap 1 < cap := by
  unfold vecDequePhysIdx; split_ifs <;> omega

theorem vecDequeRingBuf_pop_front (A : RustAlloc) (cap ptr head : BitVec 64)
    (x0 : ChainEpochGhost × ChainEpoch) (xs : List (ChainEpochGhost × ChainEpoch))
    (hhead : head.toNat < cap.toNat) (hcap_lt : cap.toNat * 112 < 2 ^ 63)
    (hptr : ptr ≠ 0#64) (hlen : (x0 :: xs).length ≤ cap.toNat) :
    A.live ptr (cap.toNat * 112) 8 ∗
      memRegion (ptr + BitVec.ofNat 64 (head.toNat * 112)) 112 ∗
      vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr (x0 :: xs) head.toNat ⊢
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr
        (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)) xs := by
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; simp at hhead
  have hlen_xs : xs.length ≤ cap.toNat := by simp only [List.length_cons] at hlen; omega
  have hphys_lt : vecDequePhysIdx head.toNat cap.toNat 1 < cap.toNat := vecDequePhysIdx_one_lt hhead
  have hphys_lt64 : vecDequePhysIdx head.toNat cap.toNat 1 < 18446744073709551616 := by omega
  have hhead1_toNat : (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)).toNat =
      vecDequePhysIdx head.toNat cap.toNat 1 := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hphys_lt64]
  unfold vecDequeRingBuf chainEpochSize chainEpochAlign
  simp only [hcap_ne, ↓reduceIte, hhead1_toNat]
  refine Entails.pure_right ⟨hlen_xs, hcap_lt, hptr, hphys_lt⟩ ?_
  rw [← vecDequeSlotsAt_pop_front (chainEpochAt A) 112 cap.toNat head.toNat ptr x0 xs hhead hlen]
  exact Entails.refl _

end ChainSendKeyFacts

end CryptoVerification.SpqrV1.ChainProofs

