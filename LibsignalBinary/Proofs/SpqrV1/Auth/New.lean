/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.Update
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep
public meta import ProofLib.SepLogic.WP.ControlTactics -- shake: keep

/-!
# Verification of `<spqr::authenticator::Authenticator>::new`

Proves that `<spqr::authenticator::Authenticator>::new` (`0x5ddfc`, Block `340`, 48 instructions)
allocates two zeroed 32-byte key buffers, delegates to `Authenticator::update` with epoch `1`,
writes `Authenticator.new F rootKey 1#64` to the output pointer, and drops the consumed `root_key`
`Vec<u8>`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout
open DoReserveNorm
open UpdateFacts NextKeyInternalFacts AgreeStateSimp

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x58a04 → 0x58ac0]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Stack Budget and Ghost Inputs -/

/-- Stack budget for `<spqr::authenticator::Authenticator>::new`:
`96` bytes (`0x60`) own frame + `authUpdateStackX` (`160 + extHookStack`) = `256 + extHookStack`. -/
abbrev authNewStackX : Nat := 96 + authUpdateStackX

/-- Ghost inputs for `<spqr::authenticator::Authenticator>::new` with pinned `root_key: Vec<u8>`. -/
structure AuthNewPinnedGhost where
  /-- Output pointer (`x0`) to 48 bytes for the returned `Authenticator`. -/
  outA : BitVec 64
  /-- Input pointer (`x1`) to `root_key: Vec<u8>` (`24` bytes, consumed by value). -/
  rkVecA : BitVec 64
  /-- Ghost `(cap, ptr)` pin for the consumed `root_key: Vec<u8>`. -/
  rkPin : LibsignalSessionRepr.VecPin
  rootKey : Bytes

/-- Ghost inputs for `<spqr::authenticator::Authenticator>::new` with unpinned `root_key: Vec<u8>`. -/
structure AuthNewGhost where
  /-- Output pointer (`x0`) to 48 bytes for the returned `Authenticator`. -/
  outA : BitVec 64
  /-- Input pointer (`x1`) to `root_key: Vec<u8>` (`24` bytes, consumed by value). -/
  rkVecA : BitVec 64
  rootKey : Bytes

/-- Pinned specification for `<spqr::authenticator::Authenticator>::new` (`0x5ddfc`):
consumes `vecU8At A x.rkVecA x.rkPin.cap x.rkPin.ptr x.rootKey` (deallocating its heap buffer and
leaving `vecHeader x.rkVecA x.rkPin.cap x.rkPin.ptr (BitVec.ofNat 64 x.rootKey.length)` on the stack)
and writes `authenticatorAt A x.outA (Authenticator.new F x.rootKey 1#64)` to `x.outA`. -/
def authNewPinnedSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthNewPinnedGhost where
  pre x s :=
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.rkVecA ∧
      32 + x.rootKey.length < 2 ^ 63⌝ ∗
      memRegion x.outA authenticatorSize ∗
      vecU8At A x.rkVecA x.rkPin.cap x.rkPin.ptr x.rootKey ∗
      A.pool ∗
      stackAt s.sp authNewStackX
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorAt A x.outA (Authenticator.new F x.rootKey 1#64) ∗
      vecHeader x.rkVecA x.rkPin.cap x.rkPin.ptr (BitVec.ofNat 64 x.rootKey.length) ∗
      A.pool ∗
      stackAt s0.sp authNewStackX
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Unpinned specification for `<spqr::authenticator::Authenticator>::new` (`0x5ddfc`):
consumes `vecU8 A x.rkVecA x.rootKey` (deallocating its heap buffer and leaving `memRegion x.rkVecA 24`
at `x.rkVecA`) and writes `authenticatorAt A x.outA (Authenticator.new F x.rootKey 1#64)` to `x.outA`. -/
def authNewSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthNewGhost where
  pre x s :=
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.rkVecA ∧
      32 + x.rootKey.length < 2 ^ 63⌝ ∗
      memRegion x.outA authenticatorSize ∗
      vecU8 A x.rkVecA x.rootKey ∗
      A.pool ∗
      stackAt s.sp authNewStackX
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorAt A x.outA (Authenticator.new F x.rootKey 1#64) ∗
      memRegion x.rkVecA 24 ∗
      A.pool ∗
      stackAt s0.sp authNewStackX
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def AuthNewOkX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authNewName)
    ((authNewSpec F A).inImage img)

/-- Stack budget for `<spqr::authenticator::Authenticator>::new` under `CliExternsOk`:
`96` bytes (`0x60`) own frame + `authUpdateStackExt` (`17776` B) = `17872` B. -/
abbrev authNewStackExt : Nat := 96 + authUpdateStackExt

def authNewPinnedSpecExt (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthNewPinnedGhost where
  pre x s := ⌜s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.rkVecA ∧ 32 + x.rootKey.length < 2 ^ 63⌝ ∗
    memRegion x.outA authenticatorSize ∗ vecU8At A x.rkVecA x.rkPin.cap x.rkPin.ptr x.rootKey ∗
    A.pool ∗ stackAt s.sp authNewStackExt
  post x s0 sf := ⌜sf.trace = s0.trace⌝ ∗
    authenticatorAt A x.outA (Authenticator.new F x.rootKey 1#64) ∗
    vecHeader x.rkVecA x.rkPin.cap x.rkPin.ptr (BitVec.ofNat 64 x.rootKey.length) ∗
    A.pool ∗ stackAt s0.sp authNewStackExt
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def authNewSpecExt (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthNewGhost where
  pre x s := ⌜s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.rkVecA ∧ 32 + x.rootKey.length < 2 ^ 63⌝ ∗
    memRegion x.outA authenticatorSize ∗ vecU8 A x.rkVecA x.rootKey ∗
    A.pool ∗ stackAt s.sp authNewStackExt
  post x s0 sf := ⌜sf.trace = s0.trace⌝ ∗
    authenticatorAt A x.outA (Authenticator.new F x.rootKey 1#64) ∗
    memRegion x.rkVecA 24 ∗ A.pool ∗ stackAt s0.sp authNewStackExt
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def AuthNewOkExt (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authNewName)
    ((authNewSpecExt F A).inImage img)

/-! ## Code Offset and Stack / Memory Splitting Lemmas -/

namespace NewFacts

theorem authNew_fnOff : libsignalSessionCode.fnOff authNewName = 0x58a04 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x58a04

theorem stackAt_authNewX_split (sp : BitVec 64) :
    stackAt sp authNewStackX =
      stackAt (sp - 96#64) authUpdateStackX ∗
        (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
         ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
         ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
          ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗
          ((sp - 80#64) ↦₆₄ w2) ∗ ((sp - 72#64) ↦₆₄ w3) ∗
          ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
          ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗
          ((sp - 32#64) ↦₆₄ w8) ∗ ((sp - 24#64) ↦₆₄ w9) ∗
          ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11)) := by
  change memRegion (sp - BitVec.ofNat 64 16640) 16640 =
    memRegion (sp - 96#64 - BitVec.ofNat 64 16544) 16544 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16640) (n := 16544) (k := 96)
      (b' := sp - 96#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - BitVec.ofNat 64 16640) 16544 ∗
    memRegion (sp - 96#64) (8 * 12) = _
  rw [ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  have hsub : sp - 96#64 - BitVec.ofNat 64 16544 = sp - BitVec.ofNat 64 16640 := by bv_kernel
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗
        ((sp - 80#64) ↦₆₄ w2) ∗ ((sp - 72#64) ↦₆₄ w3) ∗
        ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
        ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗
        ((sp - 32#64) ↦₆₄ w8) ∗ ((sp - 24#64) ↦₆₄ w9) ∗
        ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11)) := by
    cells_unfold
  rw [hsub, hc12]

theorem stackAt_authUpdateX_split_extHook (sp : BitVec 64) :
    stackAt sp authUpdateStackX =
      memRegion (sp - BitVec.ofNat 64 16544) 160 ∗ stackAt sp extHookStack := by
  change memRegion (sp - BitVec.ofNat 64 16544) 16544 =
    memRegion (sp - BitVec.ofNat 64 16544) 160 ∗
      memRegion (sp - BitVec.ofNat 64 16384) 16384
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16544) (n := 160) (k := 16384)
    (b' := sp - BitVec.ofNat 64 16384) rfl (by bv_omega) (by decide)

theorem stackAt_authNewX_split_extHook (sp : BitVec 64) :
    stackAt sp authNewStackX =
      memRegion (sp - BitVec.ofNat 64 16640) 256 ∗ stackAt sp extHookStack := by
  change memRegion (sp - BitVec.ofNat 64 16640) 16640 =
    memRegion (sp - BitVec.ofNat 64 16640) 256 ∗
      memRegion (sp - BitVec.ofNat 64 16384) 16384
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16640) (n := 256) (k := 16384)
    (b' := sp - BitVec.ofNat 64 16384) rfl (by bv_omega) (by decide)

theorem rejoin_stack_authNewX (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) :
    stackAt (sp - 96#64) authUpdateStackX ∗
      ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗
      ((sp - 80#64) ↦₆₄ w2) ∗ ((sp - 72#64) ↦₆₄ w3) ∗
      ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
      ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗
      ((sp - 32#64) ↦₆₄ w8) ∗ ((sp - 24#64) ↦₆₄ w9) ∗
      ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11) ⊢
      stackAt sp authNewStackX := by
  rw [stackAt_authNewX_split sp]
  exact sepConj_mono_right
    (Entails.sepExists_right w0 <| Entails.sepExists_right w1 <|
      Entails.sepExists_right w2 <| Entails.sepExists_right w3 <|
      Entails.sepExists_right w4 <| Entails.sepExists_right w5 <|
      Entails.sepExists_right w6 <| Entails.sepExists_right w7 <|
      Entails.sepExists_right w8 <| Entails.sepExists_right w9 <|
      Entails.sepExists_right w10 <| Entails.sepExists_right w11 <| Entails.refl _)

theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_48_cells (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        (a ↦₆₄ w5) ∗ ((a + 8#64) ↦₆₄ w4) ∗ ((a + 16#64) ↦₆₄ w3) ∗
        ((a + 24#64) ↦₆₄ w2) ∗ ((a + 32#64) ↦₆₄ w1) ∗ ((a + 40#64) ↦₆₄ w0)) := by
  rw [ProofLib.memRegion_split a 24 24 (by decide), memRegion_24, memRegion_24]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]

/-- Heap and pure invariant portion of `authenticatorPinAt A g p auth` (independent of `p`). -/
def authenticatorHeapAt (A : RustAlloc) (g : AuthenticatorGhost) (auth : Authenticator) : SepProp :=
  ⌜auth.rootKey.length ≤ g.rootKey.cap.toNat ∧ g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0⌝ ∗
    (if g.rootKey.cap = 0 then emp
     else A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗ (g.rootKey.ptr ↦ₛ auth.rootKey) ∗
       memRegion (g.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (g.rootKey.cap.toNat - auth.rootKey.length)) ∗
    ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
    (if g.macKey.cap = 0 then emp
     else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗ (g.macKey.ptr ↦ₛ auth.macKey) ∗
       memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length))

theorem authenticatorPinAt_eq_cells_heap (A : RustAlloc) (g : AuthenticatorGhost)
    (p : BitVec 64) (auth : Authenticator) :
    authenticatorPinAt A g p auth =
      (p ↦₆₄ g.rootKey.cap) ∗
      ((p + 8#64) ↦₆₄ g.rootKey.ptr) ∗
      ((p + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((p + 24#64) ↦₆₄ g.macKey.cap) ∗
      ((p + 32#64) ↦₆₄ g.macKey.ptr) ∗
      ((p + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      authenticatorHeapAt A g auth := by
  unfold authenticatorPinAt authenticatorHeapAt vecU8At vecHeader
  have h24 : p + 0x18#64 = p + 24#64 := rfl
  have h32 : p + 0x18#64 + 8#64 = p + 32#64 := by bv_omega
  have h40 : p + 0x18#64 + 16#64 = p + 40#64 := by bv_omega
  rw [h32, h40, h24]
  ac_rfl

theorem authenticatorPinAt_at_sp_eq_cells_heap (A : RustAlloc) (g : AuthenticatorGhost)
    (sp : BitVec 64) (auth : Authenticator) :
    authenticatorPinAt A g (sp - 96#64) auth =
      ((sp - 96#64) ↦₆₄ g.rootKey.cap) ∗
      ((sp - 88#64) ↦₆₄ g.rootKey.ptr) ∗
      ((sp - 80#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((sp - 72#64) ↦₆₄ g.macKey.cap) ∗
      ((sp - 64#64) ↦₆₄ g.macKey.ptr) ∗
      ((sp - 56#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      authenticatorHeapAt A g auth := by
  rw [authenticatorPinAt_eq_cells_heap]
  have e1 : sp - 96#64 + 8#64 = sp - 88#64 := by bv_omega
  have e2 : sp - 96#64 + 16#64 = sp - 80#64 := by bv_omega
  have e3 : sp - 96#64 + 24#64 = sp - 72#64 := by bv_omega
  have e4 : sp - 96#64 + 32#64 = sp - 64#64 := by bv_omega
  have e5 : sp - 96#64 + 40#64 = sp - 56#64 := by bv_omega
  rw [e1, e2, e3, e4, e5]

theorem authenticatorAt_sp_init (A : RustAlloc) (sp ptr1 ptr2 : BitVec 64)
    (hptr1 : ptr1 ≠ 0#64) (hptr2 : ptr2 ≠ 0#64) :
    ((sp - 96#64) ↦₆₄ 32#64) ∗ ((sp - 88#64) ↦₆₄ ptr1) ∗ ((sp - 80#64) ↦₆₄ 32#64) ∗
      ((sp - 72#64) ↦₆₄ 32#64) ∗ ((sp - 64#64) ↦₆₄ ptr2) ∗ ((sp - 56#64) ↦₆₄ 32#64) ∗
      A.live ptr1 32 1 ∗ (ptr1 ↦ₛ List.replicate 32 0#8) ∗
      A.live ptr2 32 1 ∗ (ptr2 ↦ₛ List.replicate 32 0#8) ⊢
      authenticatorAt A (sp - 96#64)
        { rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 } := by
  have e1 : sp - 88#64 = sp - 96#64 + 8#64 := by bv_omega
  have e2 : sp - 80#64 = sp - 96#64 + 16#64 := by bv_omega
  have e3 : sp - 72#64 = sp - 96#64 + 24#64 := by bv_omega
  have e4 : sp - 64#64 = sp - 96#64 + 32#64 := by bv_omega
  have e5 : sp - 56#64 = sp - 96#64 + 40#64 := by bv_omega
  rw [e1, e2, e3, e4, e5]
  exact authenticatorAt_of_32_32 A (sp - 96#64) ptr1 ptr2
    (List.replicate 32 0#8) (List.replicate 32 0#8) (by simp) (by simp) hptr1 hptr2

theorem vecHeader_entails_memRegion_24 (v cap ptr len : BitVec 64) :
    vecHeader v cap ptr len ⊢ memRegion v 24 := by
  unfold vecHeader
  rw [memRegion_24 v]
  exact Entails.sepExists_right len
    (Entails.sepExists_right ptr
      (Entails.sepExists_right cap (Entails.refl _)))

theorem false_sepConj_entails {T Q : SepProp} : ⌜False⌝ ∗ T ⊢ Q :=
  Entails.pure_left False.elim

open Lean Elab Tactic Meta in
meta def wppCallMidCoreNew (lemId : Ident) (hcall a hF : Term) : TacticM Unit := do
  let hcallCopyId ← freshIdent `hcall_copy
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    have $hcallCopyId := $hcall
    apply ($lemId $hcallCopyId (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wppCallMidCoreNew: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  let id1 := mkIdent ``withStack
  let id2 := mkIdent ``sessionShimSpec
  let id3 := mkIdent ``rustAllocZeroedSpecWithStack
  let id4 := mkIdent ``authUpdateSpec
  let idPanic := mkIdent ``NextKeyInternalFacts.onPanic_entails_of_trace_eq
  let idFalse := mkIdent ``false_sepConj_entails
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [$id1:ident, $id2:ident, $id3:ident, $id4:ident]
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR'
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm, *]
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcallCopyId)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; (try dsimp only [$id1:ident, $id2:ident, $id3:ident, $id4:ident]); intro _; first
      | exact $idPanic:ident (by wp_norm_lhs)
      | exact $idFalse:ident)
    wp_focus_close (wp_unfold_specs; (try dsimp only [$id1:ident, $id2:ident, $id3:ident, $id4:ident]); exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    try clear $hcallCopyId
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
    try dsimp only [$id1:ident, $id2:ident, $id3:ident, $id4:ident]
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
elab "wpp_call_lsCallInv_new " hcall:term:max a:term:max hF:term:max : tactic =>
  wppCallMidCoreNew (mkIdent ``NextKeyInternalFacts.SepWPp.call_allowPanic_lsCallInv_mid) hcall a hF

end NewFacts

open NewFacts

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length updateLabel_length replicate_32_zero_length
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  authNew_fnOff authUpdate_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  libsignalSessionCode_fnOff_0x58a04 libsignalSessionCode_fnOff_0x58ac4
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")

/-! ## Main Proofs of `<spqr::authenticator::Authenticator>::new` -/

namespace NewFacts

def authNewPinnedSpecAt (stk : Nat) (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthNewPinnedGhost where
  pre x s := ⌜s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.rkVecA ∧ 32 + x.rootKey.length < 2 ^ 63⌝ ∗
    memRegion x.outA authenticatorSize ∗ vecU8At A x.rkVecA x.rkPin.cap x.rkPin.ptr x.rootKey ∗
    A.pool ∗ stackAt s.sp stk
  post x s0 sf := ⌜sf.trace = s0.trace⌝ ∗
    authenticatorAt A x.outA (Authenticator.new F x.rootKey 1#64) ∗
    vecHeader x.rkVecA x.rkPin.cap x.rkPin.ptr (BitVec.ofNat 64 x.rootKey.length) ∗
    A.pool ∗ stackAt s0.sp stk
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def authNewUpdateSpecAt (stk : Nat) (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthUpdateGhost where
  pre x s := ⌜s.readReg64 .x0 = x.selfA ∧ s.readReg64 .x1 = x.ep ∧
    s.readReg64 .x2 = x.kA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.k.length ∧
    x.auth.rootKey.length + x.k.length < 2 ^ 63⌝ ∗
    authenticatorAt A x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗ A.pool ∗ stackAt s.sp stk
  post x s0 sf := ⌜sf.trace = s0.trace⌝ ∗
    authenticatorAt A x.selfA (x.auth.update F x.ep x.k) ∗ bytesAt x.kRO x.kA x.k ∗
    A.pool ∗ stackAt s0.sp stk
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def AuthNewUpdateOkAt (stk : Nat) (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
    ((authNewUpdateSpecAt stk F A).inImage img)

def authNewSpecAt (stk : Nat) (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec AuthNewGhost where
  pre x s := ⌜s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.rkVecA ∧ 32 + x.rootKey.length < 2 ^ 63⌝ ∗
    memRegion x.outA authenticatorSize ∗ vecU8 A x.rkVecA x.rootKey ∗ A.pool ∗ stackAt s.sp stk
  post x s0 sf := ⌜sf.trace = s0.trace⌝ ∗
    authenticatorAt A x.outA (Authenticator.new F x.rootKey 1#64) ∗
    memRegion x.rkVecA 24 ∗ A.pool ∗ stackAt s0.sp stk
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end NewFacts

set_option maxHeartbeats 1600000 in
private theorem authNewPinned_ok_gen {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)} {totalStk updStk extra : Nat}
    (hsplit_top : ∀ sp, stackAt sp totalStk =
      memRegion (sp - BitVec.ofNat 64 totalStk) extra ∗ stackAt sp authNewStackX)
    (hjoin_upd : ∀ sp, memRegion (sp - BitVec.ofNat 64 totalStk) extra ∗
      stackAt (sp - 96#64) authUpdateStackX = stackAt (sp - 96#64) updStk)
    (_himg : Obj.Loads libsignalSessionImage img)
    (hupdate : AuthNewUpdateOkAt updStk img F A ext)
    (hA : AllocContractsX img A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authNewName)
      ((authNewPinnedSpecAt totalStk F A).inImage img) := by
  unfold tripleRatchetProgAtExt at *
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff authNewName = 0x58a04 := authNew_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x58a04 192
  have h_update := sub_ok_at_rebase (name := authNewName) (callee := authUpdateName)
    (k := num% (0x58ac4 - 0x58a04)) (by rw [authNew_fnOff, authUpdate_fnOff]) hupdate
  have h_shim := sub_ok_at_rebase (name := authNewName) (callee := shimName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x58a04))
    (by rw [authNew_fnOff, shim_fnOff])
    (hA.shim extHookStack (Nat.le_refl _) (by decide))
  have h_allocZeroed := sub_ok_at_rebase (name := authNewName) (callee := allocZeroedName)
    (k := num% (ls_off% "__rustc::__rust_alloc_zeroed" - 0x58a04))
    (by rw [authNew_fnOff, allocZeroed_fnOff]) hallocZeroed
  have h_dealloc := sub_ok_at_rebase (name := authNewName) (callee := deallocName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x58a04))
    (by rw [authNew_fnOff, dealloc_fnOff]) hA.dealloc
  have h_panic := panic_at_handle_error_ext img.base ext authNewName
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x58a04))
    (by rw [authNew_fnOff, handleError_fnOff])
  dsimp only [tripleRatchetProgAtExt] at h_panic
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr authNewName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear hupdate hA hallocZeroed hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      authNewName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rcases x with ⟨outA, rkVecA, rkPin, rootKey⟩
  dsimp only [authNewPinnedSpecAt] at hpre h_1 h_2 h_3 h_4 h ⊢
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  subst h_3 h_4
  refine SepWPp.rw_pre (by rw [hsplit_top s0.sp, stackAt_authNewX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x58a04)) hinv0 ?_
  refine SepWP.fold (Entails.of_eq (stackAt_authUpdateX_split_extHook (s0.sp - 96#64))) (by sep_focus) ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_inImage_mid h_shim () hinv1
  refine SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
  refine SepWPp.of_sepWP_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc_zeroed" - 0x58a04)) hF_sf ?_
  wp_steps
  have hstack_sf : stackAt (s0.sp - 96#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 96#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  have hlay32 : LayoutOk 32 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  wpp_call_inImage_mid h_allocZeroed (32, 1) hinv2
  by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0#64
  · conv => arg 4; simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x58a04))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    exact allowPanic_panicked_update
      (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
    conv => arg 4; simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, htr2⟩
    refine SepWPp.of_sepWP_inImage
      (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x58a04)) hF_sf_1 ?_
    wp_steps
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
      rw [‹sf_1.sp = sf.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv3
    wpp_call_inImage_mid h_shim () hinv3
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr3 => ?_
    refine SepWPp.of_sepWP_inImage
      (mid := entry + bv% (ls_off% "__rustc::__rust_alloc_zeroed" - 0x58a04)) hF_sf_2 ?_
    wp_steps
    have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
      rw [‹sf_2.sp = sf_1.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv4
    wpp_call_inImage_mid h_allocZeroed (32, 1) hinv4
    by_cases hoom2 : sf_3.readReg64 Reg.x0 = 0#64
    · conv => arg 4; simp only [hoom2, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr4 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x58a04))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      exact allowPanic_panicked_update
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom2_beq : (sf_3.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom2
      conv => arg 4; simp only [hoom2, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr4⟩
      refine SepWPp.of_sepWP_inImage (mid := entry + bv% (0x58ac4 - 0x58a04)) hF_sf_3 ?_
      refine SepWP.fold
        (vecU8At_expose_entails A (s0.readReg64 (.gpr 1#5)) rkPin.cap rkPin.ptr rootKey)
        (by sep_focus) ?_
      refine SepWP.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hrk_le, hrk_lt, hrk_ptr⟩
      wp_steps
      refine SepWP.fold
        (authenticatorAt_sp_init A s0.sp (sf_1.readReg64 Reg.x0) (sf_3.readReg64 Reg.x0) hoom1 hoom2)
        (by sep_focus) ?_
      have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt (s0.sp - 96#64) extHookStack := by
        rw [‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 96#64›]
      refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (stackAt_authUpdateX_split_extHook (s0.sp - 96#64)).symm) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (hjoin_upd s0.sp)) (by sep_focus) ?_
      have hstack_upd : stackAt (s0.sp - 96#64) updStk = stackAt sf_3.sp updStk := by
        rw [‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 96#64›]
      refine SepWP.fold (Entails.of_eq hstack_upd) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv5
      have hlen_init :
          ({ rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 } : Authenticator).rootKey.length +
            rootKey.length < 2 ^ 63 := by
        simpa using h
      wpp_call_inImage_mid h_update
        (⟨s0.sp - 96#64,
          { rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 },
          1#64, false, rkPin.ptr, rootKey⟩ : AuthUpdateGhost)
        hinv5
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr5 => ?_
      apply SepWPp.of_sepWP_ret
      have hnew_eq :
          authenticatorAt A (s0.sp - 96#64)
            (Authenticator.update F { rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 } 1#64 rootKey) =
          authenticatorAt A (s0.sp - 96#64) (Authenticator.new F rootKey 1#64) := rfl
      refine SepWP.fold (Entails.of_eq hnew_eq) (by sep_focus) ?_
      refine SepWP.fold
        (Entails.of_eq (authenticatorAt_eq_exists_pinned A (s0.sp - 96#64)
          (Authenticator.new F rootKey 1#64)))
        (by sep_focus) ?_
      sep_elim_exists
      rename_i g_out
      refine SepWP.fold
        (Entails.of_eq (authenticatorPinAt_at_sp_eq_cells_heap A g_out s0.sp
          (Authenticator.new F rootKey 1#64)))
        (by sep_focus) ?_
      refine SepWP.fold
        (Entails.of_eq (memRegion_48_cells (s0.readReg64 (.gpr 0#5))))
        (by sep_focus) ?_
      sep_elim_exists
      refine SepWP.fold (vecBufAt_fold A rkPin.cap rkPin.ptr rootKey) (by sep_focus) ?_
      have hstack_sf4 : stackAt sf_3.sp updStk =
          memRegion (s0.sp - BitVec.ofNat 64 totalStk) extra ∗ stackAt (s0.sp - 96#64) authUpdateStackX := by
        rw [‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 96#64›,
          ← hjoin_upd s0.sp]
      refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
      by_cases hcap_rk : rkPin.cap = 0#64
      · refine SepWP.fold (vecBufAt_of_cap_zero A hcap_rk hrk_le) (by sep_focus) ?_
        simp only [hcap_rk]
        wp_steps
        refine SepWP.fold
          (Entails.of_eq (authenticatorPinAt_eq_cells_heap A g_out (s0.readReg64 (.gpr 0#5))
            (Authenticator.new F rootKey 1#64)).symm)
          (by sep_focus) ?_
        refine SepWP.fold
          (authenticatorPinAt_entails_authenticatorAt A g_out (s0.readReg64 (.gpr 0#5))
            (Authenticator.new F rootKey 1#64))
          (by sep_focus) ?_
        refine SepWP.fold
          (rejoin_stack_authNewX s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (hsplit_top s0.sp).symm) (by sep_focus) ?_
        dsimp only [vecHeader]
        wp_done
      · have hcap_rk_beq : (rkPin.cap == 0#64) = false := beq_false_of_ne hcap_rk
        refine SepWP.fold (vecBufAt_of_cap_ne_zero A hcap_rk hrk_le hrk_lt) (by sep_focus) ?_
        refine SepWP.pure_left_focus _ (by sep_focus) ?_
        intro hrk_lay
        have ⟨_, _, _⟩ := hrk_lay
        apply SepWP.seq_inImage
          (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x58a04)) hF_sf_4
        wp_steps
        refine SepWP.fold
          (Entails.of_eq (authenticatorPinAt_eq_cells_heap A g_out (s0.readReg64 (.gpr 0#5))
            (Authenticator.new F rootKey 1#64)).symm)
          (by sep_focus) ?_
        refine SepWP.fold
          (authenticatorPinAt_entails_authenticatorAt A g_out (s0.readReg64 (.gpr 0#5))
            (Authenticator.new F rootKey 1#64))
          (by sep_focus) ?_
        refine SepWP.fold
          (rejoin_stack_authNewX s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus) ?_
        refine SepWP.fold
          (Entails.of_eq (stackAt_authNewX_split_extHook s0.sp))
          (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        rintro ⟨hF_d, hsym_d⟩
        wp_call h_dealloc (rkPin.ptr, rkPin.cap.toNat, 1)
        refine SepWP.fold
          (Entails.of_eq (stackAt_authNewX_split_extHook s0.sp).symm)
          (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (hsplit_top s0.sp).symm) (by sep_focus) ?_
        dsimp only [vecHeader]
        wp_done

theorem authNewPinned_ok_of_contracts_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hupdate : AuthUpdateOkX img F A ext)
    (hA : AllocContractsX img A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authNewName)
      ((authNewPinnedSpec F A).inImage img) :=
  authNewPinned_ok_gen (extra := 0)
    (fun _ => by rw [memRegion_zero, emp_sepConj])
    (fun _ => by rw [memRegion_zero, emp_sepConj])
    himg hupdate hA hallocZeroed

theorem authNewPinned_ok_of_contracts_ext {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hupdate : AuthUpdateOkExt img F A ext)
    (hA : AllocContractsX img A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authNewName)
      ((authNewPinnedSpecExt F A).inImage img) :=
  authNewPinned_ok_gen (extra := 1232)
    (fun sp => ProofLib.stackAt_split_bottom sp authNewStackX 1232 (by decide))
    (fun sp => by
      have h := ProofLib.stackAt_split_bottom (sp - 96#64) authUpdateStackX 1232 (by decide)
      have hsub : sp - 96#64 - BitVec.ofNat 64 (authUpdateStackX + 1232) =
          sp - BitVec.ofNat 64 authNewStackExt := by
        dsimp only [authUpdateStackX, extHookStack, authNewStackExt, authUpdateStackExt, hkdfToSliceStackExt]
        bv_kernel
      have hstk : stackAt (sp - 96#64) (authUpdateStackX + 1232) =
          stackAt (sp - 96#64) authUpdateStackExt := rfl
      exact ((hstk.symm.trans h).trans (by rw [hsub])).symm)
    himg hupdate hA hallocZeroed

private theorem authNew_ok_of_pinned {img : Obj.Image} {stk : Nat}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hpinned : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authNewName)
      ((authNewPinnedSpecAt stk F A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authNewName)
      ((authNewSpecAt stk F A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [Spec.inImage, authNewSpecAt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨himg_s0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hpure_s0, hpre⟩
  have h1 : s0.mem ⊨ vecU8 A x.rkVecA x.rootKey ∗
      (memRegion x.outA authenticatorSize ∗ A.pool ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hpre ⊢
  unfold vecU8 at h1
  rw [sepExists_sepConj_left, satisfies_sepExists] at h1; rcases h1 with ⟨cap, h1⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at h1; rcases h1 with ⟨ptr, h1⟩
  let xp : AuthNewPinnedGhost := ⟨x.outA, x.rkVecA, ⟨cap, ptr⟩, x.rootKey⟩
  have hpre_pin : s0.mem ⊨ ((authNewPinnedSpecAt stk F A).inImage img).pre xp s0 ∗ R := by
    dsimp only [Spec.inImage, authNewPinnedSpecAt, xp]
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨himg_s0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hpure_s0, ?_⟩
    ac_nf at h1 ⊢
  refine hpinned.mono_outcome xp R s0 hpc hrun hpre_pin hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, authNewPinnedSpecAt, authNewSpecAt, xp] at hq ⊢
    have hent : vecHeader x.rkVecA cap ptr (BitVec.ofNat 64 x.rootKey.length) ⊢ memRegion x.rkVecA 24 :=
      vecHeader_entails_memRegion_24 x.rkVecA cap ptr (BitVec.ofNat 64 x.rootKey.length)
    exact Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hent)))) hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hex)

/-- `<spqr::authenticator::Authenticator>::new` (`0x5ddfc`, 48 instructions) meets
`(authNewSpec F A).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
theorem authNew_ok_of_contracts_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hupdate : AuthUpdateOkX img F A ext)
    (hA : AllocContractsX img A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext) :
    AuthNewOkX img F A ext :=
  authNew_ok_of_pinned (authNewPinned_ok_of_contracts_x himg hupdate hA hallocZeroed)

theorem authNew_ok_of_hook_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hupdate : AuthUpdateOkX img F A ext)
    (hA : AllocContractsX img A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    AuthNewOkX img F A ext :=
  authNew_ok_of_contracts_x himg hupdate hA (allocZeroedWithStackOkX_of_hook hZero)

theorem authNew_ok_of_contracts_ext {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hupdate : AuthUpdateOkExt img F A ext)
    (hA : AllocContractsX img A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext) :
    AuthNewOkExt img F A ext :=
  authNew_ok_of_pinned (authNewPinned_ok_of_contracts_ext himg hupdate hA hallocZeroed)

theorem authNew_ok_of_hook_ext {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hupdate : AuthUpdateOkExt img F A ext)
    (hA : AllocContractsX img A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    AuthNewOkExt img F A ext :=
  authNew_ok_of_contracts_ext himg hupdate hA (allocZeroedWithStackOkX_of_hook hZero)

set_option maxHeartbeats 1600000 in
theorem authNewPinned_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_update : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsmpl.base 341) (withLsCallInv lsmpl (authUpdateSpec F A)))
    (h_shim : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (h_allocZeroed : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
      (rustAllocZeroedSpecWithStack A extHookStack))
    (h_dealloc : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack A extHookStack))
    (h_panic : ((blkPC_340).rebase (blkPl_340).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_340).rebase (blkPl_340).base H) (blkPl_340).base
      (withLsCallInv lsmpl (authNewPinnedSpec F A)) := by
  wpp_init x s0
  have h_shim_inv := subroutine_ok_withLsCallInv_of_plain (pl := lsmpl) h_shim
  have h_allocZeroed_inv := subroutine_ok_withLsCallInv_of_plain (pl := lsmpl) h_allocZeroed
  rcases x with ⟨outA, rkVecA, rkPin, rootKey⟩
  dsimp only [authNewPinnedSpec, withLsCallInv] at hpre h_1 h_2 h_3 h ⊢
  have hinv0 : LsCallInv lsmpl s0.mem := h_1
  subst h_2 h_3
  refine SepWPp.rw_pre (by rw [stackAt_authNewX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hinv0 ?_
  refine SepWP.fold (Entails.of_eq (stackAt_authUpdateX_split_extHook (s0.sp - 96#64))) (by sep_focus) ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  change subroutine_ok _ _ (withLsCallInv lsmpl (withStack sessionShimSpec extHookStack)) at h_shim_inv
  wpp_call_lsCallInv_new h_shim_inv () hinv1
  refine SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed") hF_sf ?_
  wp_steps
  have hstack_sf : stackAt (s0.sp - 96#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 96#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  have hlay32 : LayoutOk 32 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  change subroutine_ok _ _ (withLsCallInv lsmpl (rustAllocZeroedSpecWithStack A extHookStack)) at h_allocZeroed_inv
  wpp_call_lsCallInv_new h_allocZeroed_inv (32, 1) hinv2
  by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0#64
  · conv => arg 4; simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    exact allowPanic_panicked_update
      (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
    conv => arg 4; simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, htr2⟩
    refine SepWPp.of_sepWP_lsCallInv
      (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hF_sf_1 ?_
    wp_steps
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
      rw [‹sf_1.sp = sf.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv3
    change subroutine_ok _ _ (withLsCallInv lsmpl (withStack sessionShimSpec extHookStack)) at h_shim_inv
    wpp_call_lsCallInv_new h_shim_inv () hinv3
    refine SepWPp.of_sepWP_lsCallInv
      (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed") hF_sf_2 ?_
    wp_steps
    have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
      rw [‹sf_2.sp = sf_1.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv4
    change subroutine_ok _ _ (withLsCallInv lsmpl (rustAllocZeroedSpecWithStack A extHookStack)) at h_allocZeroed_inv
    wpp_call_lsCallInv_new h_allocZeroed_inv (32, 1) hinv4
    by_cases hoom2 : sf_3.readReg64 Reg.x0 = 0#64
    · conv => arg 4; simp only [hoom2, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr4 => ?_
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      exact allowPanic_panicked_update
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom2_beq : (sf_3.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom2
      conv => arg 4; simp only [hoom2, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr4⟩
      refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 341) hF_sf_3 ?_
      refine SepWP.fold
        (vecU8At_expose_entails A (s0.readReg64 (.gpr 1#5)) rkPin.cap rkPin.ptr rootKey)
        (by sep_focus) ?_
      refine SepWP.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hrk_le, hrk_lt, hrk_ptr⟩
      wp_steps
      refine SepWP.fold
        (authenticatorAt_sp_init A s0.sp (sf_1.readReg64 Reg.x0) (sf_3.readReg64 Reg.x0) hoom1 hoom2)
        (by sep_focus) ?_
      have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt (s0.sp - 96#64) extHookStack := by
        rw [‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 96#64›]
      refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (stackAt_authUpdateX_split_extHook (s0.sp - 96#64)).symm) (by sep_focus) ?_
      have hstack_upd : stackAt (s0.sp - 96#64) authUpdateStackX = stackAt sf_3.sp authUpdateStackX := by
        rw [‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 96#64›]
      refine SepWP.fold (Entails.of_eq hstack_upd) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv5
      have hlen_init :
          ({ rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 } : Authenticator).rootKey.length +
            rootKey.length < 2 ^ 63 := by
        simpa using h
      change subroutine_ok _ _ (withLsCallInv lsmpl (authUpdateSpec F A)) at h_update
      wpp_call_lsCallInv_new h_update
        (⟨s0.sp - 96#64,
          { rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 },
          1#64, false, rkPin.ptr, rootKey⟩ : AuthUpdateGhost)
        hinv5
      apply SepWPp.of_sepWP_ret
      have hnew_eq :
          authenticatorAt A (s0.sp - 96#64)
            (Authenticator.update F { rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 } 1#64 rootKey) =
          authenticatorAt A (s0.sp - 96#64) (Authenticator.new F rootKey 1#64) := rfl
      refine SepWP.fold (Entails.of_eq hnew_eq) (by sep_focus) ?_
      refine SepWP.fold
        (Entails.of_eq (authenticatorAt_eq_exists_pinned A (s0.sp - 96#64)
          (Authenticator.new F rootKey 1#64)))
        (by sep_focus) ?_
      sep_elim_exists
      rename_i g_out
      refine SepWP.fold
        (Entails.of_eq (authenticatorPinAt_at_sp_eq_cells_heap A g_out s0.sp
          (Authenticator.new F rootKey 1#64)))
        (by sep_focus) ?_
      refine SepWP.fold
        (Entails.of_eq (memRegion_48_cells (s0.readReg64 (.gpr 0#5))))
        (by sep_focus) ?_
      sep_elim_exists
      refine SepWP.fold (vecBufAt_fold A rkPin.cap rkPin.ptr rootKey) (by sep_focus) ?_
      have hstack_sf4 : stackAt sf_3.sp authUpdateStackX = stackAt (s0.sp - 96#64) authUpdateStackX := by
        rw [‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 96#64›]
      refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
      by_cases hcap_rk : rkPin.cap = 0#64
      · refine SepWP.fold (vecBufAt_of_cap_zero A hcap_rk hrk_le) (by sep_focus) ?_
        simp only [hcap_rk]
        wp_steps
        refine SepWP.fold
          (Entails.of_eq (authenticatorPinAt_eq_cells_heap A g_out (s0.readReg64 (.gpr 0#5))
            (Authenticator.new F rootKey 1#64)).symm)
          (by sep_focus) ?_
        refine SepWP.fold
          (authenticatorPinAt_entails_authenticatorAt A g_out (s0.readReg64 (.gpr 0#5))
            (Authenticator.new F rootKey 1#64))
          (by sep_focus) ?_
        refine SepWP.fold
          (rejoin_stack_authNewX s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus) ?_
        dsimp only [vecHeader]
        wp_done
      · have hcap_rk_beq : (rkPin.cap == 0#64) = false := beq_false_of_ne hcap_rk
        refine SepWP.fold (vecBufAt_of_cap_ne_zero A hcap_rk hrk_le hrk_lt) (by sep_focus) ?_
        refine SepWP.pure_left_focus _ (by sep_focus) ?_
        intro hrk_lay
        have ⟨_, _, _⟩ := hrk_lay
        wp_steps
        refine SepWP.fold
          (Entails.of_eq (authenticatorPinAt_eq_cells_heap A g_out (s0.readReg64 (.gpr 0#5))
            (Authenticator.new F rootKey 1#64)).symm)
          (by sep_focus) ?_
        refine SepWP.fold
          (authenticatorPinAt_entails_authenticatorAt A g_out (s0.readReg64 (.gpr 0#5))
            (Authenticator.new F rootKey 1#64))
          (by sep_focus) ?_
        refine SepWP.fold
          (rejoin_stack_authNewX s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus) ?_
        refine SepWP.fold
          (Entails.of_eq (stackAt_authNewX_split_extHook s0.sp))
          (by sep_focus) ?_
        wp_call h_dealloc (rkPin.ptr, rkPin.cap.toNat, 1)
        refine SepWP.fold
          (Entails.of_eq (stackAt_authNewX_split_extHook s0.sp).symm)
          (by sep_focus) ?_
        dsimp only [vecHeader]
        wp_done

/-- Relocatable `<spqr::authenticator::Authenticator>::new` (Block `340`) meets
`withLsCallInv lsmpl (authNewSpec F A)` under `[LibsignalPlacement]`. -/
theorem authNew_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_update : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsmpl.base 341) (withLsCallInv lsmpl (authUpdateSpec F A)))
    (h_shim : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (h_allocZeroed : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
      (rustAllocZeroedSpecWithStack A extHookStack))
    (h_dealloc : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack A extHookStack))
    (h_panic : ((blkPC_340).rebase (blkPl_340).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_340).rebase (blkPl_340).base H) (blkPl_340).base
      (withLsCallInv lsmpl (authNewSpec F A)) := by
  have hpinned := authNewPinned_placed_ok h_update h_shim h_allocZeroed h_dealloc h_panic
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCallInv, authNewSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg_s0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure_s0, hpre⟩
  have h1 : s0.mem ⊨ vecU8 A x.rkVecA x.rootKey ∗
      (memRegion x.outA authenticatorSize ∗ A.pool ∗ stackAt s0.sp authNewStackX ∗ R) := by
    ac_nf at hpre ⊢
  unfold vecU8 at h1
  rw [sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨cap, h1⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨ptr, h1⟩
  let xp : AuthNewPinnedGhost := ⟨x.outA, x.rkVecA, ⟨cap, ptr⟩, x.rootKey⟩
  have hpre_pin : s0.mem ⊨ (withLsCallInv lsmpl (authNewPinnedSpec F A)).pre xp s0 ∗ R := by
    dsimp only [withLsCallInv, authNewPinnedSpec, xp]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨himg_s0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpure_s0, ?_⟩
    ac_nf at h1 ⊢
  refine hpinned.mono_outcome xp R s0 hpc hrun hpre_pin hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCallInv, authNewPinnedSpec, authNewSpec, xp] at hq ⊢
    have hent : vecHeader x.rkVecA cap ptr (BitVec.ofNat 64 x.rootKey.length) ⊢ memRegion x.rkVecA 24 :=
      vecHeader_entails_memRegion_24 x.rkVecA cap ptr (BitVec.ofNat 64 x.rootKey.length)
    exact Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hent)))) hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hex)

end CryptoVerification.SpqrV1.Auth
