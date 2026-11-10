/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OptImageHelper
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs

/-!
# Stack- and Optional-Image-Parameterized Allocator Contracts

Unified stack-parameterized specifications (`*SpecWithStack`) specializing definitionally (`rfl`)
to `Alloc.Defs`'s base contracts at `allocHookStack` (`finishGrowStack`) and `*SpecX` contracts at
`extHookStack` (`finishGrowStackX`), with hook adapters for `AllocContracts` (`oimg = none`) and
`AllocContractsX` (`oimg = some img`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib SepProp CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.InImageLift

/-- Stack-equipped no-op shim spec at `hookStack` (`= session2ShimSpecX` at `extHookStack`). -/
def shimSpecWithStack (hookStack : Nat) : Spec Unit where
  pre := fun _ s => stackAt s.sp hookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp hookStack

/-- Stack-equipped `memcpy` spec at `hookStack` (`= session2MemcpySpecX` at `extHookStack`). -/
def memcpySpecWithStack (hookStack : Nat) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
      stackAt s0.sp hookStack

/-- Stack-parameterized `finishGrowSpec` (`= finishGrowSpec A` at `allocHookStack`, `= finishGrowSpecX A` at `extHookStack`). -/
def finishGrowSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf A ∗ A.pool ∗ stackAt s.sp (hookStack + 48)
  post := fun x s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * x.stride.toNat)) ∗
      (if tag = 1#64 then
        ⌜p' = x.align ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ x.oldBuf A
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length)
            (x.new.toNat * x.stride.toNat - x.bs.length)) ∗
      A.pool ∗ stackAt s0.sp (hookStack + 48)

/-- Stack-parameterized `doReserveRawSpec` (`= doReserveRawSpec A` at `finishGrowStack`, `= doReserveRawSpecX A` at `finishGrowStackX`). -/
def doReserveRawSpecWithStack (A : RustAlloc) (fgStack : Nat) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp (fgStack + 64)
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp (fgStack + 64)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack-parameterized `doReserveSpec` (`= doReserveSpec A` at `finishGrowStack`, `= doReserveSpecX A` at `finishGrowStackX`). -/
def doReserveSpecWithStack (A : RustAlloc) (fgStack : Nat) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      newCap + 1 ≤ 2 ^ 63⌝ ∗
    vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (fgStack + 64)
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, vecU8At A x.v (BitVec.ofNat 64 newCap) p' x.bs) ∗
    A.pool ∗ stackAt s0.sp (fgStack + 64)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack-parameterized `intoBoxedSliceSpec` (`= intoBoxedSliceSpec A` at `allocHookStack`, `= intoBoxedSliceSpecX A` at `extHookStack`). -/
def intoBoxedSliceSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec VecArg where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗ x.at A ∗ A.pool ∗ stackAt s.sp (hookStack + 32)
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧ sf.trace = s0.trace⌝ ∗
    vecHeader x.v x.cap x.ptr (BitVec.ofNat 64 x.bytes.length) ∗
    boxU8Buf A (sf.readReg64 .x0) x.bytes ∗ A.pool ∗ stackAt s0.sp (hookStack + 32)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack-parameterized `tryCloneFromRefSpec` (`= tryCloneFromRefSpec A` at `allocHookStack`, `= tryCloneFromRefSpecX A` at `extHookStack`). -/
def tryCloneFromRefSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec TryCloneSliceCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.src ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      x.bs.length + 1 ≤ 2 ^ 63⌝ ∗
    (x.src ↦ₛ x.bs) ∗ A.pool ∗ stackAt s.sp (hookStack + 48)
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = BitVec.ofNat 64 x.bs.length⌝ ∗ (x.src ↦ₛ x.bs) ∗
    (if sf.readReg64 .x0 = 0#64 then
      ⌜x.bs ≠ [] ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝
     else
      ⌜sf.trace = s0.trace⌝ ∗ boxU8Buf A (sf.readReg64 .x0) x.bs) ∗
    A.pool ∗ stackAt s0.sp (hookStack + 48)

/-- Stack-parameterized `chainKeyToPbSpec` (`= chainKeyToPbSpec A` at `allocHookStack`, `= chainKeyToPbSpecX A` at `extHookStack`). -/
def chainKeyToPbSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec ChainKeyToPbCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.ret⌝ ∗
    (x.self ↦ₛ chainKeyBytes x.ck) ∗ memRegion x.ret 32 ∗ A.pool ∗
    stackAt s.sp (hookStack + 48)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.self ↦ₛ chainKeyBytes x.ck) ∗
    (∃∗ p' : BitVec 64, optChainKeyAt A ⟨32#64, p'⟩ (some x.ck) x.ret) ∗
    A.pool ∗ stackAt s0.sp (hookStack + 48)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack-parameterized `publicKeySerializeSpec` (`= publicKeySerializeSpec A` at `allocHookStack`, `= publicKeySerializeSpecX A` at `extHookStack`). -/
def publicKeySerializeSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec PublicKeySerializeCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self⌝ ∗ (x.self ↦ₛ x.pk.bytes.toList) ∗ A.pool ∗
    stackAt s.sp (hookStack + 32)
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
    (x.self ↦ₛ x.pk.bytes.toList) ∗ boxU8Buf A (sf.readReg64 .x0) x.pk.serialize ∗
    A.pool ∗ stackAt s0.sp (hookStack + 32)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Individual Hook Adapters (`oimg = none` from `AllocContracts`, `oimg = some img` from `AllocContractsX`) -/

theorem shim_opt_of_base {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (shimSpecWithStack allocHookStack)) := by
  apply subroutine_ok_to_optNone
  have h := subroutine_ok_withStack_of_subroutine_ok (hA.shim_ok_at name k hk) allocHookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack sessionShimSpec allocHookStack).pre x s0 ∗ R := by
    dsimp only [withStack, sessionShimSpec, shimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  exact h.mono_outcome x R s0 hpc hrun hpre' hal fun _ hout => hout

theorem shim_opt_of_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (shimSpecWithStack extHookStack)) :=
  shim_ok_at2_ext_x hA hk

theorem memcpy_opt_of_base {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (memcpySpecWithStack allocHookStack)) := by
  apply subroutine_ok_to_optNone
  have h := subroutine_ok_withStack_of_subroutine_ok (hA.session_memcpy_region_ok_at name k hk) allocHookStack
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
  · dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpecWithStack] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  · dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpecWithStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

theorem memcpy_opt_of_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (memcpySpecWithStack extHookStack)) :=
  memcpy_ok_at2_ext_x hA hk

theorem alloc_opt_of_base {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (rustAllocSpecWithStack A allocHookStack)) :=
  subroutine_ok_to_optNone (alloc_ok_at_norm_ext hA hk)

theorem alloc_opt_of_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (rustAllocSpecWithStack A extHookStack)) :=
  alloc_ok_at_norm_ext_x hA hk

theorem dealloc_opt_of_base {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (rustDeallocExternSpecWithStack A allocHookStack)) :=
  subroutine_ok_to_optNone
    (rustDeallocExternWithStack_of_rustDealloc (dealloc_ok_at_norm_ext hA hk) (by decide) (by decide))

theorem dealloc_opt_of_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (rustDeallocExternSpecWithStack A extHookStack)) :=
  dealloc_ok_at_norm_ext_x hA hk

theorem realloc_opt_of_base {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (rustReallocExternSpecWithStack A allocHookStack)) :=
  subroutine_ok_to_optNone
    (rustReallocExternWithStack_of_rustRealloc (realloc_ok_at_norm_ext hA hk) (by decide) (by decide))

theorem realloc_opt_of_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv (some img) (rustReallocExternSpecWithStack A extHookStack)) :=
  realloc_ok_at_norm_ext_x hA hk

end CryptoVerification.LibsignalTripleRatchet
