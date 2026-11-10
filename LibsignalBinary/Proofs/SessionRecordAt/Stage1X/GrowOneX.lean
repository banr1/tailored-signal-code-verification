/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.Core
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.Fetch
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import ProofLib.SepLogic.WPp

/-!
# `<alloc::raw_vec::RawVec<Chain>>::grow_one` at `externStack`

Verifies `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (`finishGrowStackX = 16432`,
Block `45`) and `<alloc::raw_vec::RawVec<Chain>>::grow_one` (`growOneChainStackX = 16896`,
stride `104`, alignment `8`, Block `43`) on `SP2Ext` under `AllocContractsX` and under relocatable
`[LibsignalPlacement]` (`AllocContractsPlaced`), modeling normal growth, OOM, and capacity-overflow
panic.
-/

@[expose] public section

set_option autoImplicit false
namespace Proofs.libsignal.Stage1X

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open Proofs.libsignal.Hooks2 (SP2Ext SP2Ext_fnAddr sub_ok_at_caller)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_GrowOneX : True := trivial

/-! ## Stack budgets and allocator contract specifications -/

/-- Stack budget of `finish_grow` at `extHookStack` (`16384 + 48 = 16432` B). -/
abbrev finishGrowStackX : Nat := extHookStack + 48

/-- Stack budget of `grow_one<Chain>` at `extHookStack` (`464 + 16432 = 16896` B). -/
abbrev growOneChainStackX : Nat := 464 + Proofs.libsignal.Stage1X.finishGrowStackX

/-- Stack budget of `consume_message_key` at `extHookStack` (`20480` B). -/
abbrev cmkStackX : Nat := 20480

/-- `sessionShimSpec` at `extHookStack` (`16384` B). -/
abbrev session2ShimSpecX : Spec Unit :=
  sessionShimSpec.withHookStack extHookStack

/-- `rustAllocSpec A` at arbitrary stack size `stk`. -/
def rustAllocSpecWithStack (A : RustAlloc) (stk : Nat) : Spec (Nat × Nat) where
  pre := fun (size, align) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      LayoutOk size align⌝ ∗
    A.pool ∗ stackAt s.sp stk
  post := fun (size, align) s0 sf =>
    (if sf.readReg64 .x0 = 0 then
      ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
    else
      ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
        A.live (sf.readReg64 .x0) size align ∗
        memRegion (sf.readReg64 .x0) size) ∗
    A.pool ∗ stackAt s0.sp stk

/-- `rustDeallocSpec A` at arbitrary stack size `stk`. -/
def rustDeallocSpecWithStack (A : RustAlloc) (stk : Nat) : Spec (BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align⌝ ∗
    A.live p size align ∗ memRegion p size ∗
    A.pool ∗ stackAt s.sp stk
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp stk

/-- `Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A stk`: `rustDeallocSpecWithStack` with `LayoutOk size align`. -/
def rustDeallocExternSpecWithStack (A : RustAlloc) (stk : Nat) : Spec (BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align ∧
      LayoutOk size align⌝ ∗
    A.live p size align ∗ memRegion p size ∗
    A.pool ∗ stackAt s.sp stk
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp stk

/-- Ghost state for `__rustc::__rust_realloc`: `(ptr, old_size, align, new_size, bs)`. -/
abbrev ReallocGhost : Type := BitVec 64 × Nat × Nat × Nat × List (BitVec 8)

/-- `rustReallocSpec A` at arbitrary stack size `stk`. -/
def rustReallocSpecWithStack (A : RustAlloc) (stk : Nat) : Spec ReallocGhost where
  pre := fun (p, old_size, align, new_size, bs) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old_size ∧
      (s.readReg64 .x2).toNat = align ∧ (s.readReg64 .x3).toNat = new_size ∧
      bs.length ≤ old_size ∧ bs.length ≤ new_size ∧ LayoutOk new_size align⌝ ∗
    A.live p old_size align ∗ (p ↦ₛ bs) ∗
    memRegion (p + BitVec.ofNat 64 bs.length) (old_size - bs.length) ∗
    A.pool ∗ stackAt s.sp stk
  post := fun (p, old_size, align, new_size, bs) s0 sf =>
    (if sf.readReg64 .x0 = 0 then
      ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        A.live p old_size align ∗ (p ↦ₛ bs) ∗
        memRegion (p + BitVec.ofNat 64 bs.length) (old_size - bs.length)
    else
      ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
        A.live (sf.readReg64 .x0) new_size align ∗
        ((sf.readReg64 .x0) ↦ₛ bs) ∗
        memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new_size - bs.length)) ∗
    A.pool ∗ stackAt s0.sp stk

/-- `Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack A stk`: `rustReallocSpecWithStack` with `LayoutOk old_size align`. -/
def rustReallocExternSpecWithStack (A : RustAlloc) (stk : Nat) : Spec ReallocGhost where
  pre := fun (p, old_size, align, new_size, bs) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old_size ∧
      (s.readReg64 .x2).toNat = align ∧ (s.readReg64 .x3).toNat = new_size ∧
      bs.length ≤ old_size ∧ bs.length ≤ new_size ∧
      LayoutOk old_size align ∧ LayoutOk new_size align⌝ ∗
    A.live p old_size align ∗ (p ↦ₛ bs) ∗
    memRegion (p + BitVec.ofNat 64 bs.length) (old_size - bs.length) ∗
    A.pool ∗ stackAt s.sp stk
  post := (rustReallocSpecWithStack A stk).post

/-- `finishGrowSpec A` at `Proofs.libsignal.Stage1X.finishGrowStackX` (`16432` B). -/
def finishGrowSpecX (A : RustAlloc) : Spec FinishGrowCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf A ∗ A.pool ∗ stackAt s.sp Proofs.libsignal.Stage1X.finishGrowStackX
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
      A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX

/-! ## Arithmetic and memory helpers -/

private theorem umulh_stride_eq_zero {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : stride.toNat * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  rfl

private theorem mul_stride_toNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem mul_stride_ne_zero {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_stride_ne_zero h0 h

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]
      change align.toNat ≤ 2 ^ 63
      omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat (by omega)]
  omega

private theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_finishGrowX (sp : BitVec 64) :
    stackAt sp Proofs.libsignal.Stage1X.finishGrowStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  LibsignalTripleRatchet.stackAt_split_cells sp 16384 6 (by decide)

/-- `growOneSpec A` at `Proofs.libsignal.Stage1X.growOneChainStackX = 464 + Proofs.libsignal.Stage1X.finishGrowStackX` (`16896` B). -/
def growOne104SpecX (A : RustAlloc) : Spec GrowGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
      max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool ∗ stackAt s.sp (464 + Proofs.libsignal.Stage1X.finishGrowStackX)
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0⌝ ∗ (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 104) ∗
      A.pool ∗ stackAt s0.sp (464 + Proofs.libsignal.Stage1X.finishGrowStackX)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev growOneChainSpecX (A : RustAlloc) : Spec GrowGhost := growOne104SpecX A

abbrev growOneChainName : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"

/-- `<alloc::raw_vec::RawVec<Chain>>::grow_one` contract on `SP2Ext img.base ext`
at `Proofs.libsignal.Stage1X.growOneChainStackX` (`16896` B). -/
def GrowOneChainOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext)
    ((SP2Ext img.base ext).fnAddr growOneChainName)
    ((growOneChainSpecX A).inImage img)

/-! ## `AllocContractsX` bundle and constructors -/

/-- Allocator and memmove contract bundle at `extHookStack` (`16384` B) for `GrowOneX` and `CmkX`. -/
structure AllocContractsX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : subroutine_ok (SP2Ext img.base ext)
    ((SP2Ext img.base ext).fnAddr "__rustc::__rust_alloc")
    ((Proofs.libsignal.Stage1X.rustAllocSpecWithStack A extHookStack).inImage img)
  dealloc : subroutine_ok (SP2Ext img.base ext)
    ((SP2Ext img.base ext).fnAddr "__rustc::__rust_dealloc")
    ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A extHookStack).inImage img)
  realloc : subroutine_ok (SP2Ext img.base ext)
    ((SP2Ext img.base ext).fnAddr "__rustc::__rust_realloc")
    ((Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack A extHookStack).inImage img)
  shim : subroutine_ok (SP2Ext img.base ext)
    ((SP2Ext img.base ext).fnAddr "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (Proofs.libsignal.Stage1X.session2ShimSpecX.inImage img)
  session_memmove : subroutine_ok (SP2Ext img.base ext)
    ((SP2Ext img.base ext).fnAddr "memmove")
    ((sessionMemmoveSpec extHookStack).inImage img)

/-- State-level call invariant (`img.FrozenLoaded s ∧ s.symtab = img.symtab`). -/
abbrev ImgCallInv (img : Obj.Image) (s : State) : Prop :=
  img.FrozenLoaded s ∧ s.symtab = img.symtab

/-- Sequence a `SepWP` segment while threading `CryptoVerification.LibsignalTripleRatchet.ImgCallInv img` to the midpoint. -/
theorem _root_.ProofLib.CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage {prog : Program} {img : Obj.Image}
    {mid target_pc : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => CryptoVerification.LibsignalTripleRatchet.ImgCallInv img sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  exact ProofLib.SepWP.of_sepWP_inv hinv.1 hinv.2 (SepWP.mono h fun sm Pm _ _ hm hF hsym => hm ⟨hF, hsym⟩)

/-- Sequence a `SepWP` segment into `SepWPp` while threading `CryptoVerification.LibsignalTripleRatchet.ImgCallInv img` to the midpoint. -/
theorem _root_.ProofLib.SepWPp.of_sepWP_inImage {prog : Program} {img : Obj.Image}
    {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => CryptoVerification.LibsignalTripleRatchet.ImgCallInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  exact ProofLib.SepWPp.of_sepWP_inv hinv.1 hinv.2 (SepWP.mono h fun sm Pm _ _ hm hF hsym => hm ⟨hF, hsym⟩)

theorem AllocContractsX.alloc_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff "__rustc::__rust_alloc") :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((Proofs.libsignal.Stage1X.rustAllocSpecWithStack A extHookStack).inImage img) := by
  have h := hA.alloc
  rw [SP2Ext_fnAddr] at h
  exact sub_ok_at_caller hk h

theorem AllocContractsX.dealloc_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff "__rustc::__rust_dealloc") :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A extHookStack).inImage img) := by
  have h := hA.dealloc
  rw [SP2Ext_fnAddr] at h
  exact sub_ok_at_caller hk h

theorem AllocContractsX.realloc_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff "__rustc::__rust_realloc") :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack A extHookStack).inImage img) := by
  have h := hA.realloc
  rw [SP2Ext_fnAddr] at h
  exact sub_ok_at_caller hk h

theorem AllocContractsX.shim_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2") :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (Proofs.libsignal.Stage1X.session2ShimSpecX.inImage img) := by
  have h := hA.shim
  rw [SP2Ext_fnAddr] at h
  exact sub_ok_at_caller hk h

theorem AllocContractsX.session_memmove_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff "memmove") :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemmoveSpec extHookStack).inImage img) := by
  have h := hA.session_memmove
  rw [SP2Ext_fnAddr] at h
  exact sub_ok_at_caller hk h

/-- Any call to `alloc::raw_vec::handle_error` panics on `SP2Ext b ext`. -/
theorem panic_at_handle_error_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "alloc::raw_vec::handle_error") := by decide) :
    (SP2Ext b ext).externAt? ((SP2Ext b ext).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol hfn hk (by decide) (ls_hook% "alloc::raw_vec::handle_error")
    (by simp [Rust.isPanicSymbol])

/-! ## `<alloc::raw_vec::RawVecInner>::finish_grow` -/

private def finishGrowZeroSpec2X (A : RustAlloc) : Spec FinishGrowCall :=
  { Proofs.libsignal.Stage1X.finishGrowSpecX A with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp Proofs.libsignal.Stage1X.finishGrowStackX }

set_option maxHeartbeats 800000 in
private theorem finish_grow_zero_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr finishGrowName)
      ((finishGrowZeroSpec2X A).inImage img) := by
  unfold Spec.inImage finishGrowZeroSpec2X Proofs.libsignal.Stage1X.finishGrowSpecX
  simp only [memRegion_24, stackAt_finishGrowX, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff finishGrowName = num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")
  have hshim := hA.shim_ok_at finishGrowName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) (by simp only [arm64_norm])
  have halloc := hA.alloc_ok_at finishGrowName
    (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) (by simp only [arm64_norm])
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalSession.RawVecGrowOne.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) 180
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  subst cap
  subst bs
  have hinv0 : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
  wp_call halloc (new.toNat * stride.toNat, align.toNat)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat hlt64
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat hlt64
    simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists align
    simp only [ite_true, FinishGrowCall.oldBuf]
    wp_done

private def finishGrowNeSpec2X (A : RustAlloc) : Spec FinishGrowCall :=
  { Proofs.libsignal.Stage1X.finishGrowSpecX A with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
        (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp Proofs.libsignal.Stage1X.finishGrowStackX }

set_option maxHeartbeats 800000 in
private theorem finish_grow_ne_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr finishGrowName)
      ((finishGrowNeSpec2X A).inImage img) := by
  unfold Spec.inImage finishGrowNeSpec2X Proofs.libsignal.Stage1X.finishGrowSpecX
  simp only [memRegion_24, stackAt_finishGrowX, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff finishGrowName = num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")
  have hrealloc := hA.realloc_ok_at finishGrowName
    (num% (ls_off% "__rustc::__rust_realloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) (by simp only [arm64_norm])
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalSession.RawVecGrowOne.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) 180
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  have hinv0 : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hlay_old : LayoutOk (cap.toNat * stride.toNat) align.toNat := ⟨hold_pos, hpow, by omega⟩
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF1, hsym1⟩
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat hlt64
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat hlt64
    simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists align
    simp only [ite_true, FinishGrowCall.oldBuf, hcap_ne, ite_false]
    wp_done

/-- `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` meets
`(Proofs.libsignal.Stage1X.finishGrowSpecX A).inImage img` on `SP2Ext img.base ext` under `AllocContractsX`. -/
theorem finish_grow_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr finishGrowName)
      ((Proofs.libsignal.Stage1X.finishGrowSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_zero_ok_ext_x hA).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrowZeroSpec2X, FinishGrowCall.oldBuf,
      hcap0, ite_true, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine (finish_grow_ne_ok_ext_x hA).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrowNeSpec2X, FinishGrowCall.oldBuf,
      hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

/-! ## `<alloc::raw_vec::RawVec<Chain>>::grow_one` -/

private abbrev FG48Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem SepWPp.ite_elim_pure1 {prog : Program} {ret : BitVec 64} {s : State}
    {c : Prop} [Decidable c] {φ ψ : Prop} {R2 F : SepProp} {Q Qp : State → SepProp → Prop}
    (hthen : c → φ → SepWPp prog ret s F Q Qp)
    (helse : ¬ c → ψ → SepWPp prog ret s (R2 ∗ F) Q Qp) :
    SepWPp prog ret s ((if c then ⌜φ⌝ else ⌜ψ⌝ ∗ R2) ∗ F) Q Qp := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact SepWPp.pure_elim (hthen hc)
  · simp only [hc, ite_false, sepConj_assoc]; exact SepWPp.pure_elim (helse hc)

private theorem SepWPp.ite_elim_pure2 {prog : Program} {ret : BitVec 64} {s : State}
    {c : Prop} [Decidable c] {φ ψ : Prop} {R1 R2 F : SepProp} {Q Qp : State → SepProp → Prop}
    (hthen : c → φ → SepWPp prog ret s (R1 ∗ F) Q Qp)
    (helse : ¬ c → ψ → SepWPp prog ret s (R2 ∗ F) Q Qp) :
    SepWPp prog ret s ((if c then ⌜φ⌝ ∗ R1 else ⌜ψ⌝ ∗ R2) ∗ F) Q Qp := by
  by_cases hc : c
  · simp only [hc, ite_true, sepConj_assoc]; exact SepWPp.pure_elim (hthen hc)
  · simp only [hc, ite_false, sepConj_assoc]; exact SepWPp.pure_elim (helse hc)

private def growPad104X (sp : BitVec 64) : SepProp :=
  memRegion (sp - 16896#64) 400

private theorem stackAt_grow_one_104_x (sp : BitVec 64) :
    stackAt sp (464 + Proofs.libsignal.Stage1X.finishGrowStackX) =
      growPad104X sp ∗
      (stackAt (sp - 64#64) Proofs.libsignal.Stage1X.finishGrowStackX ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7))) := by
  have h1 := stackAt_split_bottom sp 16496 400 (by decide)
  have h2 := LibsignalTripleRatchet.stackAt_split_cells sp 16432 8 (by decide)
  change stackAt sp (464 + Proofs.libsignal.Stage1X.finishGrowStackX) = growPad104X sp ∗ stackAt sp 16496 at h1
  change stackAt sp 16496 = stackAt (sp - 64#64) Proofs.libsignal.Stage1X.finishGrowStackX ∗ cells (sp - 64#64) 8 at h2
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, hc8]

private theorem grow_104_new_cap_eq {cap : BitVec 64}
    (h : max (2 * cap.toNat) 4 * 104 ≤ 9223372036854775800) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    have hlt : 4 < 2 * cap.toNat := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
      exact hc
    omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hle : ¬ 4 < 2 * cap.toNat := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
      exact hc
    change 4 = max (2 * cap.toNat) 4
    omega

private def finishGrow104ZeroSpecX (A : RustAlloc) : Spec FG48Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp Proofs.libsignal.Stage1X.finishGrowStackX
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          (A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104))) ∗
      A.pool ∗ stackAt fsp Proofs.libsignal.Stage1X.finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_104_zero_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hfg : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr finishGrowName) ((Proofs.libsignal.Stage1X.finishGrowSpecX A).inImage img)) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr finishGrowName)
      ((finishGrow104ZeroSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, finishGrow104ZeroSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 8#64, 104#64, []⟩
  have hlay : LayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, ?_⟩
    change new.toNat * 104 + 8 ≤ 2 ^ 63; omega
  have hpre' : s0.mem ⊨ ((Proofs.libsignal.Stage1X.finishGrowSpecX A).inImage img).pre hcall s0 ∗ R := by
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.finishGrowSpecX, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrow104ZeroSpecX, hcall, FinishGrowCall.oldBuf,
      ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    have hm104 : (104#64 : BitVec 64).toNat = 104 := rfl
    have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [hm104, ha8] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 104), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [show (out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104) ∗
            ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX) ∗ R =
          ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            ((A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX ∗ out ↦₆₄ 1#64 ∗
              (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [show (out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104) ∗
            (⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104)) ∗
            A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX) ∗ R =
          ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
            ((A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104) ∗
              A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX ∗
              out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

private def finishGrow104NeSpecX (A : RustAlloc) : Spec FG48Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length = cap.toNat * 104 ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗
    A.pool ∗ stackAt fsp Proofs.libsignal.Stage1X.finishGrowStackX
  post := fun (out, _cap, ptr, new, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          (A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs))
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          (A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length))) ∗
      A.pool ∗ stackAt fsp Proofs.libsignal.Stage1X.finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_104_ne_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hfg : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr finishGrowName) ((Proofs.libsignal.Stage1X.finishGrowSpecX A).inImage img)) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr finishGrowName)
      ((finishGrow104NeSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, finishGrow104NeSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 8#64, 104#64, bs⟩
  have hlay : LayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, ?_⟩
    change new.toNat * 104 + 8 ≤ 2 ^ 63; omega
  have hm104 : (104#64 : BitVec 64).toNat = 104 := rfl
  have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have hpre' : s0.mem ⊨ ((Proofs.libsignal.Stage1X.finishGrowSpecX A).inImage img).pre hcall s0 ∗ R := by
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.finishGrowSpecX, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [hm104, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc,
      satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, Nat.le_refl _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrow104NeSpecX, hcall, FinishGrowCall.oldBuf,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    rw [hm104, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 104), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [show (out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104) ∗
            (⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
              A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
            A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX) ∗ R =
          ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            ((A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗
              A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX ∗
              out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hq.1.2, ?_⟩
      simpa only [sepConj_assoc] using hq.2
    · simp only [htag, ite_false] at hq ⊢
      rw [show (out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104) ∗
            (⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
              memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length)) ∗
            A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX) ∗ R =
          ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
            ((A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
              memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length) ∗
              A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX ∗
              out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

set_option maxHeartbeats 800000 in
/-- `<alloc::raw_vec::RawVec<Chain>>::grow_one` (26 insns) meets
`(growOne104SpecX A).inImage img` on `SP2Ext img.base ext` under `AllocContractsX`. -/
theorem grow_one_104_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr growOneChainName)
      ((growOne104SpecX A).inImage img) := by
  have hfg := finish_grow_ok_ext_x hA
  unfold Spec.inImage growOne104SpecX
  simp only [stackAt_grow_one_104_x, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
  have hpanic := panic_at_handle_error_ext (b := img.base) (ext := ext)
    hfn (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")) (by simp only [arm64_norm])
  have hfg0 := finish_grow_104_zero_ok_x hfg
  have hfg1 := finish_grow_104_ne_ok_x hfg
  rw [Program.fnAddr_rel
    (name := growOneChainName)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]") (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")) (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalSession.RawVecGrowOne.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")) 104
  wpp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hinv0 : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hnew_eq := grow_104_new_cap_eq h
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * 104 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero h_4
    subst hbs
    simp only [BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_zero, Nat.mul_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := entry + bv% (60))
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")) hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by first | rfl | assumption) (by first | rfl | assumption)
    refine SepWPp.ite_elim_pure1 (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun_sf)
      refine SepWPp.panic (by exact hrun_sf) hpanic fun hm => ?_
      exact allowPanic_panicked
        (allocFailedIn_of_eq (htrace : (Rust.panicked _).trace = s0.trace ++ [allocFailedEvent])) hm
    · subst hw0
      rw [sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0', ite_false, sepConj_assoc]
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = new.toNat * 104 - bs.length := by
      rw [Nat.sub_mul, hnew_toNat, h_4]
    rw [hsub_mul]
    apply SepWPp.of_sepWP (mid := entry + bv% (60))
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")) hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done hpc_sf hrun_sf
    refine SepWPp.ite_elim_pure2 (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag
      rw [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun_sf)
      refine SepWPp.panic (by exact hrun_sf) hpanic fun hm => ?_
      rw [← sepConj_assoc]
      exact allowPanic_panicked
        (allocFailedIn_of_eq (htrace : (Rust.panicked _).trace = s0.trace ++ [allocFailedEvent])) hm
    · subst hw0
      rw [sepConj_assoc, sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

/-- `<alloc::raw_vec::RawVec<Chain>>::grow_one` meets `GrowOneChainOkX img A ext`
under `AllocContractsX img A ext`. -/
theorem growOneChain_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    GrowOneChainOkX img A ext :=
  grow_one_104_ok_ext_x hA

/-! ## Relocatable `[LibsignalPlacement]` proofs (Blocks `45` and `43`) -/

section Placed

open Proofs.libsignal.Hooks2
  (subroutine_ok_withLsCodeLoaded_map' subroutine_ok_withLsCl_map'
   subroutine_ok_withLsCl_withHookStack_mono subroutine_ok_withExternStackFromAlloc')

/-- Relocatable contract-form allocator + `memmove` + panic bundle at `extHookStack = 16384`. -/
structure AllocContractsPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  alloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustAllocSym) (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustAllocSpecWithStack A extHookStack))
  dealloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustDeallocSym) (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A extHookStack))
  realloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustReallocSym) (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack A extHookStack))
  shim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSym) (withLsCl lsmpl Proofs.libsignal.Stage1X.session2ShimSpecX)
  session_memmove : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memmove") (withLsCl lsmpl (sessionMemmoveSpec extHookStack))
  panic_handle_error : H lsHandleErrorSym = some Rust.panicked
  panic_handle_alloc_error : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked

/-- Construct `AllocContractsPlaced A H` from block-0 `withLsCodeLoaded` contracts. -/
theorem AllocContractsPlaced.of_block0 [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (halloc : subroutine_ok blk0Prog (lsρ lsRustAllocSym) (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.rustAllocSpecWithStack A extHookStack)))
    (hdealloc : subroutine_ok blk0Prog (lsρ lsRustDeallocSym) (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A extHookStack)))
    (hrealloc : subroutine_ok blk0Prog (lsρ lsRustReallocSym) (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack A extHookStack)))
    (hshim : subroutine_ok blk0Prog (lsρ lsRustNoAllocShimSym) (withLsCodeLoaded lsmpl Proofs.libsignal.Stage1X.session2ShimSpecX))
    (hmemmove : subroutine_ok blk0Prog (lsρ "memmove") (withLsCodeLoaded lsmpl (sessionMemmoveSpec extHookStack)))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked) (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    AllocContractsPlaced A H :=
  ⟨ls_subroutine_ok_cl_of_callee (j := 0) halloc, ls_subroutine_ok_cl_of_callee (j := 0) hdealloc,
   ls_subroutine_ok_cl_of_callee (j := 0) hrealloc, ls_subroutine_ok_cl_of_callee (j := 0) hshim,
   ls_subroutine_ok_cl_of_callee (j := 0) hmemmove, hpan_err, hpan_alloc⟩

/-- Construct `AllocContractsPlaced A H` from `HookSat H` single-step hooks via `stackAt_split_bottom` slack framing. -/
theorem AllocContractsPlaced.of_hooks [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A)) (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (hmemmove : HookSat H "memmove" (sessionMemmoveSpec extHookStack))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked) (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    AllocContractsPlaced A H where
  alloc := fun {callerProg callerBlk _} => by
    have h0 := ls_subroutine_ok_cl_of_plain_prog (pl := lsmpl) (prog := callerProg) (rustAllocWithStack_of_rustAlloc (hookStack := extHookStack) (ls_hook_ok_of_caller halloc) (by decide) (by decide))
    refine subroutine_ok_withLsCl_map' h0 fun ⟨size, align⟩ R s0 hpre => ⟨(size, align), R, ?_, fun sf hpost => ?_⟩
    · dsimp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack] at hpre ⊢; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · dsimp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack] at hpost ⊢; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  dealloc := fun {callerProg callerBlk _} => by
    have h0 := ls_subroutine_ok_cl_of_plain_prog (pl := lsmpl) (prog := callerProg) (rustDeallocExternWithStack_of_rustDealloc (hookStack := extHookStack) (ls_hook_ok_of_caller hdealloc) (by decide) (by decide))
    refine subroutine_ok_withLsCl_map' h0 fun ⟨p, size, align⟩ R s0 hpre => ⟨(p, size, align), R, ?_, fun sf hpost => ?_⟩
    · dsimp only [Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack, CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack] at hpre ⊢; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · dsimp only [Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack, CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack] at hpost ⊢; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  realloc := fun {callerProg callerBlk _} => by
    have h0 := ls_subroutine_ok_cl_of_plain_prog (pl := lsmpl) (prog := callerProg) (rustReallocExternWithStack_of_rustRealloc (hookStack := extHookStack) (ls_hook_ok_of_caller hrealloc) (by decide) (by decide))
    refine subroutine_ok_withLsCl_map' h0 fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre => ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩
    · dsimp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack, CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack] at hpre ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢; obtain ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, hlay_old, hlay_new⟩, hmem⟩ := hpre
      exact ⟨⟨hx0, hx1, hx2, hx3, hlay_old, hlay_new, hbs1, hbs2⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem⟩
    · dsimp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack, Proofs.libsignal.Stage1X.rustReallocSpecWithStack,
        CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack, CryptoVerification.LibsignalTripleRatchet.rustReallocSpecWithStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  shim := fun {callerProg callerBlk _} => by
    have h0 : subroutine_ok callerProg (lsρ lsRustNoAllocShimSym) (withLsCl lsmpl (sessionShimSpec.withHookStack 0)) := by
      refine subroutine_ok_withLsCl_map' (ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hshim)) fun x R s0 hpre => ⟨x, stackAt s0.sp 0 ∗ R, ?_, fun sf hpost => ?_⟩
      · dsimp only [Spec.withHookStack] at hpre; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
      · dsimp only [Spec.withHookStack]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    exact subroutine_ok_withLsCl_withHookStack_mono (by decide) (by decide) h0
  session_memmove := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemmove)
  panic_handle_error := hpan_err
  panic_handle_alloc_error := hpan_alloc

theorem AllocContractsPlaced.externAt_handle_error [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : AllocContractsPlaced A H) {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    callerProg.externAt? (lsρ lsHandleErrorSym) = some Rust.panicked :=
  (ls_externAt?_of_caller (sym := lsHandleErrorSym) (by decide)).trans hA.panic_handle_error
theorem AllocContractsPlaced.externAt_handle_alloc_error [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : AllocContractsPlaced A H) {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    callerProg.externAt? (lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error") = some Rust.panicked :=
  (ls_externAt?_of_caller (sym := "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error") (by decide)).trans hA.panic_handle_alloc_error

/-- Specialize a `withLsCl pl spec` contract at memory `m` with `LibsignalCodeLoaded pl m` to `withMemEq m spec`. -/
theorem lscall_of_withLsCl {pl : Obj.MultiPlacement} {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α} {m : Memory}
    (hcall : subroutine_ok prog entry (withLsCl pl spec)) (hcl : LibsignalCodeLoaded pl m) : subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono hcall (fun _ _ s0 hp => by have ⟨hm, hpre⟩ := extract_withMemEq hp; dsimp only [withLsCl]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; exact ⟨hm ▸ hcl, hpre⟩)
    (fun _ _ _ _ hq => by dsimp only [withLsCl, withMemEq] at hq ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hq; exact hq.2)

private theorem SepWPp.of_sepWP_lscl_local {pl : Obj.MultiPlacement} {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem) (h : SepWP prog mid s P (fun sm Pm => LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  exact ProofLib.SepWPp.seq_frozen (fun _ _ h' hkf => h'.of_keepsFrozen hkf) hcl h

set_option maxHeartbeats 800000 in
private theorem finish_grow_zero_placed_ok_ext_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsPlaced A H) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base (withLsCodeLoaded lsmpl (finishGrowZeroSpec2X A)) := by
  unfold withLsCodeLoaded finishGrowZeroSpec2X Proofs.libsignal.Stage1X.finishGrowSpecX
  simp only [memRegion_24, stackAt_finishGrowX, sepExists_sepConj_left, sepExists_sepConj_right]; cells_unfold
  wp_init x s0; obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x; dsimp only at *
  rcases ‹LayoutOk (new.toNat * stride.toNat) align.toNat› with ⟨hsz_pos, hpow, hbound⟩; subst cap; subst bs
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64; have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64; have hmul := mul_stride_toNat hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  wp_steps_lscl (lsρ lsRustNoAllocShimSym)
  apply sepWP_seq_lscl (mid := lsρ lsRustAllocSym) ‹_›
  have hshim_call := lscall_of_withLsCl (hA.shim (callerProg := (blkPC_45).rebase (blkPl_45).base H)) ‹_›
  wp_call hshim_call (); wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl2
  have halloc_call := lscall_of_withLsCl (hA.alloc (callerProg := (blkPC_45).rebase (blkPl_45).base H)) hcl2
  wp_call halloc_call (new.toNat * stride.toNat, align.toNat); wp_steps; wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom; have hmul_bv := mul_stride_eq_ofNat hlt64; simp only [hoom', ite_false]; wp_steps
    apply SepWP.instantiate_post_exists 0#64; apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false, pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]; wp_done
  · have hmul_bv := mul_stride_eq_ofNat hlt64; simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply SepWP.instantiate_post_exists 1#64; apply SepWP.instantiate_post_exists align; simp only [ite_true, FinishGrowCall.oldBuf]; wp_done

set_option maxHeartbeats 800000 in
private theorem finish_grow_ne_placed_ok_ext_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsPlaced A H) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base (withLsCodeLoaded lsmpl (finishGrowNeSpec2X A)) := by
  unfold withLsCodeLoaded finishGrowNeSpec2X Proofs.libsignal.Stage1X.finishGrowSpecX
  simp only [memRegion_24, stackAt_finishGrowX, sepExists_sepConj_left, sepExists_sepConj_right]; cells_unfold
  wp_init x s0; obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x; dsimp only at *
  rcases ‹LayoutOk (new.toNat * stride.toNat) align.toNat› with ⟨hsz_pos, hpow, hbound⟩
  have hcap_ne : cap ≠ 0#64 := ‹_›; have hstr_pos : 0 < stride.toNat := ‹_›
  have hcap_le_new : cap.toNat ≤ new.toNat := ‹_›; have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := ‹_›
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat := Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_pos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero hlt64; have hhi := hi_stride_eq_false hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul := mul_stride_toNat hlt64; have hmul_cap := mul_stride_toNat hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hlay_old : LayoutOk (cap.toNat * stride.toNat) align.toNat := ⟨hold_pos, hpow, by omega⟩
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  wp_steps_lscl (lsρ lsRustReallocSym)
  have hrealloc_call := lscall_of_withLsCl (hA.realloc (callerProg := (blkPC_45).rebase (blkPl_45).base H)) ‹_›
  wp_call hrealloc_call (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs); wp_steps; wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom; have hmul_bv := mul_stride_eq_ofNat hlt64; simp only [hoom', ite_false]; wp_steps
    apply SepWP.instantiate_post_exists 0#64; apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]; wp_done
  · have hmul_bv := mul_stride_eq_ofNat hlt64; simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]; wp_steps
    apply SepWP.instantiate_post_exists 1#64; apply SepWP.instantiate_post_exists align; simp only [ite_true, FinishGrowCall.oldBuf, hcap_ne, ite_false]; wp_done

/-- Relocatable `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (Block `45`) meets
`withLsCodeLoaded lsmpl (finishGrowSpecX A)` under `AllocContractsPlaced A H`. -/
theorem finish_grow_placed_ok_ext_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsPlaced A H) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.finishGrowSpecX A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have ⟨hcl0, hpre0⟩ := extract_withLsCodeLoaded hpre
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_zero_placed_ok_ext_x hA).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; refine ⟨hcl0, ?_⟩
    simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrowZeroSpec2X, FinishGrowCall.oldBuf,
      hcap0, ite_true, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine (finish_grow_ne_placed_ok_ext_x hA).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; refine ⟨hcl0, ?_⟩
    simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrowNeSpec2X, FinishGrowCall.oldBuf,
      hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

private theorem finish_grow_104_zero_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.finishGrowSpecX A))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base (withLsCodeLoaded lsmpl (finishGrow104ZeroSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_map' hfg (fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpre => ?_)
  simp only [finishGrow104ZeroSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 8#64, 104#64, []⟩
  have hlay : LayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat :=
    ⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, by change new.toNat * 104 + 8 ≤ 2 ^ 63; omega⟩
  refine ⟨hcall, R, ?_, fun sf hq => ?_⟩
  · simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, by decide, hlay⟩, by simpa only [sepConj_assoc] using hmem⟩
  · simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrow104ZeroSpecX, hcall, FinishGrowCall.oldBuf,
      ite_true, pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩; change _ at hq; rw [(rfl : (104#64 : BitVec 64).toNat = 104), (rfl : (8#64 : BitVec 64).toNat = 8)] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 104), ?_⟩; by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      have hq' : sf.mem ⊨ ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          ((A.pool ∗ stackAt s0.sp finishGrowStackX ∗ out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗ (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
      rw [satisfies_pure_sepConj] at hq'; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hq'.1.2, hq'.2⟩
    · simp only [htag, ite_false] at hq ⊢
      have hq' : sf.mem ⊨ ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          ((A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104) ∗ A.pool ∗ stackAt s0.sp finishGrowStackX ∗
            out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗ (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
      rw [satisfies_pure_sepConj] at hq'; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hq'.1.1, hq'.1.2.1, hq'.1.2.2.2⟩, by simpa only [sepConj_assoc] using hq'.2⟩

private theorem finish_grow_104_ne_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.finishGrowSpecX A))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base (withLsCodeLoaded lsmpl (finishGrow104NeSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_map' hfg (fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpre => ?_)
  simp only [finishGrow104NeSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩; subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 8#64, 104#64, bs⟩
  have hlay : LayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat :=
    ⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, by change new.toNat * 104 + 8 ≤ 2 ^ 63; omega⟩
  have hm104 : (104#64 : BitVec 64).toNat = 104 := rfl; have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
  refine ⟨hcall, R, ?_, fun sf hq => ?_⟩
  · simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩; rw [hm104, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, Nat.le_refl _, hle, hpos, by decide, hlay⟩, by simpa only [sepConj_assoc] using hmem⟩
  · simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrow104NeSpecX, hcall, FinishGrowCall.oldBuf,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩; rw [hm104, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 104), ?_⟩; by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      have hq' : sf.mem ⊨ ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          ((A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp finishGrowStackX ∗
            out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗ (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
      rw [satisfies_pure_sepConj] at hq'; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq'.1.2, by simpa only [sepConj_assoc] using hq'.2⟩
    · simp only [htag, ite_false] at hq ⊢
      have hq' : sf.mem ⊨ ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          ((A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗ memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length) ∗
            A.pool ∗ stackAt s0.sp finishGrowStackX ∗ out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗ (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
      rw [satisfies_pure_sepConj] at hq'; rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hq'.1.1, hq'.1.2.1, hq'.1.2.2.2⟩, by simpa only [sepConj_assoc] using hq'.2⟩

/-- Relocatable `<alloc::raw_vec::RawVec<Chain>>::grow_one` contract on Block `43` at `growOneChainStackX` (`16896` B). -/
def GrowOneChainPlacedOkX [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base (withLsCodeLoaded lsmpl (growOneChainSpecX A))

set_option maxHeartbeats 800000 in
/-- Relocatable `<alloc::raw_vec::RawVec<Chain>>::grow_one` (Block `43`) meets `withLsCodeLoaded lsmpl (growOne104SpecX A)` under `AllocContractsPlaced A H`. -/
theorem grow_one_104_placed_ok_ext_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsPlaced A H) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base (withLsCodeLoaded lsmpl (growOne104SpecX A)) := by
  have hpanic : ((blkPC_43).rebase (blkPl_43).base H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked := hA.externAt_handle_error
  simp only [withLsCodeLoaded, growOne104SpecX, stackAt_grow_one_104_x, sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0; obtain ⟨v, cap, ptr, bs⟩ := x; dsimp only at *
  have hfg := finish_grow_placed_ok_ext_x hA
  have hfg0_cl : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (lsmpl.base 45) (withLsCl lsmpl (finishGrow104ZeroSpecX A)) :=
    ls_subroutine_ok_cl_of_callee (j := 45) (finish_grow_104_zero_placed_ok_x hfg)
  have hfg1_cl : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (lsmpl.base 45) (withLsCl lsmpl (finishGrow104NeSpecX A)) :=
    ls_subroutine_ok_cl_of_callee (j := 45) (finish_grow_104_ne_placed_ok_x hfg)
  have hnew_eq : (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) = BitVec.ofNat 64 (max (2 * cap.toNat) 4) := grow_104_new_cap_eq (by omega)
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * 104 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0; have hbs := List.eq_nil_of_length_eq_zero ‹bs.length = (0#64 : BitVec 64).toNat * 104›; subst hbs
    simp only [BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil, BitVec.add_zero, BitVec.toNat_zero, Nat.mul_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP_lscl_local ‹_› (mid := lsmpl.base 45)
    wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl1
    have hfg0_call := lscall_of_withLsCl hfg0_cl hcl1
    wpp_call hfg0_call (x := (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64))
    refine SepWPp.ite_elim_pure1 (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag; apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using allowPanic_panicked
        (CryptoVerification.LibsignalSession.RawVecGrowOne.allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · subst hw0; rw [sepConj_assoc]; apply SepWPp.of_sepWP_ret; wp_steps; wp_done
  · have hcap0' : cap ≠ 0 := hcap0; simp only [hcap0', ite_false, sepConj_assoc]
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = new.toNat * 104 - bs.length := by
      rw [Nat.sub_mul, hnew_toNat, ‹bs.length = cap.toNat * 104›]
    rw [hsub_mul]; apply SepWPp.of_sepWP_lscl_local ‹_› (mid := lsmpl.base 45)
    wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl1
    have hfg1_call := lscall_of_withLsCl hfg1_cl hcl1
    wpp_call hfg1_call (x := (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64))
    refine SepWPp.ite_elim_pure2 (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag; rw [sepConj_assoc]; apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using allowPanic_panicked
        (CryptoVerification.LibsignalSession.RawVecGrowOne.allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · subst hw0; rw [sepConj_assoc, sepConj_assoc]; apply SepWPp.of_sepWP_ret; wp_steps; wp_done

/-- `<alloc::raw_vec::RawVec<Chain>>::grow_one` meets `GrowOneChainPlacedOkX A H` under `AllocContractsPlaced A H`. -/
theorem growOneChain_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsPlaced A H) :
    GrowOneChainPlacedOkX A H := grow_one_104_placed_ok_ext_x hA

theorem growOneChain_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] (h : GrowOneChainPlacedOkX A H) :
    subroutine_ok callerProg (lsmpl.base 43) (withLsCl lsmpl (growOneChainSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (j := 43) h

end Placed

end Proofs.libsignal.Stage1X
