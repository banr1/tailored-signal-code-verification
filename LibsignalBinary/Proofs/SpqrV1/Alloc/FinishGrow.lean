/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.InImageLift
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import ProofLib.SepLogic.WPp

/-!
# `<alloc::raw_vec::RawVecInner>::finish_grow` (`[local#2, 4, 6, 7]`)

Verifies the four `RawVecInner::finish_grow` monomorphizations in SPQR V1 (`[local#7]` generic
`(stride, align)`, `[local#2, 4]` with `stride = 1, align = 1`, and `[local#6]` with
`stride = 32, align = 8`) under `AllocContracts`, `AllocContractsX`, and `[LibsignalPlacement]`
(blocks 361, 160, 221, and 259).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev finishGrow8Name : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]"

abbrev finishGrow2Name : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [local#2]"

abbrev finishGrow4Name : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [local#4]"

abbrev finishGrow7Name : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]"

/-- Stack budget of 32-byte-frame `finish_grow` instances (`allocHookStack + 32`). -/
abbrev finishGrow32Stack : Nat := allocHookStack + 32

/-- Stack budget of 32-byte-frame `finish_grow` instances under `AllocContractsX` (`extHookStack + 32`). -/
abbrev finishGrow32StackX : Nat := extHookStack + 32

/-! ## Optional-Image (`OptCallInv`) Combinators and Hook Adapters -/

abbrev OptCallInv := CryptoVerification.InImageLift.OptCallInv

/-- Conjoins `⌜OptCallInv img? s⌝` to `spec.pre` (`spec.inImage img` at `some img`, `spec` at `none`). -/
def Spec.withOptInv {α : Type} (spec : Spec α) (img? : Option Obj.Image) : Spec α :=
  { spec with pre := fun x s => ⌜OptCallInv img? s⌝ ∗ spec.pre x s }

theorem Spec.withOptInv_some_eq {α : Type} (spec : Spec α) (img : Obj.Image) :
    Spec.withOptInv spec (some img) = spec.inImage img :=
  rfl

theorem subroutine_ok_of_withOptInv_none {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (h : subroutine_ok P addr (Spec.withOptInv spec none)) :
    subroutine_ok P addr spec := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  refine h.mono_outcome x R s0 hpc hrun ?_ hal (fun _ hout => hout)
  dsimp only [Spec.withOptInv, OptCallInv, CryptoVerification.InImageLift.OptCallInv]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨trivial, hpre⟩

theorem subroutine_ok_withOptInv_none_of {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (h : subroutine_ok P addr spec) :
    subroutine_ok P addr (Spec.withOptInv spec none) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  dsimp only [Spec.withOptInv, OptCallInv, CryptoVerification.InImageLift.OptCallInv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hal (fun _ hout => hout)

theorem SepWP.seq_optInv {prog : Program} {img? : Option Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : OptCallInv img? s)
    (h : SepWP prog mid s P (fun sm Pm => OptCallInv img? sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP reaches_pc
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · rcases (hnext (CryptoVerification.InImageLift.OptCallInv.of_steps hinv hsteps)).elim hmm
        (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hpost⟩ | ⟨hoom, hf⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, Pf, hmf, hpost⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr ⟨hoom, hf⟩⟩
  · exact ⟨sm, hsteps, Or.inr ⟨hoom, hf⟩⟩

theorem SepWPp.of_sepWP_optInv {prog : Program} {img? : Option Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : OptCallInv img? s)
    (h : SepWP prog mid s P (fun sm Pm => OptCallInv img? sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (CryptoVerification.InImageLift.OptCallInv.of_steps hinv hsteps) R hmm
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hf⟩)⟩

/-- Stack-equipped no-op shim specification at `hookStack`. -/
def session2ShimSpecWithStack (hookStack : Nat) : Spec Unit where
  pre := fun _ s => stackAt s.sp hookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp hookStack

/-- Stack-equipped `memcpy` specification at `hookStack`. -/
def session2MemcpySpecWithStack (hookStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
      stackAt s0.sp hookStack

theorem shim_ok_opt_of_contracts {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {name : String} {k : Nat} (hookStack : Nat := allocHookStack)
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2") :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) none) := by
  refine subroutine_ok_withOptInv_none_of ?_
  have h := subroutine_ok_withStack_of_subroutine_ok (shim_ok_at2_ext hA hk) hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack noAllocShimSpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, noAllocShimSpec, sessionShimSpec, session2ShimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  exact h.mono_outcome x R s0 hpc hrun hpre' hal (fun _ hout => hout)

theorem memcpy_ok_opt_of_contracts {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {name : String} {k : Nat} (hookStack : Nat := allocHookStack)
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy") :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (session2MemcpySpecWithStack hookStack) none) := by
  refine subroutine_ok_withOptInv_none_of ?_
  have h := subroutine_ok_withStack_of_subroutine_ok (memcpy_ok_at2_ext hA hk) hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack framelessMemcpySpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, framelessMemcpySpec, memcpyRegionSpec, session2MemcpySpecWithStack]
      at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, framelessMemcpySpec, memcpyRegionSpec, session2MemcpySpecWithStack]
      at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem alloc_ok_opt_of_contracts {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc") :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (rustAllocSpecWithStack A allocHookStack) none) :=
  subroutine_ok_withOptInv_none_of (alloc_ok_at_norm_ext hA hk)

theorem realloc_ok_opt_of_contracts {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc") :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (rustReallocExternSpecWithStack A allocHookStack) none) :=
  subroutine_ok_withOptInv_none_of
    (rustReallocExternWithStack_of_rustRealloc (realloc_ok_at_norm_ext hA hk)
      (by decide) (by decide))

/-! ## Arithmetic and Memory Helpers -/

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

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  change new.toNat = 0 at ht
  omega

theorem lsr59_eq_zero {new : BitVec 64} (h : new.toNat * 32 + 8 ≤ 2 ^ 63) :
    new >>> 59 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (by omega)

theorem lsl5_toNat {x : BitVec 64} (h : x.toNat * 32 < 2 ^ 64) :
    (x <<< 5).toNat = x.toNat * 32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change (x.toNat * 32) % 2 ^ 64 = x.toNat * 32
  exact Nat.mod_eq_of_lt h

theorem lsl5_eq_ofNat {x : BitVec 64} (h : x.toNat * 32 < 2 ^ 64) :
    x <<< 5 = BitVec.ofNat 64 (x.toNat * 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [lsl5_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem lsl5_ne_zero {new : BitVec 64} (h0 : 0 < new.toNat) (h : new.toNat * 32 < 2 ^ 64) :
    new <<< 5 ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [lsl5_toNat h] at ht
  change new.toNat * 32 = 0 at ht
  omega

theorem hi_32_eq_false {new : BitVec 64} (h : new.toNat * 32 + 8 ≤ 2 ^ 63) :
    (9223372036854775800#64).ult (new <<< 5) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, lsl5_toNat (by omega)]
  change ¬ (9223372036854775800 < new.toNat * 32)
  omega

theorem beq_lsl5_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat)
    (h : new.toNat * 32 + 8 ≤ 2 ^ 63) :
    ((new <<< 5) == 0#64) = false :=
  beq_eq_false_iff_ne.mpr (lsl5_ne_zero h0 (by omega))

theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_finishGrow_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp hookStack 6 hhook

private theorem stackAt_finishGrow32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 32) =
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp hookStack 4 hhook

/-! ## `finish_grow [local#7]` (Generic `stride` and `align`) -/

/-- `finishGrowSpec` parameterized by callee `hookStack`. -/
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

private def finishGrow8AllocSpecG (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 48) }

private theorem finish_grow_8_zero_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 48 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (Spec.withOptInv (finishGrow8AllocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow8AllocSpecG finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow8Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% finishGrow8Name) 180
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  subst cap
  subst bs
  have hinv0 : OptCallInv img? s0 := by assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name))
    hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv2
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

private def finishGrow8ReallocSpecG (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A hookStack with
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
      A.pool ∗ stackAt s.sp (hookStack + 48) }

private theorem finish_grow_8_ne_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 48 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (Spec.withOptInv (finishGrow8ReallocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow8ReallocSpecG finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow8Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% finishGrow8Name) 180
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  have hinv0 : OptCallInv img? s0 := by assumption
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
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
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

private theorem finish_grow_8_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 48 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?))
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow8Name)))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (Spec.withOptInv (finishGrowSpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_8_zero_opt_ok hhook hshim halloc).mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [Spec.withOptInv, finishGrowSpecWithStack, finishGrow8AllocSpecG,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine (finish_grow_8_ne_opt_ok hhook hrealloc).mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [Spec.withOptInv, finishGrowSpecWithStack, finishGrow8ReallocSpecG,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

/-- `finish_grow [local#7]` meets `finishGrowSpec A`. -/
theorem finish_grow_8_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrowSpec A) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_8_opt_ok (hookStack := allocHookStack) (by decide)
      (shim_ok_opt_of_contracts hA allocHookStack (by fnoff_eq))
      (alloc_ok_opt_of_contracts hA (by fnoff_eq))
      (realloc_ok_opt_of_contracts hA (by fnoff_eq)))

/-- `finish_grow [local#7]` meets `(finishGrowSpecX A).inImage img`. -/
theorem finish_grow_8_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrow8Name)
      ((finishGrowSpecX A).inImage img) :=
  finish_grow_8_opt_ok (A := A) (b := img.base) (ext := ext)
    (hookStack := extHookStack) (img? := some img) (by decide)
    (shim_ok_at2_ext_x hA (hk := by fnoff_eq))
    (alloc_ok_at_norm_ext_x hA (hk := by fnoff_eq))
    (realloc_ok_at_norm_ext_x hA (hk := by fnoff_eq))

/-! ## `finish_grow [local#2]` and `[local#4]` (`stride = 1, align = 1`) -/

/-- Ghost parameters for fixed-layout `finish_grow` (`[local#2, 4, 6]`). -/
structure FinishGrow1Call where
  out : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  new : BitVec 64
  bs : List (BitVec 8)

/-- Pre-call heap buffer of a `RawVecInner` with `stride = 1, align = 1`. -/
def FinishGrow1Call.oldBuf (A : RustAlloc) (x : FinishGrow1Call) : SepProp :=
  if x.cap = 0#64 then emp
  else
    A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)

/-- `finishGrow1Spec` parameterized by callee `hookStack`. -/
def finishGrow1SpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf A ∗ A.pool ∗ stackAt s.sp (hookStack + 32)
  post := fun x s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ x.new) ∗
      (if tag = 1#64 then
        ⌜p' = 1#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ x.oldBuf A
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' x.new.toNat 1 ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length) (x.new.toNat - x.bs.length)) ∗
      A.pool ∗ stackAt s0.sp (hookStack + 32)

/-- Contract of `finish_grow [local#2, 4]` (`stride = 1, align = 1`) at `finishGrow32Stack`. -/
def finishGrow1Spec (A : RustAlloc) : Spec FinishGrow1Call where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf A ∗ A.pool ∗ stackAt s.sp finishGrow32Stack
  post := fun x s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ x.new) ∗
      (if tag = 1#64 then
        ⌜p' = 1#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ x.oldBuf A
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' x.new.toNat 1 ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length) (x.new.toNat - x.bs.length)) ∗
      A.pool ∗ stackAt s0.sp finishGrow32Stack

def finishGrow1SpecX (A : RustAlloc) : Spec FinishGrow1Call :=
  finishGrow1SpecWithStack A extHookStack

private def finishGrow1AllocSpecG (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 32) }

private def finishGrow1ReallocSpecG (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (hookStack + 32) }

private theorem finish_grow_2_zero_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow2Name)))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow2Name)))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (Spec.withOptInv (finishGrow1AllocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow1AllocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow2Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% finishGrow2Name) 168
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  subst cap
  subst bs
  have hinv0 : OptCallInv img? s0 := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow2Name))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow2Name))
    hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv2
  wp_call halloc (new.toNat, 1)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf]
    wp_done

private theorem finish_grow_2_ne_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow2Name)))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (Spec.withOptInv (finishGrow1ReallocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow1ReallocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow2Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% finishGrow2Name) 168
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv img? s0 := by assumption
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : LayoutOk cap.toNat 1 := ⟨hcap_pos, hpow, by omega⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow2Name))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf, hcap_ne, ite_false]
    wp_done

private theorem finish_grow_1_opt_of_zero_ne {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hz : subroutine_ok P addr (Spec.withOptInv (finishGrow1AllocSpecG A hookStack) img?))
    (hne : subroutine_ok P addr (Spec.withOptInv (finishGrow1ReallocSpecG A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (finishGrow1SpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [Spec.withOptInv, finishGrow1SpecWithStack, finishGrow1AllocSpecG,
      FinishGrow1Call.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay⟩, hmem⟩
  · refine hne.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [Spec.withOptInv, finishGrow1SpecWithStack, finishGrow1ReallocSpecG,
      FinishGrow1Call.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay⟩, hmem⟩

/-- `finish_grow [local#2]` meets `finishGrow1Spec A`. -/
theorem finish_grow_2_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (finishGrow1Spec A) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_1_opt_of_zero_ne
      (finish_grow_2_zero_opt_ok (hookStack := allocHookStack) (by decide)
        (shim_ok_opt_of_contracts hA allocHookStack (by fnoff_eq))
        (alloc_ok_opt_of_contracts hA (by fnoff_eq)))
      (finish_grow_2_ne_opt_ok (hookStack := allocHookStack) (by decide)
        (realloc_ok_opt_of_contracts hA (by fnoff_eq))))

/-- `finish_grow [local#2]` meets `(finishGrow1SpecX A).inImage img`. -/
theorem finish_grow_2_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrow2Name)
      ((finishGrow1SpecX A).inImage img) :=
  finish_grow_1_opt_of_zero_ne (A := A) (hookStack := extHookStack) (img? := some img)
    (finish_grow_2_zero_opt_ok (A := A) (b := img.base) (ext := ext)
      (hookStack := extHookStack) (img? := some img) (by decide)
      (shim_ok_at2_ext_x hA (hk := by fnoff_eq))
      (alloc_ok_at_norm_ext_x hA (hk := by fnoff_eq)))
    (finish_grow_2_ne_opt_ok (A := A) (b := img.base) (ext := ext)
      (hookStack := extHookStack) (img? := some img) (by decide)
      (realloc_ok_at_norm_ext_x hA (hk := by fnoff_eq)))

private theorem finish_grow_4_zero_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow4Name)))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow4Name)))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (Spec.withOptInv (finishGrow1AllocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow1AllocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow4Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% finishGrow4Name) 168
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  subst cap
  subst bs
  have hinv0 : OptCallInv img? s0 := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow4Name))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow4Name))
    hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv2
  wp_call halloc (new.toNat, 1)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf]
    wp_done

private theorem finish_grow_4_ne_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow4Name)))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (Spec.withOptInv (finishGrow1ReallocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow1ReallocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow4Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% finishGrow4Name) 168
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv img? s0 := by assumption
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : LayoutOk cap.toNat 1 := ⟨hcap_pos, hpow, by omega⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow4Name))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf, hcap_ne, ite_false]
    wp_done

/-- `finish_grow [local#4]` meets `finishGrow1Spec A`. -/
theorem finish_grow_4_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (finishGrow1Spec A) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_1_opt_of_zero_ne
      (finish_grow_4_zero_opt_ok (hookStack := allocHookStack) (by decide)
        (shim_ok_opt_of_contracts hA allocHookStack (by fnoff_eq))
        (alloc_ok_opt_of_contracts hA (by fnoff_eq)))
      (finish_grow_4_ne_opt_ok (hookStack := allocHookStack) (by decide)
        (realloc_ok_opt_of_contracts hA (by fnoff_eq))))

/-- `finish_grow [local#4]` meets `(finishGrow1SpecX A).inImage img`. -/
theorem finish_grow_4_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrow4Name)
      ((finishGrow1SpecX A).inImage img) :=
  finish_grow_1_opt_of_zero_ne (A := A) (hookStack := extHookStack) (img? := some img)
    (finish_grow_4_zero_opt_ok (A := A) (b := img.base) (ext := ext)
      (hookStack := extHookStack) (img? := some img) (by decide)
      (shim_ok_at2_ext_x hA (hk := by fnoff_eq))
      (alloc_ok_at_norm_ext_x hA (hk := by fnoff_eq)))
    (finish_grow_4_ne_opt_ok (A := A) (b := img.base) (ext := ext)
      (hookStack := extHookStack) (img? := some img) (by decide)
      (realloc_ok_at_norm_ext_x hA (hk := by fnoff_eq)))

/-! ## `finish_grow [local#6]` (`stride = 32, align = 8`) -/

/-- Pre-call heap buffer of a `RawVecInner` with `stride = 32, align = 8`. -/
def FinishGrow1Call.oldBuf32 (A : RustAlloc) (x : FinishGrow1Call) : SepProp :=
  if x.cap = 0#64 then emp
  else
    A.live x.ptr (x.cap.toNat * 32) 8 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat * 32 - x.bs.length)

/-- `finishGrow7Spec` parameterized by callee `hookStack`. -/
def finishGrow7SpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat * 32 ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf32 A ∗ A.pool ∗ stackAt s.sp (hookStack + 32)
  post := fun x s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * 32)) ∗
      (if tag = 1#64 then
        ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ x.oldBuf32 A
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (x.new.toNat * 32) 8 ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length) (x.new.toNat * 32 - x.bs.length)) ∗
      A.pool ∗ stackAt s0.sp (hookStack + 32)

/-- Contract of `finish_grow [local#6]` (`stride = 32, align = 8`) at `finishGrow32Stack`. -/
def finishGrow7Spec (A : RustAlloc) : Spec FinishGrow1Call where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat * 32 ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf32 A ∗ A.pool ∗ stackAt s.sp finishGrow32Stack
  post := fun x s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * 32)) ∗
      (if tag = 1#64 then
        ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ x.oldBuf32 A
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (x.new.toNat * 32) 8 ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length) (x.new.toNat * 32 - x.bs.length)) ∗
      A.pool ∗ stackAt s0.sp finishGrow32Stack

def finishGrow7SpecX (A : RustAlloc) : Spec FinishGrow1Call :=
  finishGrow7SpecWithStack A extHookStack

private def finishGrow7AllocSpecG (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow7SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 32) }

private def finishGrow7ReallocSpecG (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow7SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * 32 ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr (x.cap.toNat * 32) 8 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat * 32 - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (hookStack + 32) }

private theorem finish_grow_7_zero_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow7Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow7Name)))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow7Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow7Name)))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow7Name)
      (Spec.withOptInv (finishGrow7AllocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow7AllocSpecG finishGrow7SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow7Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% finishGrow7Name) 164
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  subst cap
  subst bs
  have hinv0 : OptCallInv img? s0 := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat * 32 + 8 ≤ 2 ^ 63 := by omega
  have hlt64 : new.toNat * 32 < 2 ^ 64 := by omega
  have hlsr59 := lsr59_eq_zero (new := new) (by omega)
  have hhi := hi_32_eq_false (new := new) (by omega)
  have hcbz := beq_lsl5_zero_eq_false hnew_pos (by omega)
  have hlsl : (new <<< 5).toNat = new.toNat * 32 := lsl5_toNat hlt64
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk (new.toNat * 32) 8 := ⟨by omega, hpow, hnew_bound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% finishGrow7Name))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% finishGrow7Name))
    hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv2
  wp_call halloc (new.toNat * 32, 8)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    have hlsl_bv : new <<< 5 = BitVec.ofNat 64 (new.toNat * 32) := lsl5_eq_ofNat hlt64
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · have hlsl_bv : new <<< 5 = BitVec.ofNat 64 (new.toNat * 32) := lsl5_eq_ofNat hlt64
    simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 8#64
    simp only [ite_true, FinishGrow1Call.oldBuf32]
    wp_done

private theorem finish_grow_7_ne_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 32 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow7Name +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow7Name)))
      (Spec.withOptInv (rustReallocExternSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow7Name)
      (Spec.withOptInv (finishGrow7ReallocSpecG A hookStack) img?) := by
  unfold Spec.withOptInv finishGrow7ReallocSpecG finishGrow7SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn := (ls_lemma% fnOff finishGrow7Name)
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% finishGrow7Name) 164
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv img? s0 := by assumption
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * 32 := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat * 32 + 8 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hlt64 : new.toNat * 32 < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * 32 ≤ new.toNat * 32 := Nat.mul_le_mul_right 32 hcap_le_new
  have hcap_lt64 : cap.toNat * 32 < 2 ^ 64 := by omega
  have hlsr59 := lsr59_eq_zero (new := new) (by omega)
  have hhi := hi_32_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hlsl_cap : (cap <<< 5).toNat = cap.toNat * 32 := lsl5_toNat hcap_lt64
  have hlsl_new : (new <<< 5).toNat = new.toNat * 32 := lsl5_toNat hlt64
  have hle_new : bs.length ≤ new.toNat * 32 := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay_old : LayoutOk (cap.toNat * 32) 8 := ⟨by omega, hpow, by omega⟩
  have hlay : LayoutOk (new.toNat * 32) 8 := ⟨by omega, hpow, hnew_bound⟩
  apply SepWP.seq_optInv
    (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% finishGrow7Name))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  wp_call hrealloc (ptr, cap.toNat * 32, 8, new.toNat * 32, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    have hlsl_bv : new <<< 5 = BitVec.ofNat 64 (new.toNat * 32) := lsl5_eq_ofNat hlt64
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · have hlsl_bv : new <<< 5 = BitVec.ofNat 64 (new.toNat * 32) := lsl5_eq_ofNat hlt64
    simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 8#64
    simp only [ite_true, FinishGrow1Call.oldBuf32, hcap_ne, ite_false]
    wp_done

private theorem finish_grow_7_opt_of_zero_ne {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hz : subroutine_ok P addr (Spec.withOptInv (finishGrow7AllocSpecG A hookStack) img?))
    (hne : subroutine_ok P addr (Spec.withOptInv (finishGrow7ReallocSpecG A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (finishGrow7SpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [Spec.withOptInv, finishGrow7SpecWithStack, finishGrow7AllocSpecG,
      FinishGrow1Call.oldBuf32, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay⟩, hmem⟩
  · refine hne.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [Spec.withOptInv, finishGrow7SpecWithStack, finishGrow7ReallocSpecG,
      FinishGrow1Call.oldBuf32, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay⟩, hmem⟩

/-- `finish_grow [local#6]` meets `finishGrow7Spec A`. -/
theorem finish_grow_7_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow7Name)
      (finishGrow7Spec A) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_7_opt_of_zero_ne
      (finish_grow_7_zero_opt_ok (hookStack := allocHookStack) (by decide)
        (shim_ok_opt_of_contracts hA allocHookStack (by fnoff_eq))
        (alloc_ok_opt_of_contracts hA (by fnoff_eq)))
      (finish_grow_7_ne_opt_ok (hookStack := allocHookStack) (by decide)
        (realloc_ok_opt_of_contracts hA (by fnoff_eq))))

/-- `finish_grow [local#6]` meets `(finishGrow7SpecX A).inImage img`. -/
theorem finish_grow_7_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrow7Name)
      ((finishGrow7SpecX A).inImage img) :=
  finish_grow_7_opt_of_zero_ne (A := A) (hookStack := extHookStack) (img? := some img)
    (finish_grow_7_zero_opt_ok (A := A) (b := img.base) (ext := ext)
      (hookStack := extHookStack) (img? := some img) (by decide)
      (shim_ok_at2_ext_x hA (hk := by fnoff_eq))
      (alloc_ok_at_norm_ext_x hA (hk := by fnoff_eq)))
    (finish_grow_7_ne_opt_ok (A := A) (b := img.base) (ext := ext)
      (hookStack := extHookStack) (img? := some img) (by decide)
      (realloc_ok_at_norm_ext_x hA (hk := by fnoff_eq)))

/-! ## Relocatable Contracts (Blocks 361, 160, 221, and 259) -/

theorem session2ShimWithStack_of_noAllocShim {prog : Program} {addr : BitVec 64}
    (hookStack : Nat) (h : subroutine_ok prog addr noAllocShimSpec) :
    subroutine_ok prog addr (session2ShimSpecWithStack hookStack) := by
  have h' := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack noAllocShimSpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, noAllocShimSpec, sessionShimSpec, session2ShimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  exact h'.mono_outcome x R s0 hpc hrun hpre' hal (fun _ hout => hout)

theorem session2MemcpyWithStack_of_framelessMemcpy {prog : Program} {addr : BitVec 64}
    (hookStack : Nat) (h : subroutine_ok prog addr framelessMemcpySpec) :
    subroutine_ok prog addr (session2MemcpySpecWithStack hookStack) := by
  have h' := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack framelessMemcpySpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, framelessMemcpySpec, memcpyRegionSpec, session2MemcpySpecWithStack]
      at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine h'.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, framelessMemcpySpec, memcpyRegionSpec, session2MemcpySpecWithStack]
      at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ### Block 361: `finish_grow [local#8]` -/

set_option quotPrecheck false in
local notation "finishGrow8AllocSpecG_pub" => fun (A : RustAlloc) (hookStack : Nat) =>
  ({ finishGrowSpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 48) } : Spec FinishGrowCall)

set_option quotPrecheck false in
local notation "finishGrow8ReallocSpecG_pub" => fun (A : RustAlloc) (hookStack : Nat) =>
  ({ finishGrowSpecWithStack A hookStack with
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
      A.pool ∗ stackAt s.sp (hookStack + 48) } : Spec FinishGrowCall)

set_option quotPrecheck false in
local notation "finishGrow1AllocSpecG_pub" => fun (A : RustAlloc) (hookStack : Nat) =>
  ({ finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 32) } : Spec FinishGrow1Call)

set_option quotPrecheck false in
local notation "finishGrow1ReallocSpecG_pub" => fun (A : RustAlloc) (hookStack : Nat) =>
  ({ finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (hookStack + 32) } : Spec FinishGrow1Call)

set_option quotPrecheck false in
local notation "finishGrow7AllocSpecG_pub" => fun (A : RustAlloc) (hookStack : Nat) =>
  ({ finishGrow7SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 32) } : Spec FinishGrow1Call)

set_option quotPrecheck false in
local notation "finishGrow7ReallocSpecG_pub" => fun (A : RustAlloc) (hookStack : Nat) =>
  ({ finishGrow7SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * 32 ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr (x.cap.toNat * 32) 8 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat * 32 - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (hookStack + 32) } : Spec FinishGrow1Call)

theorem finish_grow_8_zero_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrow8AllocSpecG_pub A hookStack) := by
  change subroutine_ok _ _ (finishGrow8AllocSpecG A hookStack)
  unfold finishGrow8AllocSpecG finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  subst cap
  subst bs
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  wp_steps
  wp_call hshim ()
  wp_steps
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

theorem finish_grow_8_ne_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrow8ReallocSpecG_pub A hookStack) := by
  change subroutine_ok _ _ (finishGrow8ReallocSpecG A hookStack)
  unfold finishGrow8ReallocSpecG finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
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
  wp_steps
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

theorem finish_grow_8_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hrealloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrowSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_8_zero_placed_ok_of_hooks hhook hshim halloc).mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [finishGrowSpecWithStack,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine (finish_grow_8_ne_placed_ok_of_hooks hhook hrealloc).mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [finishGrowSpecWithStack,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

/-- Block 361 (`finish_grow [local#8]`) meets `finishGrowSpec A`. -/
theorem finish_grow_8_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrowSpec A) :=
  finish_grow_8_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem hshim))
    (spqr_hook_ok_of_mem halloc)
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem hrealloc) (by decide) (by decide))

theorem finish_grow_8_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrowSpecX A) :=
  finish_grow_8_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (spqr_hook_ok_of_mem halloc) (by decide) (by decide))
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem hrealloc) (by decide) (by decide))

/-! ### Blocks 160 (`[local#2]`) and 221 (`[local#4]`) -/

private theorem finish_grow_1_placed_of_zero_ne {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hz : subroutine_ok P addr (finishGrow1AllocSpecG A hookStack))
    (hne : subroutine_ok P addr (finishGrow1ReallocSpecG A hookStack)) :
    subroutine_ok P addr (finishGrow1SpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [finishGrow1SpecWithStack, finishGrow1AllocSpecG,
      FinishGrow1Call.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay⟩, hmem⟩
  · refine hne.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [finishGrow1SpecWithStack, finishGrow1ReallocSpecG,
      FinishGrow1Call.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay⟩, hmem⟩

theorem finish_grow_2_zero_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (blkPl_160).base
      (finishGrow1AllocSpecG_pub A hookStack) := by
  change subroutine_ok _ _ (finishGrow1AllocSpecG A hookStack)
  unfold finishGrow1AllocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  subst cap
  subst bs
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (new.toNat, 1)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf]
    wp_done

theorem finish_grow_2_ne_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (blkPl_160).base
      (finishGrow1ReallocSpecG_pub A hookStack) := by
  change subroutine_ok _ _ (finishGrow1ReallocSpecG A hookStack)
  unfold finishGrow1ReallocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : LayoutOk cap.toNat 1 := ⟨hcap_pos, hpow, by omega⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  wp_steps
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf, hcap_ne, ite_false]
    wp_done

theorem finish_grow_2_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hrealloc : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (blkPl_160).base
      (finishGrow1SpecWithStack A hookStack) :=
  finish_grow_1_placed_of_zero_ne
    (finish_grow_2_zero_placed_ok_of_hooks hhook hshim halloc)
    (finish_grow_2_ne_placed_ok_of_hooks hhook hrealloc)

/-- Block 160 (`finish_grow [local#2]`) meets `finishGrow1Spec A`. -/
theorem finish_grow_2_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (blkPl_160).base
      (finishGrow1Spec A) :=
  finish_grow_2_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem hshim))
    (spqr_hook_ok_of_mem halloc)
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem hrealloc) (by decide) (by decide))

theorem finish_grow_2_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (blkPl_160).base
      (finishGrow1SpecX A) :=
  finish_grow_2_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (spqr_hook_ok_of_mem halloc) (by decide) (by decide))
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem hrealloc) (by decide) (by decide))

theorem finish_grow_4_zero_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (blkPl_221).base
      (finishGrow1AllocSpecG_pub A hookStack) := by
  change subroutine_ok _ _ (finishGrow1AllocSpecG A hookStack)
  unfold finishGrow1AllocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  subst cap
  subst bs
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (new.toNat, 1)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf]
    wp_done

theorem finish_grow_4_ne_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (blkPl_221).base
      (finishGrow1ReallocSpecG_pub A hookStack) := by
  change subroutine_ok _ _ (finishGrow1ReallocSpecG A hookStack)
  unfold finishGrow1ReallocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : LayoutOk cap.toNat 1 := ⟨hcap_pos, hpow, by omega⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  wp_steps
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf, hcap_ne, ite_false]
    wp_done

theorem finish_grow_4_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hrealloc : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (blkPl_221).base
      (finishGrow1SpecWithStack A hookStack) :=
  finish_grow_1_placed_of_zero_ne
    (finish_grow_4_zero_placed_ok_of_hooks hhook hshim halloc)
    (finish_grow_4_ne_placed_ok_of_hooks hhook hrealloc)

/-- Block 221 (`finish_grow [local#4]`) meets `finishGrow1Spec A`. -/
theorem finish_grow_4_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (blkPl_221).base
      (finishGrow1Spec A) :=
  finish_grow_4_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem hshim))
    (spqr_hook_ok_of_mem halloc)
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem hrealloc) (by decide) (by decide))

theorem finish_grow_4_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (blkPl_221).base
      (finishGrow1SpecX A) :=
  finish_grow_4_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (spqr_hook_ok_of_mem halloc) (by decide) (by decide))
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem hrealloc) (by decide) (by decide))

/-! ### Block 259: `finish_grow [local#7]` (`stride = 32, align = 8`) -/

private theorem finish_grow_7_placed_of_zero_ne {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hz : subroutine_ok P addr (finishGrow7AllocSpecG A hookStack))
    (hne : subroutine_ok P addr (finishGrow7ReallocSpecG A hookStack)) :
    subroutine_ok P addr (finishGrow7SpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [finishGrow7SpecWithStack, finishGrow7AllocSpecG,
      FinishGrow1Call.oldBuf32, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay⟩, hmem⟩
  · refine hne.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ hout => hout)
    simp only [finishGrow7SpecWithStack, finishGrow7ReallocSpecG,
      FinishGrow1Call.oldBuf32, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay⟩, hmem⟩

theorem finish_grow_7_zero_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (blkPl_259).base
      (finishGrow7AllocSpecG_pub A hookStack) := by
  change subroutine_ok _ _ (finishGrow7AllocSpecG A hookStack)
  unfold finishGrow7AllocSpecG finishGrow7SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  subst cap
  subst bs
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat * 32 + 8 ≤ 2 ^ 63 := by omega
  have hlt64 : new.toNat * 32 < 2 ^ 64 := by omega
  have hlsr59 := lsr59_eq_zero (new := new) (by omega)
  have hhi := hi_32_eq_false (new := new) (by omega)
  have hcbz := beq_lsl5_zero_eq_false hnew_pos (by omega)
  have hlsl : (new <<< 5).toNat = new.toNat * 32 := lsl5_toNat hlt64
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk (new.toNat * 32) 8 := ⟨by omega, hpow, hnew_bound⟩
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (new.toNat * 32, 8)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    have hlsl_bv : new <<< 5 = BitVec.ofNat 64 (new.toNat * 32) := lsl5_eq_ofNat hlt64
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · have hlsl_bv : new <<< 5 = BitVec.ofNat 64 (new.toNat * 32) := lsl5_eq_ofNat hlt64
    simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 8#64
    simp only [ite_true, FinishGrow1Call.oldBuf32]
    wp_done

theorem finish_grow_7_ne_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (blkPl_259).base
      (finishGrow7ReallocSpecG_pub A hookStack) := by
  change subroutine_ok _ _ (finishGrow7ReallocSpecG A hookStack)
  unfold finishGrow7ReallocSpecG finishGrow7SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * 32 := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat * 32 + 8 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hlt64 : new.toNat * 32 < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * 32 ≤ new.toNat * 32 := Nat.mul_le_mul_right 32 hcap_le_new
  have hcap_lt64 : cap.toNat * 32 < 2 ^ 64 := by omega
  have hlsr59 := lsr59_eq_zero (new := new) (by omega)
  have hhi := hi_32_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hlsl_cap : (cap <<< 5).toNat = cap.toNat * 32 := lsl5_toNat hcap_lt64
  have hlsl_new : (new <<< 5).toNat = new.toNat * 32 := lsl5_toNat hlt64
  have hle_new : bs.length ≤ new.toNat * 32 := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay_old : LayoutOk (cap.toNat * 32) 8 := ⟨by omega, hpow, by omega⟩
  have hlay : LayoutOk (new.toNat * 32) 8 := ⟨by omega, hpow, hnew_bound⟩
  wp_steps
  wp_call hrealloc (ptr, cap.toNat * 32, 8, new.toNat * 32, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    have hlsl_bv : new <<< 5 = BitVec.ofNat 64 (new.toNat * 32) := lsl5_eq_ofNat hlt64
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · have hlsl_bv : new <<< 5 = BitVec.ofNat 64 (new.toNat * 32) := lsl5_eq_ofNat hlt64
    simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 8#64
    simp only [ite_true, FinishGrow1Call.oldBuf32, hcap_ne, ite_false]
    wp_done

theorem finish_grow_7_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hrealloc : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (blkPl_259).base
      (finishGrow7SpecWithStack A hookStack) :=
  finish_grow_7_placed_of_zero_ne
    (finish_grow_7_zero_placed_ok_of_hooks hhook hshim halloc)
    (finish_grow_7_ne_placed_ok_of_hooks hhook hrealloc)

/-- Block 259 (`finish_grow [local#7]`) meets `finishGrow7Spec A`. -/
theorem finish_grow_7_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (blkPl_259).base
      (finishGrow7Spec A) :=
  finish_grow_7_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem hshim))
    (spqr_hook_ok_of_mem halloc)
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem hrealloc) (by decide) (by decide))

theorem finish_grow_7_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (blkPl_259).base
      (finishGrow7SpecX A) :=
  finish_grow_7_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (spqr_hook_ok_of_mem halloc) (by decide) (by decide))
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem hrealloc) (by decide) (by decide))

end CryptoVerification.SpqrV1.Alloc
