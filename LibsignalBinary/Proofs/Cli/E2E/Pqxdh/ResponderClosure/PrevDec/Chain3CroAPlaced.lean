/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Chain3Placed
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.Core

/-!
# `GrowOneChain` and `VerNe.Chain3` (Block `516`) Part A under `LibsignalCodeRoLoaded`

Verifies `<alloc::raw_vec::RawVec<Chain>>::grow_one` (Block `43`) without `memmove`, establishes
`Rust.withPanics ext` extern equivalence on `libsignalSessionExterns`, and proves the `Entry`,
`Exit`, and framework lemmas for `message::merge<Chain> [local#4]` (Block `516`) under
`StoreKit.LibsignalCodeRoLoaded lsmpl`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi
open Proofs.libsignal.Hooks2
  (subroutine_ok_withLsCodeLoaded_map' subroutine_ok_withLsCl_map'
   subroutine_ok_withLsCl_withHookStack_mono)
open Proofs.libsignal.Stage1X
  (growOneChainStackX growOne104SpecX growOneChainSpecX lscall_of_withLsCl)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

/-! ## `Rust.withPanics` Equivalence on Libsignal Session Externs -/

private theorem libsignalSessionExterns_notPanic :
    (libsignalSessionExterns.all fun sym => !Rust.isPanicSymbol sym) = true := by
  simp [libsignalSessionExterns, Rust.isPanicSymbol]

theorem isPanicSymbol_false_of_mem_lsExterns {sym : String}
    (h : sym ∈ libsignalSessionExterns) : Rust.isPanicSymbol sym = false := by
  have h1 := List.all_eq_true.mp libsignalSessionExterns_notPanic sym h
  simpa using h1

theorem withPanics_apply_lsExtern {ext : LibsignalHooks} {sym : String}
    (h : sym ∈ libsignalSessionExterns) :
    Rust.withPanics ext sym = ext sym := by
  simp only [Rust.withPanics, isPanicSymbol_false_of_mem_lsExterns h, Bool.false_eq_true, ↓reduceIte]

theorem hookSat_withPanics_of_mem {α : Type} {ext : LibsignalHooks} {sym : String} {spec : Spec α}
    (hmem : sym ∈ libsignalSessionExterns) (hsat : HookSat ext sym spec) :
    HookSat (Rust.withPanics ext) sym spec := by
  unfold HookSat at hsat ⊢
  rwa [withPanics_apply_lsExtern hmem]

/-- Any two `IsLsBlockProg` programs over `Rust.withPanics ext` and `ext` have identical `externAt?`,
since no symbol in `libsignalSessionExterns` is a demangled `Rust.isPanicSymbol`. -/
theorem ls_externAt?_withPanics_eq [LibsignalPlacement] {prog1 prog2 : Program} {i j : Nat}
    {ext : LibsignalHooks}
    [hp1 : IsLsBlockProg prog1 i (Rust.withPanics ext)]
    [hp2 : IsLsBlockProg prog2 j ext] :
    ∀ pc, prog1.externAt? pc = prog2.externAt? pc := by
  intro a
  rw [hp1.eq_blockProgram, hp2.eq_blockProgram]
  dsimp only [Program.externAt?, Program.hookAtOff?, Obj.MultiPlacedLib.blockProgram,
    Obj.MultiPlacedLib.blockPlacement, Obj.PlacedLib.program]
  have hnone : ∀ {α β : Type} (l : List α), l.findSome? (fun _ => (none : Option β)) = none := by
    intro α β l; induction l with | nil => rfl | cons _ _ ih => exact ih
  simp only [ite_self, hnone, Option.or_none]
  rw [hp1.externs_eq, hp2.externs_eq]
  have hfind :
      ∀ (es : List String) (hes : ∀ e ∈ es, Rust.isPanicSymbol e = false) (b1 b2 : BitVec 64),
        (es.map (fun e => (e, (libsignalSessionLib.resolve lsmpl e - b1).toNat))).findSome?
          (fun p => if (p.2 == (a - b1).toNat) = true then Rust.withPanics ext p.1 else none) =
        (es.map (fun e => (e, (libsignalSessionLib.resolve lsmpl e - b2).toNat))).findSome?
          (fun p => if (p.2 == (a - b2).toNat) = true then ext p.1 else none) := by
    intro es hes b1 b2
    induction es with
    | nil => rfl
    | cons e rest ih =>
      simp only [List.map_cons, List.findSome?_cons]
      have hcond :
          ((libsignalSessionLib.resolve lsmpl e - b1).toNat == (a - b1).toNat) =
          ((libsignalSessionLib.resolve lsmpl e - b2).toNat == (a - b2).toNat) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, BitVec.toNat_inj]
        constructor <;> intro h <;> bv_omega
      have he : Rust.withPanics ext e = ext e := by
        simp [Rust.withPanics, hes e (List.mem_cons_self ..)]
      rw [hcond, he, ih (fun x hx => hes x (List.mem_cons_of_mem _ hx))]
  exact hfind libsignalSessionExterns (fun _ h => isPanicSymbol_false_of_mem_lsExterns h)
    (lsmpl.base i) (lsmpl.base j)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `GrowOneChain` (Block `43`) Without `memmove` -/

private theorem sessionShim_of_noAllocShim_local {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym noAllocShimSpec) :
    HookSat H sym sessionShimSpec := by
  obtain ⟨f, hf, hsat⟩ := h
  refine ⟨f, hf, fun x R s0 hrun hpre hal => ?_⟩
  have hpre' : s0.mem ⊨ noAllocShimSpec.pre () s0 ∗ R := by
    dsimp only [sessionShimSpec, noAllocShimSpec] at hpre ⊢
    simpa only [pure_true, emp_sepConj] using hpre
  exact hsat () R s0 hrun hpre' hal

/-- Minimal allocator bundle for `RawVec<Chain>::grow_one` (no `dealloc` or `memmove`). -/
structure GrowAllocPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  alloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustAllocSpecWithStack A extHookStack))
  realloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustReallocSym)
      (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack A extHookStack))
  shim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
      (withLsCl lsmpl Proofs.libsignal.Stage1X.session2ShimSpecX)
  panic_handle_error : H lsHandleErrorSym = some Rust.panicked

theorem GrowAllocPlaced.of_hooks [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked) :
    GrowAllocPlaced A H where
  alloc := fun {callerProg callerBlk _} => by
    have h0 := ls_subroutine_ok_cl_of_plain_prog (pl := lsmpl) (prog := callerProg)
      (rustAllocWithStack_of_rustAlloc (hookStack := extHookStack) (ls_hook_ok_of_caller halloc) (by decide) (by decide))
    refine subroutine_ok_withLsCl_map' h0 fun ⟨size, align⟩ R s0 hpre => ⟨(size, align), R, ?_, fun sf hpost => ?_⟩
    · dsimp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack] at hpre ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · dsimp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  realloc := fun {callerProg callerBlk _} => by
    have h0 := ls_subroutine_ok_cl_of_plain_prog (pl := lsmpl) (prog := callerProg)
      (rustReallocExternWithStack_of_rustRealloc (hookStack := extHookStack) (ls_hook_ok_of_caller hrealloc) (by decide) (by decide))
    refine subroutine_ok_withLsCl_map' h0 fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre => ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩
    · dsimp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack, CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack] at hpre ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, hlay_old, hlay_new⟩, hmem⟩ := hpre
      exact ⟨⟨hx0, hx1, hx2, hx3, hlay_old, hlay_new, hbs1, hbs2⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem⟩
    · dsimp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack, Proofs.libsignal.Stage1X.rustReallocSpecWithStack,
        CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack, CryptoVerification.LibsignalTripleRatchet.rustReallocSpecWithStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  shim := fun {callerProg callerBlk _} => by
    have hsh := sessionShim_of_noAllocShim_local hshim
    have h0 : subroutine_ok callerProg (lsρ lsRustNoAllocShimSym) (withLsCl lsmpl (sessionShimSpec.withHookStack 0)) := by
      refine subroutine_ok_withLsCl_map' (ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hsh)) fun x R s0 hpre =>
        ⟨x, stackAt s0.sp 0 ∗ R, ?_, fun sf hpost => ?_⟩
      · dsimp only [Spec.withHookStack] at hpre; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
      · dsimp only [Spec.withHookStack]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    exact subroutine_ok_withLsCl_withHookStack_mono (by decide) (by decide) h0
  panic_handle_error := hpan_err

theorem GrowAllocPlaced.externAt_handle_error [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : GrowAllocPlaced A H) {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    callerProg.externAt? (lsρ lsHandleErrorSym) = some Rust.panicked :=
  (ls_externAt?_of_caller (sym := lsHandleErrorSym) (by decide)).trans hA.panic_handle_error

private def finishGrowZeroSpec2X (A : RustAlloc) : Spec FinishGrowCall :=
  { Proofs.libsignal.Stage1X.finishGrowSpecX A with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp Proofs.libsignal.Stage1X.finishGrowStackX }

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

private abbrev FG48Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

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
      (if tag = 1#64 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          (A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104))) ∗
      A.pool ∗ stackAt fsp Proofs.libsignal.Stage1X.finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private def finishGrow104NeSpecX (A : RustAlloc) : Spec FG48Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length = cap.toNat * 104 ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt fsp Proofs.libsignal.Stage1X.finishGrowStackX
  post := fun (out, _cap, ptr, new, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ (A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs))
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          (A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length))) ∗
      A.pool ∗ stackAt fsp Proofs.libsignal.Stage1X.finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

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
  rw [Nat.div_eq_of_lt (by omega)]; rfl

private theorem mul_stride_toNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq; have ht := congrArg BitVec.toNat heq; rw [mul_stride_toNat h] at ht
  change new.toNat * stride.toNat = 0 at ht; omega

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]; · simp
    · rw [BitVec.le_def]; change align.toNat ≤ 2 ^ 63; omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat (by omega)]; omega

private theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private abbrev memRegion_24_cells := memRegion_24

private theorem stackAt_finishGrowX (sp : BitVec 64) :
    stackAt sp Proofs.libsignal.Stage1X.finishGrowStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  LibsignalTripleRatchet.stackAt_split_cells sp 16384 6 (by decide)

private theorem ite_elim_pure1_grow {prog : Program} {ret : BitVec 64} {s : State}
    {c : Prop} [Decidable c] {φ ψ : Prop} {R2 F : SepProp} {Q Qp : State → SepProp → Prop}
    (hthen : c → φ → SepWPp prog ret s F Q Qp)
    (helse : ¬ c → ψ → SepWPp prog ret s (R2 ∗ F) Q Qp) :
    SepWPp prog ret s ((if c then ⌜φ⌝ else ⌜ψ⌝ ∗ R2) ∗ F) Q Qp := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact SepWPp.pure_elim (hthen hc)
  · simp only [hc, ite_false, sepConj_assoc]; exact SepWPp.pure_elim (helse hc)

private theorem ite_elim_pure2_grow {prog : Program} {ret : BitVec 64} {s : State}
    {c : Prop} [Decidable c] {φ ψ : Prop} {R1 R2 F : SepProp} {Q Qp : State → SepProp → Prop}
    (hthen : c → φ → SepWPp prog ret s (R1 ∗ F) Q Qp)
    (helse : ¬ c → ψ → SepWPp prog ret s (R2 ∗ F) Q Qp) :
    SepWPp prog ret s ((if c then ⌜φ⌝ ∗ R1 else ⌜ψ⌝ ∗ R2) ∗ F) Q Qp := by
  by_cases hc : c
  · simp only [hc, ite_true, sepConj_assoc]; exact SepWPp.pure_elim (hthen hc)
  · simp only [hc, ite_false, sepConj_assoc]; exact SepWPp.pure_elim (helse hc)

private def growPad104X (sp : BitVec 64) : SepProp := memRegion (sp - 16896#64) 400

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
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by cells_unfold
  rw [h1, h2, hc8]

private theorem grow_104_new_cap_eq {cap : BitVec 64}
    (h : max (2 * cap.toNat) 4 * 104 ≤ 9223372036854775800) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change 4 < 2 * cap.toNat at hc; omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change ¬ 4 < 2 * cap.toNat at hc
    change 4 = max (2 * cap.toNat) 4; omega

private theorem sepWPp_of_sepWP_lscl_grow {pl : Obj.MultiPlacement} {prog : Program}
    {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm => LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL; rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ := hnext (hcl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hf⟩)⟩

set_option maxHeartbeats 800000 in
private theorem finish_grow_zero_of_growAlloc [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : GrowAllocPlaced A H) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowZeroSpec2X A)) := by
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
private theorem finish_grow_ne_of_growAlloc [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : GrowAllocPlaced A H) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowNeSpec2X A)) := by
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

private theorem finish_grow_of_growAlloc [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : GrowAllocPlaced A H) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.finishGrowSpecX A)) := by
  intro x R s0 hpc hrun hpre hsp; have ⟨hcl0, hpre0⟩ := extract_withLsCodeLoaded hpre
  by_cases hcap0 : x.cap = 0#64
  · refine finish_grow_zero_of_growAlloc hA x R s0 hpc hrun ?_ hsp
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; refine ⟨hcl0, ?_⟩
    simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrowZeroSpec2X, FinishGrowCall.oldBuf,
      hcap0, ite_true, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine finish_grow_ne_of_growAlloc hA x R s0 hpc hrun ?_ hsp
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; refine ⟨hcl0, ?_⟩
    simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrowNeSpec2X, FinishGrowCall.oldBuf,
      hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

private theorem finish_grow_104_zero_of_fg [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.finishGrowSpecX A))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrow104ZeroSpecX A)) := by
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
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  · simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrow104ZeroSpecX, hcall, FinishGrowCall.oldBuf,
      ite_true, pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩; change _ at hq; rw [(rfl : (104#64 : BitVec 64).toNat = 104), (rfl : (8#64 : BitVec 64).toNat = 8)] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 104), ?_⟩; by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      have hq' : sf.mem ⊨ ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          ((A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX ∗ out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗ (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
      rw [satisfies_pure_sepConj] at hq'; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hq'.1.2, hq'.2⟩
    · simp only [htag, ite_false] at hq ⊢
      have hq' : sf.mem ⊨ ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          ((A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104) ∗ A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX ∗
            out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗ (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
      rw [satisfies_pure_sepConj] at hq'; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hq'.1.1, hq'.1.2.1, hq'.1.2.2.2⟩, by simpa only [sepConj_assoc] using hq'.2⟩

private theorem finish_grow_104_ne_of_fg [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.finishGrowSpecX A))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrow104NeSpecX A)) := by
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
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, Nat.le_refl _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  · simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrow104NeSpecX, hcall, FinishGrowCall.oldBuf,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩; rw [hm104, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 104), ?_⟩; by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      have hq' : sf.mem ⊨ ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          ((A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX ∗
            out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗ (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
      rw [satisfies_pure_sepConj] at hq'; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq'.1.2, by simpa only [sepConj_assoc] using hq'.2⟩
    · simp only [htag, ite_false] at hq ⊢
      have hq' : sf.mem ⊨ ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          ((A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗ memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length) ∗
            A.pool ∗ stackAt s0.sp Proofs.libsignal.Stage1X.finishGrowStackX ∗ out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗ (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
      rw [satisfies_pure_sepConj] at hq'; rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hq'.1.1, hq'.1.2.1, hq'.1.2.2.2⟩, by simpa only [sepConj_assoc] using hq'.2⟩

set_option maxHeartbeats 800000 in
theorem grow_one_104_of_growAlloc [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : GrowAllocPlaced A H) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOne104SpecX A)) := by
  have hpanic : ((blkPC_43).rebase (blkPl_43).base H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked :=
    hA.externAt_handle_error
  simp only [withLsCodeLoaded, growOne104SpecX, stackAt_grow_one_104_x, sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0; obtain ⟨v, cap, ptr, bs⟩ := x; dsimp only at *
  have hfg := finish_grow_of_growAlloc hA
  have hfg0_cl : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (lsmpl.base 45) (withLsCl lsmpl (finishGrow104ZeroSpecX A)) :=
    ls_subroutine_ok_cl_of_callee (j := 45) (finish_grow_104_zero_of_fg hfg)
  have hfg1_cl : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (lsmpl.base 45) (withLsCl lsmpl (finishGrow104NeSpecX A)) :=
    ls_subroutine_ok_cl_of_callee (j := 45) (finish_grow_104_ne_of_fg hfg)
  have hnew_eq : (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) = BitVec.ofNat 64 (max (2 * cap.toNat) 4) :=
    grow_104_new_cap_eq (by omega)
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * 104 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0; have hbs := List.eq_nil_of_length_eq_zero ‹bs.length = (0#64 : BitVec 64).toNat * 104›; subst hbs
    simp only [BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil, BitVec.add_zero, BitVec.toNat_zero, Nat.mul_zero, Nat.sub_zero]
    apply sepWPp_of_sepWP_lscl_grow ‹_› (mid := lsmpl.base 45)
    wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl1
    have hfg0_call := lscall_of_withLsCl hfg0_cl hcl1
    wpp_call hfg0_call (x := (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64))
    refine ite_elim_pure1_grow (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag; apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using allowPanic_panicked
        (CryptoVerification.LibsignalSession.RawVecGrowOne.allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · subst hw0; rw [sepConj_assoc]; apply SepWPp.of_sepWP_ret; wp_steps; wp_done
  · have hcap0' : cap ≠ 0 := hcap0; simp only [hcap0', ite_false, sepConj_assoc]
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = new.toNat * 104 - bs.length := by
      rw [Nat.sub_mul, hnew_toNat, ‹bs.length = cap.toNat * 104›]
    rw [hsub_mul]; apply sepWPp_of_sepWP_lscl_grow ‹_› (mid := lsmpl.base 45)
    wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl1
    have hfg1_call := lscall_of_withLsCl hfg1_cl hcl1
    wpp_call hfg1_call (x := (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64))
    refine ite_elim_pure2_grow (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag; rw [sepConj_assoc]; apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using allowPanic_panicked
        (CryptoVerification.LibsignalSession.RawVecGrowOne.allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · subst hw0; rw [sepConj_assoc, sepConj_assoc]; apply SepWPp.of_sepWP_ret; wp_steps; wp_done

/-- `<alloc::raw_vec::RawVec<Chain>>::grow_one` (Block `43`) meets
`withLsCl lsmpl (growOneChainSpecX A)` from the 4 allocator/panic hooks alone (no `memmove`). -/
theorem growOneChain_placed_ok_cl_of_hooks [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok callerProg (lsmpl.base 43) (withLsCl lsmpl (growOneChainSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (j := 43)
    (grow_one_104_of_growAlloc (GrowAllocPlaced.of_hooks hshim halloc hrealloc hpan_err))

/-! ## `VerNe.Chain3` (Block `516`) Framework, `Entry`, and `Exit` -/

section Chain3Cro
open CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.CliHandshake.Placed

/-- Callee contracts for `message::merge<Chain> [local#4]` (Block `516`) where `bytes::merge`
uses `StoreKit.withLsCodeRoLoaded` instead of `withLsCl`. -/
structure Chain3CalleesCroPlacedW [LibsignalPlacement] (ext : LibsignalHooks) : Prop where
  dv : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 515)
    (withLsCl lsmpl (SpqrH.decodeVarint2SpecX A0))
  bm : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 514)
    (StoreKit.withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0))
  grow : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 43)
    (withLsCl lsmpl (growOneChainSpecX A0))

theorem chain3CalleesCro_of_hooks [LibsignalPlacement] {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext lsRustAllocSym (rustAllocSpec A0))
    (hrealloc : HookSat ext lsRustReallocSym (rustReallocSpec A0))
    (hdealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A0))
    (hmc : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : ext lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    Chain3CalleesCroPlacedW ext := by
  have hshim' : HookSat (Rust.withPanics ext) lsRustNoAllocShimSym noAllocShimSpec :=
    hookSat_withPanics_of_mem (by decide) hshim
  have halloc' : HookSat (Rust.withPanics ext) lsRustAllocSym (rustAllocSpec A0) :=
    hookSat_withPanics_of_mem (by decide) halloc
  have hrealloc' : HookSat (Rust.withPanics ext) lsRustReallocSym (rustReallocSpec A0) :=
    hookSat_withPanics_of_mem (by decide) hrealloc
  have hdealloc' : HookSat (Rust.withPanics ext) lsRustDeallocSym (rustDeallocSpec A0) :=
    hookSat_withPanics_of_mem (by decide) hdealloc
  have hmc' : HookSat (Rust.withPanics ext) lsMemcpySym framelessMemcpySpec :=
    hookSat_withPanics_of_mem (by decide) hmc
  have hpan_alloc' : Rust.withPanics ext lsHandleAllocErrorSym = some Rust.panicked :=
    (withPanics_apply_lsExtern (by decide)).trans hpanic_alloc
  have hpan_raw' : Rust.withPanics ext lsHandleErrorSym = some Rust.panicked :=
    (withPanics_apply_lsExtern (by decide)).trans hpanic_raw
  refine ⟨?_, ?_, ?_⟩
  · exact ls_subroutine_ok_cl_of_block (callerProg := lsProg_516 (Rust.withPanics ext))
      (SpqrH.bm6_decodeVarint5_placed_of_hooks hshim' halloc' hpan_alloc')
  · exact SpqrH.bytes_merge_6_placed_ok_cro (callerProg := lsProg_516 (Rust.withPanics ext))
      hshim' halloc' hrealloc' hdealloc' hmc' hpan_alloc' hpan_raw'
  · exact growOneChain_placed_ok_cl_of_hooks (callerProg := lsProg_516 (Rust.withPanics ext))
      hshim' halloc' hrealloc' hpan_raw'

/-- Loop invariant of `message::merge<Chain> [local#4]` augmented with `LibsignalCodeRoLoaded`. -/
def Chain3LoopCroPlacedAtW [LibsignalPlacement] (ext : LibsignalHooks)
    (x : E2E.Record.DeserializeGeneral.ChainMergeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) : Prop :=
  StoreKit.LibsignalCodeRoLoaded lsmpl s.mem ∧
    VerNe.Chain3.Chain3LoopPlacedAtW ext x R s0 k s

def Chain3EntryCroStmt [LibsignalPlacement] (ext : LibsignalHooks) : Prop :=
  Chain3CalleesCroPlacedW ext →
  ∀ (x : E2E.Record.DeserializeGeneral.ChainMergeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = lsmpl.base 516 → s0.status = .Running →
    (s0.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl VerNe.Chain3.chainMerge3RawSpecW).pre x s0 ∗ R) →
    s0.spAligned = true →
    VerNe.Chain3.Chain3StepPlacedAtW ext x R s0 s0 (Chain3LoopCroPlacedAtW ext x R s0 0)

def Chain3SrkCroStmt [LibsignalPlacement] (ext : LibsignalHooks) : Prop :=
  Chain3CalleesCroPlacedW ext →
  ∀ (x : E2E.Record.DeserializeGeneral.ChainMergeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hk : k < x.c.fields.length),
    ((x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2) →
    Chain3LoopCroPlacedAtW ext x R s0 k s →
    VerNe.Chain3.Chain3StepPlacedAtW ext x R s0 s (Chain3LoopCroPlacedAtW ext x R s0 (k + 1))

def Chain3ChainKeyCroStmt [LibsignalPlacement] (ext : LibsignalHooks) : Prop :=
  Chain3CalleesCroPlacedW ext →
  ∀ (x : E2E.Record.DeserializeGeneral.ChainMergeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 3 →
    Chain3LoopCroPlacedAtW ext x R s0 k s →
    VerNe.Chain3.Chain3StepPlacedAtW ext x R s0 s (Chain3LoopCroPlacedAtW ext x R s0 (k + 1))

def Chain3MessageKeysCroStmt [LibsignalPlacement] (ext : LibsignalHooks) : Prop :=
  Chain3CalleesCroPlacedW ext →
  ∀ (x : E2E.Record.DeserializeGeneral.ChainMergeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 4 →
    Chain3LoopCroPlacedAtW ext x R s0 k s →
    VerNe.Chain3.Chain3StepPlacedAtW ext x R s0 s (Chain3LoopCroPlacedAtW ext x R s0 (k + 1))

theorem chain3Loop_cro_run [LibsignalPlacement] (ext : LibsignalHooks)
    (hC : Chain3CalleesCroPlacedW ext)
    (hSrk : Chain3SrkCroStmt ext) (hCk : Chain3ChainKeyCroStmt ext)
    (hMk : Chain3MessageKeysCroStmt ext)
    {x : E2E.Record.DeserializeGeneral.ChainMergeGenGhost} {R : SepProp} {s0 : State} :
    ∀ (m k : Nat) (s : State), k + m = x.c.fields.length →
      Chain3LoopCroPlacedAtW ext x R s0 k s →
      reaches_outcome (lsProg_516 (Rust.withPanics ext))
        (StoreKit.withLsCodeRoLoaded lsmpl VerNe.Chain3.chainMerge3RawSpecW) x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk ⟨_hcro, hs⟩
    simp only [Nat.add_zero] at hk
    subst hk
    intro hL
    obtain ⟨sf, hst, ⟨hret, hcc, hm⟩ | ⟨hpan, hmpan⟩⟩ :=
      VerNe.Chain3.chain3Exit_placed_ok ext x R s0 s hs hL
    · dsimp only [VerNe.Chain3.chainMerge3PlacedSpecW, withLsCl, withLsCodeLoaded] at hm
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm
      exact ⟨sf, hst, Or.inl ⟨hret, hcc, hm.2⟩⟩
    · exact ⟨sf, hst, Or.inr (Or.inl ⟨hpan, hmpan⟩)⟩
  | succ m ih =>
    intro k s hk hs
    have hlt : k < x.c.fields.length := by omega
    have next : ∀ s', Chain3LoopCroPlacedAtW ext x R s0 (k + 1) s' →
        reaches_outcome (lsProg_516 (Rust.withPanics ext))
          (StoreKit.withLsCodeRoLoaded lsmpl VerNe.Chain3.chainMerge3RawSpecW) x R s0 s' :=
      fun s' hs' => ih (k + 1) s' (by omega) hs'
    rcases chainField_tag_cases (x.c.fields[k]'hlt) with h12 | h3 | h4
    · exact segStepG_then (hSrk hC x R s0 k s hlt h12 hs) next
    · exact segStepG_then (hCk hC x R s0 k s hlt h3 hs) next
    · exact segStepG_then (hMk hC x R s0 k s hlt h4 hs) next

theorem chainMerge3W_cro_placed_ok [LibsignalPlacement] (ext : LibsignalHooks)
    (hC : Chain3CalleesCroPlacedW ext)
    (hEntry : Chain3EntryCroStmt ext) (hSrk : Chain3SrkCroStmt ext)
    (hCk : Chain3ChainKeyCroStmt ext) (hMk : Chain3MessageKeysCroStmt ext) :
    subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516)
      (StoreKit.withLsCodeRoLoaded lsmpl VerNe.Chain3.chainMerge3RawSpecW) := by
  intro x R s0 hpc hrun hpre hal
  exact segStepG_then (hEntry hC x R s0 hpc hrun hpre hal) fun s hs =>
    chain3Loop_cro_run ext hC hSrk hCk hMk x.c.fields.length 0 s (Nat.zero_add _) hs

/-- Lift `message::merge<Chain> [local#4]` (Block `516`) from `lsProg_516 (Rust.withPanics ext)` to any `callerProg` over `ext` under `StoreKit.withLsCodeRoLoaded`. -/
theorem chainMerge5_cro_of_block [LibsignalPlacement] {ext : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [hcaller : IsLsBlockProg callerProg callerBlk ext]
    (hC5 : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516)
      (StoreKit.withLsCodeRoLoaded lsmpl VerNe.Chain3.chainMerge3RawSpecW)) :
    subroutine_ok callerProg (lsmpl.base 516)
      (StoreKit.withLsCodeRoLoaded lsmpl VerNe.Chain3.chainMerge3RawSpecW) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcrl0, _⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  have hcallee : IsLsBlockProg (lsProg_516 (Rust.withPanics ext)) 516 (Rust.withPanics ext) :=
    inferInstance
  have hQL : (lsProg_516 (Rust.withPanics ext)).CodeLoaded s0.mem :=
    hcallee.eq_blockProgram ▸
      hcrl0.1 516 (by decide) (by decide) (Rust.withPanics ext) (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hC5.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, (lsProg_516 (Rust.withPanics ext)).externAt? pc =
      callerProg.externAt? pc :=
    ls_externAt?_withPanics_eq (prog1 := lsProg_516 (Rust.withPanics ext)) (prog2 := callerProg)
  have hsvc : (lsProg_516 (Rust.withPanics ext)).svc = callerProg.svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact Arm64.reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ)
    (reaches_outcome.of_outcome hout)

/-- Cut a `SepWPp` proof at `mid` while forwarding `LibsignalCodeRoLoaded` across `Steps.keepsFrozen`. -/
theorem SepWPp.bind_lscro [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q1 Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P Q1 Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q1 sm Pm →
      SepWPp prog ret sm Pm Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hst1, ⟨hpcm, hrunm, Pm, hmm, hq1⟩ | hpan | hoom⟩ := h1 R hm hL
  · obtain ⟨sf, hst2, hout⟩ :=
      h2 sm Pm hpcm hrunm (hcro.of_keepsFrozen hst1.keepsFrozen) hq1 R hmm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hst1, Or.inr (Or.inr hoom)⟩

/-- Lift a `Chain3StepPlacedAtW` step to preserve `StoreKit.LibsignalCodeRoLoaded`. -/
theorem segStepG_keep_cro [LibsignalPlacement] {ext : LibsignalHooks}
    {x : ChainMergeGenGhost} {R : SepProp}
    {s0 s : State} {Q : State → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : VerNe.Chain3.Chain3StepPlacedAtW ext x R s0 s Q) :
    VerNe.Chain3.Chain3StepPlacedAtW ext x R s0 s
      (fun s' => StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem ∧ Q s') := by
  intro hL
  obtain ⟨sf, hst, hq | hpan⟩ := hstep hL
  · exact ⟨sf, hst, Or.inl ⟨hcro.of_keepsFrozen hst.keepsFrozen, hq⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

theorem intro_withLsCodeRoLoaded_c3 [LibsignalPlacement] {α : Type} {S : Spec α} {x : α}
    {s0 : State} {R : SepProp}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem) (h : s0.mem ⊨ S.pre x s0 ∗ R) :
    s0.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl S).pre x s0 ∗ R := by
  have h' : s0.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ (S.pre x s0 ∗ R) := by
    rw [satisfies_pure_sepConj]; exact ⟨hcro, h⟩
  dsimp only [StoreKit.withLsCodeRoLoaded]
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h'

theorem sp_sub_240_aligned_c3_cro {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 240#64) &&& 15#64 = 0#64 := by
  have := sp_and_15_sub_aligned sp0 240#64 (by decide)
  simpa only [show (0b1111#64 : BitVec 64) = 15#64 from rfl, h] using this

private theorem allocFailedIn_of_trace_eq_c3_cro {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rwa [htr] at h

private theorem chainG_enc_eq_fields_c3_cro (c : ChainG) :
    c.enc = c.fields.flatMap ChainField.enc := by
  rcases c with ⟨srk, priv, ck, keys⟩
  unfold ChainG.enc ChainG.fields
  simp only [List.flatMap_append, List.flatMap_map]
  have h1 : bytesField 1 srk =
      List.flatMap ChainField.enc (if srk = [] then [] else [ChainField.srk srk]) := by
    unfold bytesField; split <;> simp [ChainField.enc]
  have h2 : bytesField 2 priv =
      List.flatMap ChainField.enc (if priv = [] then [] else [ChainField.priv priv]) := by
    unfold bytesField; split <;> simp [ChainField.enc]
  have h3 : msgField 3 (Option.map (fun ik => uint32Field 1 ik.1 ++ bytesField 2 ik.2) ck) =
      List.flatMap ChainField.enc
        (match ck with | some (i, k) => [ChainField.ck i k] | none => []) := by
    cases ck <;> simp [msgField, ChainField.enc]
  have h4 : (List.map (fun m => lenField 4 (encMessageKey m)) keys).flatten =
      List.flatMap (fun a => (ChainField.key a).enc) keys := by
    rw [← List.flatMap_def]; rfl
  rw [h1, h2, h3, h4]; rfl

section EntrySlice
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

set_option maxHeartbeats 400000 in
/-- Entry slice under `LibsignalCodeRoLoaded`: from the entry of `message::merge<Chain> [local#4]` to the loop head `+0x0a8` with 0 fields consumed. -/
theorem chain3Entry_cro_placed_ok [LibsignalPlacement] (ext : LibsignalHooks) :
    Chain3EntryCroStmt ext := by
  intro hC x R s0 hpc hrun hpre hal
  obtain ⟨hcro0, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  refine segStepG_keep_cro hcro0 ?_
  intro hL0
  rcases x with ⟨a, c, bufRef, slot, ptr, tail⟩
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hcro0.1
  dsimp only [chainMerge3RawSpecW] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hcOk, hlen_lt⟩, hmem⟩
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
  have hsp_sub_align : (s0.sp - 240#64) &&& 15#64 = 0#64 := sp_sub_240_aligned_c3_cro hsp_align
  have hmem1 : s0.mem ⊨ stackAt s0.sp chainMerge3StackX ∗
      (chain3GAt A0 a ChainG.empty ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (c.payload ++ tail) ∗ R) :=
    Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, hsp1, htr1, hvregs1, hlr1, hx0_1, hx19_1, hx20_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hent1⟩ | ⟨_, hoom1⟩⟩ :=
    (step_chain3Entry_pre_placed (ext := ext) a bufRef s0.sp
      (post := fun sm Pm =>
        sm.sp = s0.sp - 240#64 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .lr = lsmpl.base 516 + 56#64 ∧
        sm.readReg64 .x0 = bufRef ∧ sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧
        sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧ sm.readReg64 .x29 = s0.sp - 80#64 ∧
        (Pm ⊢ stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0))
      hpc hrun rfl hsp_align hx0 hx1 hx2
      (fun _ _ _ hsp' htr' hvregs' hlr' hx0' hx19' hx20' hx26' hx27' hx28' hx29' _ hent =>
        ⟨hsp', htr', hvregs', hlr', hx0', hx19', hx20', hx26', hx27', hx28', hx29',
          hent⟩)).elim hmem1 hL0
  rotate_left; · exact (not_satisfies_false_sepConj hoom1).elim
  have hm1' := Satisfies.mono (sepConj_mono_left hent1) hm1
  have hal1 : s1.spAligned = true := by simp only [State.spAligned, hsp1, beq_iff_eq]; exact hsp_sub_align
  let gvar : DecodeVarintSlowGhost := ⟨bufRef, slot, ptr, c.payload ++ tail⟩
  let F_call : SepProp :=
    memRegion (s0.sp - 240#64 - BitVec.ofNat 64 chainMerge3SubStackX)
        (chainMerge3SubStackX - SpqrH.decodeVarint2StackX) ∗
      chain3SavedRegs s0.sp s0 ∗ chain3GAt A0 a ChainG.empty
  have hlen63 : (c.payload ++ tail).length < 2 ^ 63 := Nat.lt_trans hlen_lt (by decide)
  have hm1_call : s1.mem ⊨ (withLsCl lsmpl (SpqrH.decodeVarint2SpecX A0)).pre gvar s1 ∗ (F_call ∗ R) := by
    refine intro_withLsCl_c3 (libsignalCodeLoaded_preserve_c3 hcl0 hst1) ?_
    unfold SpqrH.decodeVarint2SpecX; dsimp only [gvar]
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hx0_1, hlen63⟩, ?_⟩
    rw [stackAt_c3Sub_to_decodeVarint (s0.sp - 240#64)] at hm1'
    have hpool : A0.pool = emp := rfl
    rw [hsp1, hpool]; dsimp only [F_call]; convert hm1' using 1; simp only [emp_sepConj]; ac_rfl
  obtain ⟨s2, hst2, ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hm2⟩ | ⟨hpan2, hm2_pan⟩ | ⟨_, _, hm2_ex⟩ | ⟨_, hm2_oom⟩⟩ :=
    subroutine_ok_apply_outcome hC.dv gvar (F_call ∗ R) hpc1 hrun1 hm1_call hal1 (hst1.codeLoaded hL0)
  · have hpc2' : s2.pc = lsmpl.base 516 + 56#64 := by rw [hpc2, hlr1]
    have hsp2' : s2.sp = s0.sp - 240#64 := by rw [hsp2, hsp1]
    have hx19_2 : s2.readReg64 .x19 = bufRef := hcs2.1.trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = a := hcs2.2.1.trans hx20_1
    have hx26_2 : s2.readReg64 .x26 = s0.readReg64 .x26 := hcs2.2.2.2.2.2.2.2.1.trans hx26_1
    have hx27_2 : s2.readReg64 .x27 = s0.readReg64 .x27 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
    have hx28_2 : s2.readReg64 .x28 = s0.readReg64 .x28 := hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
    have hx29_2 : s2.readReg64 .x29 = s0.sp - 80#64 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    have hdec : decodeVarint (c.payload ++ tail) = some (BitVec.ofNat 64 c.enc.length, c.enc ++ tail) := by
      rw [show c.payload ++ tail = encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.enc ++ tail) by
        unfold ChainG.payload; rw [List.append_assoc]]
      exact decodeVarint_encodeVarint (BitVec.ofNat 64 c.enc.length) (c.enc ++ tail)
    obtain ⟨_, hm2⟩ := extract_withLsCl_post_c3 hm2
    unfold SpqrH.decodeVarint2SpecX at hm2; dsimp only [gvar] at hm2; rw [hdec] at hm2; dsimp only at hm2
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hm2
    rcases hm2 with ⟨⟨hx0_2, hx1_2⟩, htr2, hm2⟩
    rw [hsp1, show A0.pool = emp from rfl] at hm2
    have hlenA : (c.enc ++ tail).length = c.enc.length + tail.length := List.length_append
    have hlt2 : c.enc.length + tail.length < 2 ^ 62 := by
      unfold ChainG.payload at hlen_lt; simp only [List.length_append] at hlen_lt; omega
    let p1 := ptr + BitVec.ofNat 64 ((c.payload ++ tail).length - (c.enc ++ tail).length)
    unfold sliceCursorAfter at hm2
    have hm2_post : s2.mem ⊨
        ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ p1) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.enc.length + tail.length))) ∗
        ((ptr ↦ₛ (c.payload ++ tail)) ∗ stackAt (s0.sp - 240#64) SpqrH.decodeVarint2StackX ∗ F_call ∗ R) := by
      rw [← hlenA]; dsimp only [p1]; refine Satisfies.mono (sep_ac_seedChain ?_) hm2
      simp only [emp_sepConj]; ac_rfl
    obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, hsp3, htr3, hvregs3, hx19_3, hx20_3, hx21_3,
        hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx28_3, hx29_3, hent3⟩ | ⟨_, hoom3⟩⟩ :=
      (step_chain3Entry_post_placed (ext := ext) a bufRef slot p1 s0.sp
        (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28) c.enc.length tail.length hlt2
        (post := fun sm Pm =>
          sm.sp = s0.sp - 240#64 ∧ sm.trace = s2.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s2 ∧
          sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 tail.length ∧ sm.readReg64 .x22 = s0.sp - 232#64 ∧
          sm.readReg64 .x23 = 1#64 ∧ sm.readReg64 .x24 = 104#64 ∧
          sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧
          sm.readReg64 .x28 = s0.readReg64 .x28 ∧ sm.readReg64 .x29 = s0.sp - 80#64 ∧
          (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ p1) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.enc.length + tail.length))))
        hpc2' hrun2 hsp2' hsp_align hx0_2 hx1_2 hx19_2 hx20_2 hx26_2 hx27_2 hx28_2 hx29_2
        (fun _ _ _ hsp' htr' hvregs' hx19' hx20' hx21' hx22' hx23' hx24' hx26' hx27' hx28' hx29' _ hent =>
          ⟨hsp', htr', hvregs', hx19', hx20', hx21', hx22', hx23', hx24', hx26', hx27', hx28', hx29', hent⟩)).elim
        hm2_post ((hst1.trans hst2).codeLoaded hL0)
    rotate_left; · exact (not_satisfies_false_sepConj hoom3).elim
    have hm3' := Satisfies.mono (sepConj_mono_left hent3) hm3
    have hst_all := (hst1.trans hst2).trans hst3
    refine ⟨s3, hst_all, Or.inl ⟨hpc3, hrun3, (htr3.trans htr2).trans htr1,
      hvregs3.trans hvregs2, libsignalCodeLoaded_preserve_c3 hcl0 hst_all, hsp3,
      by simp only [State.spAligned, hsp3, beq_iff_eq]; exact hsp_sub_align,
      hx29_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx28_3, hcOk, hlen_lt, ?_⟩⟩
    dsimp only
    rw [show chainGAfter c 0 = ChainG.empty from rfl,
      show (c.fields.drop 0).flatMap ChainField.enc = c.enc by
        rw [List.drop_zero, ← chainG_enc_eq_fields_c3_cro c]]
    unfold sliceCursorAfter
    rw [hlenA, stackAt_c3Sub_to_decodeVarint (s0.sp - 240#64)]
    dsimp only [F_call, p1] at hm3'; rw [hlenA] at hm3'
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hm3'
  · refine ⟨s2, hst1.trans hst2, Or.inr ⟨hpan2, ?_⟩⟩
    unfold withLsCl SpqrH.decodeVarint2SpecX at hm2_pan; dsimp only at hm2_pan
    dsimp only [chainMerge3PlacedSpecW, withLsCl, chainMerge3RawSpecW, Serialization.allocPanic]
    refine allowPanic_frame (F := F_call) (allocFailedIn_of_trace_eq_c3_cro htr1) ?_
    rw [sepConj_assoc _ F_call R]; exact hm2_pan
  · exact False.elim (not_satisfies_false_sepConj hm2_ex)
  · exact False.elim (not_satisfies_false_sepConj hm2_oom)

set_option maxHeartbeats 400000 in
/-- Unified `bl decode_varint [local#4]` (Block `515`) call helper for `Chain3CalleesCroPlacedW`. -/
theorem c3_dv_call_cro [LibsignalPlacement] {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW ext)
    (bufRef slot curPtr sp0 ret_pc v : BitVec 64) (enc rest : List (BitVec 8))
    (hdv : decodeVarint (enc ++ rest) = some (v, rest))
    (hlen_lt : (enc ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 515)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 → sm.readReg64 .x1 = v →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ (curPtr ↦ₛ enc) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 enc.length) rest ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot curPtr (enc ++ rest) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  have hlen_lt63 : (enc ++ rest).length < 2 ^ 63 := by omega
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_240_aligned_c3_cro halign
  refine SepWPp.call_lscl_c3
    (x := DecodeVarintSlowGhost.mk bufRef slot curPtr (enc ++ rest))
    (F := memRegion (sp0 - 240#64 - BitVec.ofNat 64 chainMerge3SubStackX)
      (chainMerge3SubStackX - SpqrH.decodeVarint2StackX) ∗ F)
    hC.dv hpc hrun hsp_aligned hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    refine intro_withLsCl_c3 hcl ?_
    rw [stackAt_c3Sub_to_decodeVarint (sp0 - 240#64)] at hm
    dsimp only [SpqrH.decodeVarint2SpecX]
    rw [show A0.pool = emp from rfl, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen_lt63⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm; dsimp only [withLsCl, SpqrH.decodeVarint2SpecX] at hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withLsCl, SpqrH.decodeVarint2SpecX, chainMerge3PlacedSpecW, chainMerge3RawSpecW,
      Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn] at hm ⊢; rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    dsimp only [withLsCl, SpqrH.decodeVarint2SpecX]; rw [hdv, hsp]; dsimp only
    rw [show A0.pool = emp from rfl]; simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun _ => SepWPp.pure_elim fun ⟨hx0m, hx1m⟩ =>
      SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.mono_pre_seedChain ?_
      (hnext sm hpcm hrunm hspm hclm (htrm.trans htr) hcsm hx0m hx1m)
    rw [sliceCursorAfter_append_eq_seedChain slot curPtr enc rest,
      stackAt_c3Sub_to_decodeVarint (sp0 - 240#64)]
    exact sep_ac_seedChain (by ac_rfl)

end EntrySlice
end Chain3Cro

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
