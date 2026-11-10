/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExt
public import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.Common.CallInv

@[expose] public section

set_option autoImplicit false

/-!
# `SessionRecord::serialize` Stack Budgets, Specifications, and Stub Contracts

Defines the `extHookStack`-sized (`16384`-byte) stack budgets, subroutine specifications
(`encodeChainSpecX`, `encodeRawSpecX`, `sessionCloneSpecX`, `dropSessionStructureLocal1SpecX`,
`serializeSpecX`, `serializeCanonSpecX`), and external stub contract bundles (`SerContractsX` and
`SerContractsXPlaced`) for `SessionRecord::serialize` and its callees.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal.Stage1X

theorem L1_SerDefsX : True := trivial

/-! ## Stack budgets at `extHookStack` -/

/-- `encode::<Chain>` (`0x44b0`): frame `0x60` + `encode_varint` + `do_reserve` + `Chain::encoded_len`. -/
abbrev encodeChainStackX : Nat :=
  0x60 + Prost.encodeVarintStackX + Proofs.libsignal.Hooks2.doReserveStackX + chainLenStack

/-- `SessionStructure::encode_raw` (`0x4d38`): frame `0x50` + `encode_varint` + `do_reserve` + `encode::<Chain>`. -/
abbrev encodeRawStackX : Nat :=
  0x50 + Prost.encodeVarintStackX + Proofs.libsignal.Hooks2.doReserveStackX + encodeChainStackX

/-- `SessionStructure::clone` (`0x240f0`) + `Chain::clone` (`0x24848`) + `0x400` margin + one stub call. -/
abbrev sessionCloneStackX : Nat := 0x1d0 + 0xd0 + 0x400 + Stage1X.extHookStack

/-- `drop_glue<SessionStructure> [local#1]` (`0x25b4`): frame `32` + `drop_glue<Vec<Chain>>`
(`48` + `drop_glue<Vec<MessageKey>>` (`48` + one `__rust_dealloc` at `extHookStack`)). -/
abbrev dropSessionStructureLocal1StackX : Nat := 32 + (48 + (48 + Stage1X.extHookStack))

/-- `SessionRecord::serialize` (`0x1857c`): frame `0x360` + every callee. -/
abbrev serializeStackX : Nat :=
  0x360 + sessionCloneStackX + vecVecCloneStack + sessionLenStack + Stage1X.extHookStack +
    Prost.encodeVarintStackX + encodeRawStackX + Proofs.libsignal.Hooks2.doReserveStackX + dropSessionStructureLocal1StackX

set_option maxRecDepth 2000000 in
/-- The X budget fits in the frozen `recordSerializeStack = 0x30000`. -/
theorem serializeStackX_le_recordSerializeStack :
    serializeStackX ≤ CryptoVerification.E2E.Bin.recordSerializeStack := by decide

/-! ## Subroutine specifications at `extHookStack` -/

/-- `encodeChainSpec A` at `encodeChainStackX`. -/
def encodeChainSpecX (A : RustAlloc) : Spec EncodeChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = BitVec.ofNat 64 x.tag ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.v ∧
      (x.tag = 6 ∨ x.tag = 7) ∧ x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32⌝ ∗
      protoChainAt A x.gc x.a ∗ vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp encodeChainStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ protoChainAt A x.gc x.a ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A x.v cap' ptr' (x.bs ++ lenField x.tag (encChainMem x.gc))) ∗
      A.pool ∗ stackAt s0.sp encodeChainStackX
  onPanic := allocPanic

/-- `encodeRawSpec A` at `encodeRawStackX`. -/
def encodeRawSpecX (A : RustAlloc) : Spec EncodeRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp encodeRawStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionStateReprAt A x.ss x.G x.s ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A x.v cap' ptr' (x.bs ++ encSessionMem x.G x.s)) ∗
      A.pool ∗ stackAt s0.sp encodeRawStackX
  onPanic := allocPanic

/-- `sessionCloneSpec A` at `sessionCloneStackX`. -/
def sessionCloneSpecX (A : RustAlloc) : Spec SessionCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
      sessionStateReprAt A x.src x.G x.s ∗ memRegion x.dst 344 ∗ A.pool ∗ stackAt s.sp sessionCloneStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionStateReprAt A x.src x.G x.s ∗
      (∃∗ G' : SessionGhost, ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A x.dst G' x.s) ∗
      A.pool ∗ stackAt s0.sp sessionCloneStackX
  onPanic := allocPanic

/-- `FromRecordCallees.dropSessionStructureLocal1Spec A` at `dropSessionStructureLocal1StackX`. -/
def dropSessionStructureLocal1SpecX (A : RustAlloc) :
    Spec FromRecordCallees.DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp dropSessionStructureLocal1StackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp dropSessionStructureLocal1StackX

/-- `serializeSpec A` at `serializeStackX`. -/
def serializeSpecX (A : RustAlloc) : Spec SerializeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧ (encRecordMem x.g x.r).length < 2 ^ 32⌝ ∗
      sessionRecordAt A x.self x.g x.r ∗ memRegion x.out 32 ∗ A.pool ∗
      stackAt s.sp serializeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionRecordAt A x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (encRecordMem x.g x.r) ∗
      A.pool ∗ stackAt s0.sp serializeStackX
  onPanic := allocPanic

/-- `serializeCanonSpec A` at `serializeStackX`. -/
def serializeCanonSpecX (A : RustAlloc) : Spec SerializeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧ CanonRecord x.g x.r ∧
      (encodeRecord x.r).length < 2 ^ 32⌝ ∗
      sessionRecordAt A x.self x.g x.r ∗ memRegion x.out 32 ∗ A.pool ∗
      stackAt s.sp serializeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionRecordAt A x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (encodeRecord x.r) ∗
      A.pool ∗ stackAt s0.sp serializeStackX
  onPanic := allocPanic

/-! ## Stub contract bundle (`SerContractsX`) -/

/-- Stub contracts used by `serialize` and its callees on `SP2Ext img.base ext`:
alloc / dealloc / realloc / shim / memmove (`Stage1X.AllocContractsX`, `extHookStack`) and the
owned-source `memcpy` (`sessionMemcpySpec externStack`). -/
structure SerContractsX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : Stage1X.AllocContractsX img A ext
  memcpy : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memcpyName)
    ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img)

/-- Call `memcpy` (`sessionMemcpySpec externStack`) at caller-relative offset `k`. -/
theorem SerContractsX.memcpy_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : SerContractsX img A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) :=
  sub_ok_at_caller hk hC.memcpy

theorem serContractsX_of_stage2ContractsA0 {img : Obj.Image}
    {ext : String → Option (State → State)} (hC : Stage2ContractsA0 img ext) :
    SerContractsX img CryptoVerification.E2E.HooksE.A0 ext where
  alloc := allocContractsX_of_stage2ContractsA0 hC
  memcpy := hC.memcpy

/-- Frame `sessionMemcpySpec stk` (e.g. `memHookStack = 4096`) up to `extHookStack = 16384`
on `SP2Ext`. -/
theorem sessionMemcpy_extHookStack_of_le {img : Obj.Image}
    {ext : String → Option (State → State)} {entry : BitVec 64} {stk : Nat}
    (hle : stk ≤ CryptoVerification.LibsignalTripleRatchet.extHookStack)
    (h : subroutine_ok (SP2Ext img.base ext) entry ((sessionMemcpySpec stk).inImage img)) :
    subroutine_ok (SP2Ext img.base ext) entry
      ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) := by
  have hmax : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ 2 ^ 64 := by decide
  have hsplit : ∀ sp : BitVec 64,
      stackAt sp CryptoVerification.LibsignalTripleRatchet.extHookStack =
        stackAt sp stk ∗
          memRegion (sp - BitVec.ofNat 64 CryptoVerification.LibsignalTripleRatchet.extHookStack)
            (CryptoVerification.LibsignalTripleRatchet.extHookStack - stk) := by
    intro sp
    have hs := ProofLib.stackAt_split_bottom sp stk
      (CryptoVerification.LibsignalTripleRatchet.extHookStack - stk)
      (by omega)
    rw [Nat.add_sub_of_le hle, sepConj_comm] at hs
    exact hs
  refine subroutine_ok_inImage_map' h fun x R s0 hpre => ?_
  refine ⟨x,
    memRegion (s0.sp - BitVec.ofNat 64 CryptoVerification.LibsignalTripleRatchet.extHookStack)
      (CryptoVerification.LibsignalTripleRatchet.extHookStack - stk) ∗ R,
    ?_, fun sf hpost => ?_⟩
  · simp only [sessionMemcpySpec, libcMemcpySpec, hsplit s0.sp] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · simp only [sessionMemcpySpec, libcMemcpySpec, hsplit s0.sp] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

/-- Builds `SerContractsX img A ext` from `LibsignalTripleRatchet.AllocContractsX img A ext` for
arbitrary `A : RustAlloc`. -/
theorem SerContractsX.of_trAllocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    SerContractsX img A ext where
  alloc := {
    alloc := by
      refine subroutine_ok_inImage_map' hA.alloc fun ⟨size, align⟩ R s0 hpre => ?_
      refine ⟨(size, align), R, ?_, fun sf hpost => ?_⟩
      · simp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
          Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hpre ⊢
        exact hpre
      · simp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
          Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hpost ⊢
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    dealloc := by
      refine subroutine_ok_inImage_map' hA.dealloc fun ⟨p, size, align⟩ R s0 hpre => ?_
      refine ⟨(p, size, align), R, ?_, fun sf hpost => ?_⟩
      · simp only [CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack,
          Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at hpre ⊢
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
      · simp only [CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack,
          Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at hpost ⊢
        exact hpost
    realloc := by
      refine subroutine_ok_inImage_map' hA.realloc
        fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre => ?_
      refine ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩
      · simp only [CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
          Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
          sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
        obtain ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, hlay_old, hlay_new⟩, hmem⟩ := hpre
        exact ⟨⟨hx0, hx1, hx2, hx3, hlay_old, hlay_new, hbs1, hbs2⟩,
          Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem⟩
      · simp only [CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
          CryptoVerification.LibsignalTripleRatchet.rustReallocSpecWithStack,
          Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
          Proofs.libsignal.Stage1X.rustReallocSpecWithStack] at hpost ⊢
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    shim := hA.shim CryptoVerification.LibsignalTripleRatchet.extHookStack (Nat.le_refl _) (by decide)
    session_memmove :=
      hA.session_memmove CryptoVerification.LibsignalTripleRatchet.extHookStack (Nat.le_refl _) (by decide)
  }
  memcpy := sub_ok_at_of_fnAddr (SP2Ext_fnAddr img.base ext memcpyName)
    (hA.session_memcpy CryptoVerification.LibsignalTripleRatchet.extHookStack (Nat.le_refl _) (by decide))

/-- Builds `SerContractsX img A ext` from 4 KiB-framed allocator contracts together with `shim`,
`memcpy`, and `memmove` at `extHookStack = 16384`. -/
theorem SerContractsX.of_stage2Stubs {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff allocName)
      (((rustAllocSpec A).withExternStackFromAlloc').inImage img))
    (hdealloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff deallocName)
      (((rustDeallocLayoutSpec' A).withExternStackFromAlloc').inImage img))
    (hrealloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff reallocName)
      (((rustReallocSpec A).withExternStackFromAlloc').inImage img))
    (hshim : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff shimName)
      ((sessionShimSpec.withHookStack CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img))
    (hmemcpy : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memcpyName)
      ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img))
    (hmemmove : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memmoveName)
      ((sessionMemmoveSpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img)) :
    SerContractsX img A ext where
  alloc := {
    alloc := by
      rw [SP2Ext_fnAddr]
      refine subroutine_ok_inImage_map' halloc fun ⟨size, align⟩ R s0 hpre => ?_
      refine ⟨(size, align), R, ?_, fun sf hpost => ?_⟩
      · simp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, Spec.withExternStackFromAlloc',
          rustAllocSpec, Stage1X.extHookStack, stackAt_externStack_split_allocHookStack'] at hpre ⊢
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
      · simp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, Spec.withExternStackFromAlloc',
          rustAllocSpec, Stage1X.extHookStack, stackAt_externStack_split_allocHookStack'] at hpost ⊢
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    dealloc := by
      rw [SP2Ext_fnAddr]
      refine subroutine_ok_inImage_map' hdealloc fun ⟨p, size, align⟩ R s0 hpre => ?_
      refine ⟨(p, size, align), R, ?_, fun sf hpost => ?_⟩
      · simp only [Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack, Spec.withExternStackFromAlloc',
          rustDeallocLayoutSpec', rustDeallocSpec, Stage1X.extHookStack,
          stackAt_externStack_split_allocHookStack', sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
        obtain ⟨⟨hx0, hx1, hx2, hlay⟩, hmem⟩ := hpre
        refine ⟨hlay, ⟨hx0, hx1, hx2⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
      · simp only [Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack, Spec.withExternStackFromAlloc',
          rustDeallocLayoutSpec', rustDeallocSpec, Stage1X.extHookStack,
          stackAt_externStack_split_allocHookStack'] at hpost ⊢
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    realloc := by
      rw [SP2Ext_fnAddr]
      refine subroutine_ok_inImage_map' hrealloc fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre => ?_
      refine ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩
      · simp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack, Spec.withExternStackFromAlloc',
          rustReallocSpec, Stage1X.extHookStack,
          stackAt_externStack_split_allocHookStack', sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
        obtain ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, _hlay_old, hlay_new⟩, hmem⟩ := hpre
        refine ⟨⟨hx0, hx1, hx2, hx3, hlay_new, hbs1, hbs2⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
      · simp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
          Proofs.libsignal.Stage1X.rustReallocSpecWithStack,
          Spec.withExternStackFromAlloc', rustReallocSpec, Stage1X.extHookStack,
          stackAt_externStack_split_allocHookStack'] at hpost ⊢
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    shim := by rw [SP2Ext_fnAddr]; exact hshim
    session_memmove := by rw [SP2Ext_fnAddr]; exact hmemmove
  }
  memcpy := hmemcpy

/-- Builds `SerContractsX img A ext` from 4 KiB-framed allocator contracts, `shim` at
`extHookStack`, and `memcpy`/`memmove` at any stack budgets `stk_cpy, stk_mv ≤ extHookStack`. -/
theorem SerContractsX.of_memHookStubs {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk_cpy stk_mv : Nat}
    (hle_cpy : stk_cpy ≤ CryptoVerification.LibsignalTripleRatchet.extHookStack)
    (hle_mv : stk_mv ≤ CryptoVerification.LibsignalTripleRatchet.extHookStack)
    (halloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff allocName)
      (((rustAllocSpec A).withExternStackFromAlloc').inImage img))
    (hdealloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff deallocName)
      (((rustDeallocLayoutSpec' A).withExternStackFromAlloc').inImage img))
    (hrealloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff reallocName)
      (((rustReallocSpec A).withExternStackFromAlloc').inImage img))
    (hshim : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff shimName)
      ((sessionShimSpec.withHookStack CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img))
    (hmemcpy : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memcpyName)
      ((sessionMemcpySpec stk_cpy).inImage img))
    (hmemmove : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memmoveName)
      ((sessionMemmoveSpec stk_mv).inImage img)) :
    SerContractsX img A ext := by
  have hmax : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ 2 ^ 64 := by decide
  have hmv : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memmoveName)
      ((sessionMemmoveSpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) := by
    have hsplit : ∀ sp : BitVec 64,
        stackAt sp CryptoVerification.LibsignalTripleRatchet.extHookStack =
          stackAt sp stk_mv ∗
            memRegion (sp - BitVec.ofNat 64 CryptoVerification.LibsignalTripleRatchet.extHookStack)
              (CryptoVerification.LibsignalTripleRatchet.extHookStack - stk_mv) := by
      intro sp
      have hs := ProofLib.stackAt_split_bottom sp stk_mv
        (CryptoVerification.LibsignalTripleRatchet.extHookStack - stk_mv) (by omega)
      rw [Nat.add_sub_of_le hle_mv, sepConj_comm] at hs
      exact hs
    refine subroutine_ok_inImage_map' hmemmove fun x R s0 hpre => ?_
    refine ⟨x,
      memRegion (s0.sp - BitVec.ofNat 64 CryptoVerification.LibsignalTripleRatchet.extHookStack)
        (CryptoVerification.LibsignalTripleRatchet.extHookStack - stk_mv) ∗ R,
      ?_, fun sf hpost => ?_⟩
    · simp only [sessionMemmoveSpec, libcMemmoveSpec, hsplit s0.sp] at hpre ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · simp only [sessionMemmoveSpec, libcMemmoveSpec, hsplit s0.sp] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  exact SerContractsX.of_stage2Stubs halloc hdealloc hrealloc hshim
    (sessionMemcpy_extHookStack_of_le hle_cpy hmemcpy) hmv

/-! ## State-specialized stub contracts for `wp_call`

Specializes `.inImage img` contracts at a state `s` satisfying `img.FrozenLoaded s ∧ s.symtab = img.symtab`
into plain-precondition contracts guarded by `s'.mem = s.mem ∧ s'.symtab = s.symtab`. -/

theorem shim_ok_at_stateX {b : BitVec 64} {ext : String → Option (State → State)}
    {img : Obj.Image} {entry : BitVec 64} {s : State}
    (hshim : subroutine_ok (SP2Ext b ext) entry (Proofs.libsignal.Stage1X.session2ShimSpecX.inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP2Ext b ext) entry
      { pre := fun (_ : Unit) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab⌝ ∗ stackAt s'.sp Stage1X.extHookStack
        post := fun (_ : Unit) s0 sf =>
          ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp Stage1X.extHookStack } := by
  refine subroutine_ok_mono hshim (fun _ _ s0 hm => ?_) (fun _ _ _ _ hpost => ?_)
  · refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.session2ShimSpecX,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, Spec.withHookStack,
      emp_sepConj]
    apply Entails.pure_left
    rintro ⟨hmem, hsym'⟩
    exact Entails.pure_right ⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩ (Entails.refl _)
  · simpa only [Spec.inImage, Proofs.libsignal.Stage1X.session2ShimSpecX,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, Spec.withHookStack] using hpost

private theorem pure_and_entails_pure_sep_of' {P P' Q : Prop} {R : SepProp}
    (h : P → P' ∧ Q) :
    ⌜P⌝ ∗ R ⊢ ⌜P'⌝ ∗ (⌜Q⌝ ∗ R) := by
  apply Entails.pure_left
  intro hp
  rcases h hp with ⟨hp', hq⟩
  exact Entails.pure_right hp' (Entails.pure_right hq (Entails.refl R))

theorem alloc_ok_at_stateX {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64} {s : State}
    (halloc : subroutine_ok (SP2Ext b ext) entry
      ((Proofs.libsignal.Stage1X.rustAllocSpecWithStack A Stage1X.extHookStack).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP2Ext b ext) entry
      { pre := fun (size, align) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            (s'.readReg64 .x0).toNat = size ∧ (s'.readReg64 .x1).toNat = align ∧
            LayoutOk size align⌝ ∗
          A.pool ∗ stackAt s'.sp Stage1X.extHookStack
        post := (Proofs.libsignal.Stage1X.rustAllocSpecWithStack A Stage1X.extHookStack).post } := by
  refine subroutine_ok_mono halloc (fun ⟨size, align⟩ _ s0 hm => ?_) (fun _ _ _ _ hq => hq)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, Proofs.libsignal.Stage1X.rustAllocSpecWithStack]
  exact pure_and_entails_pure_sep_of' fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

theorem dealloc_ok_at_stateX {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64} {s : State}
    (hdealloc : subroutine_ok (SP2Ext b ext) entry
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP2Ext b ext) entry
      { pre := fun (p, size, align) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = size ∧
            (s'.readReg64 .x2).toNat = align ∧ LayoutOk size align⌝ ∗
          A.live p size align ∗ memRegion p size ∗
          A.pool ∗ stackAt s'.sp Stage1X.extHookStack
        post := (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).post } := by
  refine subroutine_ok_mono hdealloc (fun ⟨p, size, align⟩ _ s0 hm => ?_) (fun _ _ _ _ hq => hq)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack]
  exact pure_and_entails_pure_sep_of' fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

theorem realloc_ok_at_stateX {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64} {s : State}
    (hrealloc : subroutine_ok (SP2Ext b ext) entry
      ((Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack A Stage1X.extHookStack).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP2Ext b ext) entry
      { pre := fun (p, old_size, align, new_size, bs) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = old_size ∧
            (s'.readReg64 .x2).toNat = align ∧ (s'.readReg64 .x3).toNat = new_size ∧
            bs.length ≤ old_size ∧ bs.length ≤ new_size ∧
            LayoutOk old_size align ∧ LayoutOk new_size align⌝ ∗
          A.live p old_size align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old_size - bs.length) ∗
          A.pool ∗ stackAt s'.sp Stage1X.extHookStack
        post := (Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack A Stage1X.extHookStack).post } := by
  refine subroutine_ok_mono hrealloc (fun ⟨p, old_size, align, new_size, bs⟩ _ s0 hm => ?_) (fun _ _ _ _ hq => hq)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack]
  exact pure_and_entails_pure_sep_of' fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

theorem memcpy_ok_at_stateX {b : BitVec 64}
    {ext : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64} {s : State}
    (hmemcpy : subroutine_ok (SP2Ext b ext) entry ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP2Ext b ext) entry
      { pre := fun (dst, src, bs) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = dst ∧ s'.readReg64 .x1 = src ∧
            (s'.readReg64 .x2).toNat = bs.length⌝ ∗
          memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s'.sp CryptoVerification.LibsignalTripleRatchet.extHookStack
        post := (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).post } := by
  refine subroutine_ok_mono hmemcpy (fun ⟨dst, src, bs⟩ _ s0 hm => ?_) (fun _ _ _ _ hq => hq)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, sessionMemcpySpec, libcMemcpySpec]
  exact pure_and_entails_pure_sep_of' fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

/-! ## Relocatable `[LibsignalPlacement]` stub contracts (`SerContractsXPlaced`) -/

section Placed

set_option maxRecDepth 2000000

/-- Relocatable `[LibsignalPlacement]` counterpart of `SerContractsX`:
allocator / shim / memmove / panic contracts (`Stage1X.AllocContractsPlaced`, at `extHookStack`)
plus owned-source `memcpy` (`sessionMemcpySpec extHookStack`). -/
structure SerContractsXPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  alloc : Stage1X.AllocContractsPlaced A H
  memcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))

/-- Construct `SerContractsXPlaced A H` from block-0 `withLsCodeLoaded` contracts. -/
theorem SerContractsXPlaced.of_block0 [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (halloc : subroutine_ok blk0Prog (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.rustAllocSpecWithStack A Stage1X.extHookStack)))
    (hdealloc : subroutine_ok blk0Prog (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack)))
    (hrealloc : subroutine_ok blk0Prog (lsρ lsRustReallocSym)
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack A Stage1X.extHookStack)))
    (hshim : subroutine_ok blk0Prog (lsρ lsRustNoAllocShimSym)
      (withLsCodeLoaded lsmpl Proofs.libsignal.Stage1X.session2ShimSpecX))
    (hmemmove : subroutine_ok blk0Prog (lsρ "memmove")
      (withLsCodeLoaded lsmpl (sessionMemmoveSpec Stage1X.extHookStack)))
    (hmemcpy : subroutine_ok blk0Prog (lsρ lsMemcpySym)
      (withLsCodeLoaded lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack)))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    SerContractsXPlaced A H where
  alloc := Stage1X.AllocContractsPlaced.of_block0 halloc hdealloc hrealloc hshim hmemmove hpan_err hpan_alloc
  memcpy := ls_subroutine_ok_cl_of_callee (j := 0) hmemcpy

/-- Construct `SerContractsXPlaced A H` from `HookSat H` single-step hooks. -/
theorem SerContractsXPlaced.of_hooks [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (hmemmove : HookSat H "memmove" (sessionMemmoveSpec Stage1X.extHookStack))
    (hmemcpy : HookSat H lsMemcpySym (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    SerContractsXPlaced A H where
  alloc := Stage1X.AllocContractsPlaced.of_hooks halloc hdealloc hrealloc hshim hmemmove hpan_err hpan_alloc
  memcpy := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy)

theorem serContractsXPlaced_of_stage2ContractsA0Placed [LibsignalPlacement] {H : LibsignalHooks}
    (hC : Stage2ContractsA0Placed H) :
    SerContractsXPlaced CryptoVerification.E2E.HooksE.A0 H where
  alloc := allocContractsPlaced_of_stage2ContractsA0Placed hC
  memcpy := hC.memcpy

theorem shim_placed_ok_at_stateX {pl : Obj.MultiPlacement} {prog : Program}
    {entry : BitVec 64} {s : State}
    (hshim : subroutine_ok prog entry (withLsCl pl Proofs.libsignal.Stage1X.session2ShimSpecX))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (_ : Unit) s' =>
          ⌜s'.mem = s.mem⌝ ∗ stackAt s'.sp Stage1X.extHookStack
        post := fun (_ : Unit) s0 sf =>
          ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp Stage1X.extHookStack } := by
  have h0 := Stage1X.lscall_of_withLsCl hshim hcl
  refine subroutine_ok_mono h0 (fun _ _ s0 hp => ?_) (fun _ _ _ _ hq => ?_)
  · dsimp only [withMemEq, Proofs.libsignal.Stage1X.session2ShimSpecX,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, Spec.withHookStack] at hp ⊢
    exact Satisfies.mono (Entails.of_eq (by simp only [emp_sepConj]; ac_rfl)) hp
  · dsimp only [withMemEq, Proofs.libsignal.Stage1X.session2ShimSpecX,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, Spec.withHookStack] at hq ⊢
    exact hq

theorem alloc_placed_ok_at_stateX {pl : Obj.MultiPlacement} {A : RustAlloc} {prog : Program}
    {entry : BitVec 64} {s : State}
    (halloc : subroutine_ok prog entry
      (withLsCl pl (Proofs.libsignal.Stage1X.rustAllocSpecWithStack A Stage1X.extHookStack)))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (size, align) s' =>
          ⌜s'.mem = s.mem ∧
            (s'.readReg64 .x0).toNat = size ∧ (s'.readReg64 .x1).toNat = align ∧
            LayoutOk size align⌝ ∗
          A.pool ∗ stackAt s'.sp Stage1X.extHookStack
        post := (Proofs.libsignal.Stage1X.rustAllocSpecWithStack A Stage1X.extHookStack).post } := by
  have h0 := Stage1X.lscall_of_withLsCl halloc hcl
  refine subroutine_ok_mono h0 (fun _ _ s0 hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withMemEq, Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hrest⟩, hsp⟩
  rw [sepConj_assoc, sepConj_left_comm _ ⌜s0.mem = s.mem⌝, satisfies_pure_sepConj]
  refine ⟨hm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hsp⟩

theorem dealloc_placed_ok_at_stateX {pl : Obj.MultiPlacement} {A : RustAlloc} {prog : Program}
    {entry : BitVec 64} {s : State}
    (hdealloc : subroutine_ok prog entry
      (withLsCl pl (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack)))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (p, size, align) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = size ∧
            (s'.readReg64 .x2).toNat = align ∧ LayoutOk size align⌝ ∗
          A.live p size align ∗ memRegion p size ∗
          A.pool ∗ stackAt s'.sp Stage1X.extHookStack
        post := (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).post } := by
  have h0 := Stage1X.lscall_of_withLsCl hdealloc hcl
  refine subroutine_ok_mono h0 (fun _ _ s0 hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withMemEq, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hrest⟩, hsp⟩
  rw [sepConj_assoc, sepConj_left_comm _ ⌜s0.mem = s.mem⌝, satisfies_pure_sepConj]
  refine ⟨hm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hsp⟩

theorem realloc_placed_ok_at_stateX {pl : Obj.MultiPlacement} {A : RustAlloc} {prog : Program}
    {entry : BitVec 64} {s : State}
    (hrealloc : subroutine_ok prog entry
      (withLsCl pl (Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack A Stage1X.extHookStack)))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (p, old_size, align, new_size, bs) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = old_size ∧
            (s'.readReg64 .x2).toNat = align ∧ (s'.readReg64 .x3).toNat = new_size ∧
            bs.length ≤ old_size ∧ bs.length ≤ new_size ∧
            LayoutOk old_size align ∧ LayoutOk new_size align⌝ ∗
          A.live p old_size align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old_size - bs.length) ∗
          A.pool ∗ stackAt s'.sp Stage1X.extHookStack
        post := (Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack A Stage1X.extHookStack).post } := by
  have h0 := Stage1X.lscall_of_withLsCl hrealloc hcl
  refine subroutine_ok_mono h0 (fun _ _ s0 hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withMemEq, Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hrest⟩, hsp⟩
  rw [sepConj_assoc, sepConj_left_comm _ ⌜s0.mem = s.mem⌝, satisfies_pure_sepConj]
  refine ⟨hm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hsp⟩

theorem memcpy_placed_ok_at_stateX {pl : Obj.MultiPlacement} {prog : Program}
    {entry : BitVec 64} {s : State}
    (hmemcpy : subroutine_ok prog entry
      (withLsCl pl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack)))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (dst, src, bs) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = dst ∧ s'.readReg64 .x1 = src ∧
            (s'.readReg64 .x2).toNat = bs.length⌝ ∗
          memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s'.sp CryptoVerification.LibsignalTripleRatchet.extHookStack
        post := (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).post } := by
  have h0 := Stage1X.lscall_of_withLsCl hmemcpy hcl
  refine subroutine_ok_mono h0 (fun _ _ s0 hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withMemEq, sessionMemcpySpec, libcMemcpySpec] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hrest⟩, hsp⟩
  rw [sepConj_assoc, sepConj_left_comm _ ⌜s0.mem = s.mem⌝, satisfies_pure_sepConj]
  refine ⟨hm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hsp⟩

end Placed

end Proofs.libsignal.Hooks2
