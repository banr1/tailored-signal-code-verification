/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVec
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptDecode
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecDecode
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WPp

/-!
# Verification of `<Pqxdh as Handshake>::accept` (`0x23920`)

Defines the `Pqxdh::accept` memory layouts and proves `subroutine_ok` for `pqxdhAcceptSpec` and
`pqxdhAcceptOptFieldsSpec` (`0x23920`) across both `opk = none` and `opk = some` branches on
`trTrapProgAt`, `tripleRatchetProgAt`, and `tripleRatchetProgAtExt`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace CryptoVerification.E2E.Pqxdh.ResponderCore
open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.Shared (pqxdhVecAppendElementsFastSpec vecAppendElements_fast_ok vecAppendElements_fast_ok_trap)
abbrev Bytes := CryptoVerification.E2E.Pqxdh.Initiator.Bytes
abbrev memRegion_cells := @CryptoVerification.E2E.Pqxdh.Initiator.memRegion_cells
abbrev stackAt_split_cells := @CryptoVerification.E2E.Pqxdh.Initiator.stackAt_split_cells
abbrev memRegion_eight := @ProofLib.memRegion_eight
abbrev kyberDecapsStub : String := "libcrux_ml_kem::mlkem1024::kyber::decapsulate"
def dalekMontToEdOutAt (P : Primitives) (outPtr : BitVec 64) (inBytes : Bytes) (signBit : UInt8) :
    SepProp :=
  match P.montToEd inBytes signBit with
  | some edPt => outPtr ↦ₛ (u64le 1#64 ++ fitBv8 160 edPt)
  | none      => (outPtr ↦₆₄ 0#64) ∗ memRegion (outPtr + 8#64) 160
def dalekMontToEdStubSpec (P : Primitives) (_img : Obj.Image :=
    default) : Spec DalekMontToEdGhost where
  pre := fun g s => ⌜s.readReg64 .x0 = g.inPtr ∧ (s.readReg64 .x1).setWidth 8 =
    BitVec.ofNat 8 g.signBit.toNat ∧ s.readReg64 .x8 = g.outPtr ∧ g.inBytes.length = 32⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ memRegion g.outPtr 168 ∗ stackAt s.sp pqxdhHookStack
  post := fun g s0 sf => ⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      dalekMontToEdOutAt P g.outPtr g.inBytes (g.signBit &&& 1) ∗ stackAt s0.sp pqxdhHookStack
structure PqxdhHookContracts (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) : Prop where
  alloc            : AllocHooks A absHooks
  kyberDecaps      : HookSat absHooks kyberDecapsStub (kyberDecapsStubSpec P)
  dalekMontToEd    : HookSat absHooks dalekMontToEdStub (dalekMontToEdStubSpec P img)
  dalekTorsionFree : HookSat absHooks dalekTorsionFreeStub (cryptoBoolRegStubSpec P.isTorsionFree
                       160 img)
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
macro "cells_pre_unfold_fast" : tactic =>
  `(tactic| (
    conv => arg 4; simp (config := { maxSteps := 1000000 }) only [
      cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.reduceSub]))
macro "wp_simp_pre_fast " "[" rules:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (conv => arg 4; simp only [$rules,*]))
macro "wp_extract_exists" : tactic =>
  `(tactic| (
    (conv =>
      arg 4
      simp (config := { maxSteps := 1000000 }) only [
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    repeat' (apply SepWP.exists_elim; intro _)
    try (apply SepWP.pure_elim; intro _)))
abbrev Model.DRKey := CryptoVerification.E2E.Pqxdh.Initiator.DRKey
abbrev Model.encodeEC := CryptoVerification.E2E.Pqxdh.Initiator.encodeEC
abbrev Model.encodeKEM := CryptoVerification.E2E.Pqxdh.Initiator.encodeKEM
abbrev Model.decodeEC := CryptoVerification.E2E.Pqxdh.Initiator.decodeEC
abbrev Model.decodeKEM := CryptoVerification.E2E.Pqxdh.Initiator.decodeKEM
abbrev calculateAgreementStack : Nat := 160 + allocHookStack
abbrev createChainStack : Nat := 576 + calculateAgreementStack
def pqxdhCalculateAgreementResultAt (P : Primitives) (A : RustAlloc) (r : BitVec 64) (ourSk32
    theirPk32 : Bytes) : SepProp := if P.x25519 ourSk32 theirPk32 = List.replicate 32 0 then
    (r ↦₆₄ 1#64) ∗ (∃∗ hi : BitVec 56, (r + 8#64) ↦₆₄ (hi ++ 3#8)) ∗ (∃∗ u2 : BitVec 64, (r +
      16#64) ↦₆₄ u2)
  else (r ↦₆₄ 0#64) ∗ boxSliceU8 A (r + 8#64) (bytesToBv8 (P.x25519 ourSk32 theirPk32))
def pqxdhCalculateAgreementBaseSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64) where
  pre := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s =>
    ⌜s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧ s.readReg64 .x8 = ret ∧ s.sp = sp ∧
      ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗ (ourA ↦ₛ bytesToBv8 ourSk32) ∗
      (theirA ↦ₛ bytesToBv8 theirPk32) ∗ memRegion ret 24 ∗ A.pool ∗
      stackAt sp calculateAgreementStack
  post := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
      pqxdhCalculateAgreementResultAt P A ret ourSk32 theirPk32 ∗ A.pool ∗
      stackAt sp calculateAgreementStack
  onPanic := rustPanicOnOom img
def pqxdhCalculateAgreementSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64) where
  pre := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s =>
    ⌜s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧ s.readReg64 .x8 = ret ∧ s.sp = sp ∧
      ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗ (ourA ↦ₛ bytesToBv8 ourSk32) ∗
      (theirA ↦ₛ bytesToBv8 theirPk32) ∗ memRegion ret 24 ∗ A.pool ∗
      stackAt sp calculateAgreementStack ∗ ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8)
  post := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
      pqxdhCalculateAgreementResultAt P A ret ourSk32 theirPk32 ∗ A.pool ∗
      stackAt sp calculateAgreementStack ∗ ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8)
  onPanic := rustPanicOnOom img
def PqxdhCalculateAgreementOk_trap (P : Primitives) (A : RustAlloc) (img : Obj.Image) (C : Crypto) (absHooks : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C absHooks) ((trTrapProgAt img.base C absHooks).fnAddr calculateAgreementSym)
    (pqxdhCalculateAgreementSpec P A img)

def PqxdhCalculateAgreementOk (P : Primitives) (A : RustAlloc) (img : Obj.Image) (C : Crypto) (ctl :
    BitVec 64) (absHooks : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks) ((tripleRatchetProgAt img.base C ctl
    absHooks).fnAddr calculateAgreementSym)
    (pqxdhCalculateAgreementSpec P A img)
@[local simp, local arm64_norm, local wp_norm] theorem extractLsb_hi56_3 (hi : BitVec 56) :
    (hi ++ 3#8).extractLsb' 0 8 = 3#8 := by bv_bits
@[local simp, local arm64_norm, local wp_norm] theorem and_ff_hi56_3 (hi : BitVec 56) :
    (hi ++ 3#8) &&& 0xff#64 = 3#64 := by bv_bits
@[local simp, local arm64_norm, local wp_norm] theorem and_ff32_hi56_3 (hi : BitVec 56) :
    BitVec.truncate 32 (hi ++ 3#8) &&& 0xff#32 = 3#32 := by bv_bits
@[local simp, local arm64_norm, local wp_norm]
theorem zext64_trunc32_hi56_3_and_ff (hi : BitVec 56) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (hi ++ 3#8)) &&& 255#64 = 3#64 := by bv_bits
theorem boxSliceU8_32_entails (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) (hlen :
    bs.length = 32) : boxSliceU8 A a bs ⊢
      ∃∗ ptr : BitVec 64, (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ 32#64) ∗ (ptr ↦ₛ bs) ∗ A.live ptr 32 1 := by
  dsimp only [boxSliceU8]; rw [hlen, BitVec.ofNat_eq_ofNat]
  refine Entails.sepExists_elim fun ptr => ?_; refine Entails.pure_left fun _ => ?_
  exact Entails.sepExists_right ptr (Entails.refl _)
theorem SepWPp.rw_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp} {Q Qp : State
    → SepProp → Prop} (hP : P = P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := hP ▸ h
macro "sep_elim_exists" : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _))))
theorem SepWPp.split_alloc {prog : Program} {ret : BitVec 64} {s : State} {A : RustAlloc} {sp sp' :
    BitVec 64} {tr : List TraceEvent} {size align : Nat} {F : SepProp} {Q Qp : State → SepProp →
    Prop} (hsp : sp = sp') (hnull : s.readReg64 (.gpr 0#5) = 0#64 → s.trace = tr ++
    [allocFailedEvent] → SepWPp prog ret s (A.pool ∗ stackAt sp' allocHookStack ∗ F) Q Qp)
    (hok : s.readReg64 (.gpr 0#5) ≠ 0#64 → (s.readReg64 (.gpr 0#5)).toNat % align = 0 → s.trace =
      tr → SepWPp prog ret s (A.pool ∗ stackAt sp' allocHookStack ∗
        A.live (s.readReg64 (.gpr 0#5)) size align ∗ memRegion (s.readReg64 (.gpr 0#5)) size ∗
        F) Q Qp) : SepWPp prog ret s (A.pool ∗ stackAt sp allocHookStack ∗
      (if s.readReg64 (.gpr 0#5) = 0 then ⌜s.trace = tr ++ [allocFailedEvent]⌝
        else ⌜(s.readReg64 (.gpr 0#5)).toNat % align = 0 ∧ s.trace = tr⌝ ∗
        A.live (s.readReg64 (.gpr 0#5)) size align ∗ memRegion (s.readReg64 (.gpr 0#5)) size) ∗
        F) Q Qp := by
  subst hsp; by_cases h0 : s.readReg64 (.gpr 0#5) = 0
  · simp only [h0, ↓reduceIte]; intro R hm
    have hm' : s.mem ⊨ ⌜s.trace = tr ++ [allocFailedEvent]⌝ ∗ ((A.pool ∗ stackAt sp allocHookStack ∗
      F) ∗ R) := (by ac_nf at hm ⊢); rw [satisfies_pure_sepConj] at hm'
    exact hnull h0 hm'.1 R hm'.2
  · simp only [h0, ↓reduceIte]; intro R hm
    have hm' : s.mem ⊨ ⌜(s.readReg64 (.gpr 0#5)).toNat % align = 0 ∧ s.trace = tr⌝ ∗ ((A.pool ∗
      stackAt sp allocHookStack ∗ A.live (s.readReg64 (.gpr 0#5)) size align ∗
      memRegion (s.readReg64 (.gpr 0#5)) size ∗ F) ∗ R) := by ac_nf at hm ⊢
    rw [satisfies_pure_sepConj] at hm'; exact hok h0 hm'.1.1 hm'.1.2 R hm'.2
theorem allocFailedIn_panicked_of_append {s0 sf : State} (htr : sf.trace = s0.trace ++
    [allocFailedEvent]) :
    allocFailedIn s0 (Rust.panicked sf) ∧ s0.trace <+: (Rust.panicked sf).trace := by
  simp [allocFailedIn, Rust.panicked, htr]
theorem rodata_0x7ff6a {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) {m : Memory}
    (hro : img.RoDataLoaded m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗ P := by
  have hsec : (num% (ls_xref% 0x3e748 0x3e74c), 32) ∈ libsignalSessionImage.roData :=
    List.mem_of_elem_eq_true (by rfl_kernel)
  have ⟨h1, h2⟩ := rodata_readBytes_disjoint himg (dataOff := num% (ls_xref% 0x2440 0x2444)) rfl hsec
    (by decide) (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) m hro
  have hbytes : (libsignalSessionImage.data.drop (num% (ls_xref% 0x3e748 0x3e74c) - num% (ls_xref% 0x2440 0x2444))).take 32 =
      List.replicate 32 0#8 := (by rfl_kernel); rw [hbytes] at h2
  exact Satisfies.rodata_intro h1 h2 (by decide) hP
theorem pqxdh_shim_ok_at_trap {b : BitVec 64} {C : Crypto} {absHooks : String → Option
    (State → State)} {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        fnoff_eq) :
    subroutine_ok (trTrapProgAt b C absHooks) ((trTrapProgAt b C absHooks).fnAddr name + BitVec.ofNat 64 k) pqxdhShimSpec :=
  hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol])
    ⟨hookNoop, rfl, pqxdhShim_hookOk⟩

theorem pqxdh_shim_ok_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {absHooks : String → Option
    (State → State)} {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks) ((tripleRatchetProgAt b C ctl
      absHooks).fnAddr name + BitVec.ofNat 64 k) pqxdhShimSpec :=
  by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdh_shim_ok_at_trap hk)

theorem pqxdh_memcpy_region_ok_at_trap {b : BitVec 64} {C : Crypto} {absHooks : String
    → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff "memcpy" := by
      fnoff_eq) :
    subroutine_ok (trTrapProgAt b C absHooks) ((trTrapProgAt b C absHooks).fnAddr name + BitVec.ofNat 64 k) pqxdhMemcpyRegionSpec :=
  hook_ok_at (hname := "memcpy") rfl hk (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol])
    ⟨ProofLib.hookMemcpy, rfl, Initiator.hookMemcpy_region_trace_ok⟩

theorem pqxdh_memcpy_region_ok_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {absHooks : String
    → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff "memcpy" := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks) ((tripleRatchetProgAt b C ctl
      absHooks).fnAddr name + BitVec.ofNat 64 k) pqxdhMemcpyRegionSpec :=
  by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdh_memcpy_region_ok_at_trap hk)

theorem pqxdh_alloc_ok_at_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto} {absHooks :
    String → Option (State → State)} (hA : AllocHooks A absHooks) {name : String} {k : Nat} (hk :
    libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C absHooks) ((trTrapProgAt b C absHooks).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  alloc_ok_at_trap b C A absHooks hA name k hk

theorem pqxdh_alloc_ok_at {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {absHooks :
    String → Option (State → State)} (hA : AllocHooks A absHooks) {name : String} {k : Nat} (hk :
    libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks) ((tripleRatchetProgAt b C ctl
      absHooks).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdh_alloc_ok_at_trap hA hk)

theorem pqxdh_dealloc_ok_at_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto} {absHooks
    : String → Option (State → State)} (hA : AllocHooks A absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C absHooks) ((trTrapProgAt b C absHooks).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  dealloc_ok_at_trap b C A absHooks hA name k hk

theorem pqxdh_dealloc_ok_at {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {absHooks
    : String → Option (State → State)} (hA : AllocHooks A absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks) ((tripleRatchetProgAt b C ctl
      absHooks).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdh_dealloc_ok_at_trap hA hk)

theorem pqxdh_panic_at_raw_vec_handle_error_trap {b : BitVec 64} {C : Crypto} {absHooks
    : String → Option (State → State)} {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff
    name + k = libsignalSessionCode.fnOff "alloc::raw_vec::handle_error" := by fnoff_eq) :
    (trTrapProgAt b C absHooks).externAt? ((trTrapProgAt b C absHooks).fnAddr
      name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_handle_error_trap b C absHooks name k hk

theorem pqxdh_panic_at_raw_vec_handle_error {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {absHooks
    : String → Option (State → State)} {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff
    name + k = libsignalSessionCode.fnOff "alloc::raw_vec::handle_error" := by fnoff_eq) :
    (tripleRatchetProgAt b C ctl absHooks).externAt? ((tripleRatchetProgAt b C ctl absHooks).fnAddr
      name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_handle_error b C ctl absHooks name k hk
theorem pqxdh_panic_at_handle_alloc_error_trap {b : BitVec 64} {C : Crypto} {absHooks :
    String → Option (State → State)} {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name
    + k = libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by fnoff_eq) :
    (trTrapProgAt b C absHooks).externAt? ((trTrapProgAt b C absHooks).fnAddr
      name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_handle_alloc_error_trap b C absHooks name k hk

theorem pqxdh_panic_at_handle_alloc_error {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {absHooks :
    String → Option (State → State)} {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name
    + k = libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by fnoff_eq) :
    (tripleRatchetProgAt b C ctl absHooks).externAt? ((tripleRatchetProgAt b C ctl absHooks).fnAddr
      name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_handle_alloc_error b C ctl absHooks name k hk
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  libsignalSessionCode_fnOff_0x1af54 libsignalSessionCode_fnOff_0x3dd44
  libsignalSessionCode_fnOff_0x23920 (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy") (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "alloc::alloc::handle_alloc_error") (ls_stub% "libcrux_ml_kem::mlkem1024::kyber::decapsulate")
  (ls_stub% "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards") (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free")
  (ls_hook% "libcrux_ml_kem::mlkem1024::kyber::decapsulate") (ls_hook% "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards")
  (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free")
theorem dalekMontToEd_ok_at_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image} {C : Crypto} {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img
    absHooks) {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekMontToEdStub := by fnoff_eq) :
    subroutine_ok (trTrapProgAt img.base C absHooks) ((trTrapProgAt img.base C absHooks).fnAddr name + BitVec.ofNat 64 k)
      (dalekMontToEdStubSpec P img) := hook_ok_at (hname := dalekMontToEdStub) rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, dalekMontToEdStub])
    (hookSat_tripleRatchetExterns'_trap C absHooks rfl hH.dalekMontToEd)

theorem dalekMontToEd_ok_at {P : Primitives} {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl :
    BitVec 64} {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img
    absHooks) {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekMontToEdStub := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks) ((tripleRatchetProgAt img.base C ctl
      absHooks).fnAddr name + BitVec.ofNat 64 k)
      (dalekMontToEdStubSpec P img) := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (dalekMontToEd_ok_at_trap hH hk)

theorem dalekTorsionFree_ok_at_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image} {C : Crypto} {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img
    absHooks) {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekTorsionFreeStub := by fnoff_eq) :
    subroutine_ok (trTrapProgAt img.base C absHooks) ((trTrapProgAt img.base C absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoBoolRegStubSpec P.isTorsionFree 160 img) :=
  hook_ok_at (hname := dalekTorsionFreeStub) rfl hk (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, dalekTorsionFreeStub])
    (hookSat_tripleRatchetExterns'_trap C absHooks rfl hH.dalekTorsionFree)

theorem dalekTorsionFree_ok_at {P : Primitives} {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl
    : BitVec 64} {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img
    absHooks) {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekTorsionFreeStub := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks) ((tripleRatchetProgAt img.base C ctl
      absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoBoolRegStubSpec P.isTorsionFree 160 img) :=
  by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (dalekTorsionFree_ok_at_trap hH hk)

theorem kyberDecaps_ok_at_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image} {C : Crypto} {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img
    absHooks) {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff kyberDecapsStub := by fnoff_eq) :
    subroutine_ok (trTrapProgAt img.base C absHooks) ((trTrapProgAt img.base C absHooks).fnAddr name + BitVec.ofNat 64 k)
      (kyberDecapsStubSpec P) := hook_ok_at (hname := kyberDecapsStub) rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, kyberDecapsStub])
    (hookSat_tripleRatchetExterns'_trap C absHooks rfl hH.kyberDecaps)
attribute [local arm64_norm] bv_sub_sub_lit bv_add_neg64

theorem kyberDecaps_ok_at {P : Primitives} {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl :
    BitVec 64} {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img
    absHooks) {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff kyberDecapsStub := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks) ((tripleRatchetProgAt img.base C ctl
      absHooks).fnAddr name + BitVec.ofNat 64 k)
      (kyberDecapsStubSpec P) := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (kyberDecaps_ok_at_trap hH hk)

def ecPubKeyIsCanonicalCallSpec (P : Primitives) : Spec KeyCanonicalGhost where
  pre := fun g s => ⌜s.readReg64 .x0 = g.keyPtr ∧ g.keyBytes.length = 32⌝ ∗
    (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗ stackAt s.sp (pqxdhHookStack + 400)
  post := fun g s0 sf => ⌜sf.trace = s0.trace ∧ (sf.readReg64 .x0).setWidth 8 =
      (if P.isCanonicalEC g.keyBytes then 1#8 else 0#8)⌝ ∗ (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗
      stackAt s0.sp (pqxdhHookStack + 400)
def toSignalPqxdhPrimitives (P : Primitives) : SignalPqxdh.Primitives where
  x25519 := P.x25519; x25519Base := P.x25519Base; isCanonical := P.isCanonical
  sigPkGen := P.sigPkGen; sigSign := P.sigSign; sigVerify := P.sigVerify; sha512 := P.sha512
  scalarMul := P.scalarMul; scalarAdd := P.scalarAdd
  scalarFromBytesModOrder := P.scalarFromBytesModOrder; scalarFromWide := P.scalarFromWide
  montToEd := P.montToEd; isTorsionFree := P.isTorsionFree; edNeg := P.edNeg
  doubleScalarMulBasepoint := P.doubleScalarMulBasepoint; compress := P.compress
  kemKeyGen := P.kemKeyGen; kemEncaps := P.kemEncaps; kemDecaps := P.kemDecaps
  hkdfDerive96 := fun s =>
    let dk := P.hkdfDerive96 s
    ⟨dk.rootKey, dk.chainKey, dk.pqrKey⟩
  rootCreateChain := P.rootCreateChain; chainKdfSeed := P.chainKdfSeed
  chainKdfNext := P.chainKdfNext
  spqrInitSend := fun k c => P.spqrInitSend k c
  spqrInitRecv := fun k m => P.spqrInitRecv k m
  deriveMsgKeys := fun s salt =>
    let mk := P.deriveMsgKeys s salt
    ⟨mk.cipherKey, mk.macKey, mk.iv⟩
  aeadEnc := fun mk ad pt => P.aeadEnc ⟨mk.cipherKey, mk.macKey, mk.iv⟩ ad pt
  aeadDec := fun mk ad ct => P.aeadDec ⟨mk.cipherKey, mk.macKey, mk.iv⟩ ad ct
  pow8 := P.pow8; isValidDhTriple := P.isValidDhTriple; sha256Compress := P.sha256Compress
  sha512Compress := P.sha512Compress; aesEncBlock := P.aesEncBlock; aesDecBlock := P.aesDecBlock
theorem ecPubKeyIsCanonical_call_ok_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image} {C : Crypto} {absHooks : String → Option (State → State)} (hWF : StructuralPrims P) (hH :
    PqxdhHookContracts P A img absHooks) : subroutine_ok (trTrapProgAt img.base C absHooks) ((trTrapProgAt img.base C absHooks).fnAddr ecPubKeyIsCanonicalSym)
      (ecPubKeyIsCanonicalCallSpec P) := by
  obtain ⟨fnM, hfnM, hokM⟩ := hH.dalekMontToEd
  obtain ⟨fnT, hfnT, hokT⟩ := hH.dalekTorsionFree
  have hSub := CryptoVerification.E2E.Pqxdh.Shared.ecPubKeyIsCanonical_call_ok'_trap (P :=
    toSignalPqxdhPrimitives P) (img := img) (C := C)
    hWF.isCanonical_eq_isCanonicalRef hWF.montToEd_len
    ⟨fnM, hfnM, fun gm Rm sm hrunm hprem hspm =>
      hokM ⟨gm.inBytes, gm.signBit, gm.inPtr, gm.outPtr⟩ Rm sm hrunm hprem hspm⟩
    ⟨fnT, hfnT, fun gt Rt st hrunt hpret hspt => hokT ⟨gt.inPtr, gt.inBytes⟩ Rt st hrunt hpret hspt⟩
  exact subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp =>
    hSub.mono_outcome ⟨g.keyPtr, g.keyBytes⟩ R s0 hpc hrun hpre hsp fun _ hout => hout

theorem ecPubKeyIsCanonical_call_ok {P : Primitives} {A : RustAlloc} {img : Obj.Image} {C : Crypto}
    {ctl : BitVec 64} {absHooks : String → Option (State → State)} (hWF : StructuralPrims P) (hH :
    PqxdhHookContracts P A img absHooks) : subroutine_ok (tripleRatchetProgAt img.base C ctl
    absHooks) ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr ecPubKeyIsCanonicalSym)
      (ecPubKeyIsCanonicalCallSpec P) := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (ecPubKeyIsCanonical_call_ok_trap hWF hH)

def incomingWord0 : BitVec 64 := 0x676e696d6f636e69#64 -- "incoming"
def incomingWord1 : BitVec 64 := 0x656b206573616220#64 -- " base ke"
def incomingWord2 : BitVec 64 := 0x73692079656b2065#64 -- "e key is" (bytes 12..20)
def incomingWord3 : BitVec 64 := 0x64696c61766e6920#64 -- " invalid" (bytes 20..28)
theorem incomingBaseKeyInvalidBytes_split1_eq : incomingBaseKeyInvalidBytes =
      unpack64 incomingWord0 ++ (unpack64 incomingWord1 ++ incomingBaseKeyInvalidBytes.drop 16) :=
        by decide +kernel
theorem incomingBaseKeyInvalidBytes_split2_eq : incomingBaseKeyInvalidBytes =
      incomingBaseKeyInvalidBytes.take 12 ++ (unpack64 incomingWord2 ++ unpack64 incomingWord3) :=
        by decide +kernel
theorem rodata_incoming_split1 (a : BitVec 64) : (a ↦ᵣ incomingBaseKeyInvalidBytes) =
      ((a ↦₆₄ᵣ incomingWord0) ∗ ((a + 8#64) ↦₆₄ᵣ incomingWord1) ∗ ((a +
        16#64) ↦ᵣ (incomingBaseKeyInvalidBytes.drop 16))) := by
  rw [incomingBaseKeyInvalidBytes_split1_eq, pointsToBytesRO_append, ←
    pointsTo64RO_eq_pointsToBytesRO, unpack64_length, pointsToBytesRO_append, ←
    pointsTo64RO_eq_pointsToBytesRO, unpack64_length, show a + BitVec.ofNat 64 8 +
      BitVec.ofNat 64 8 = a + 16#64 by bv_omega]; ac_rfl
theorem rodata_incoming_split2 (a : BitVec 64) : (a ↦ᵣ incomingBaseKeyInvalidBytes) =
      ((a ↦ᵣ incomingBaseKeyInvalidBytes.take 12) ∗ ((a + 12#64) ↦₆₄ᵣ incomingWord2) ∗ ((a +
        20#64) ↦₆₄ᵣ incomingWord3)) := by
  rw [incomingBaseKeyInvalidBytes_split2_eq, pointsToBytesRO_append, pointsToBytesRO_append, ←
    pointsTo64RO_eq_pointsToBytesRO, ← pointsTo64RO_eq_pointsToBytesRO,
      show (incomingBaseKeyInvalidBytes.take 12).length = 12 by decide, unpack64_length, show a +
        BitVec.ofNat 64 12 = a + 12#64 by bv_omega, show a + 12#64 + BitVec.ofNat 64 8 = a +
        20#64 by bv_omega]; ac_rfl
theorem rodata_incoming_1_to_2 (a : BitVec 64) : (a ↦₆₄ᵣ incomingWord0) ∗ ((a +
    8#64) ↦₆₄ᵣ incomingWord1) ∗ ((a + 16#64) ↦ᵣ (incomingBaseKeyInvalidBytes.drop 16)) =
    (a ↦ᵣ incomingBaseKeyInvalidBytes.take 12) ∗ ((a + 12#64) ↦₆₄ᵣ incomingWord2) ∗ ((a +
      20#64) ↦₆₄ᵣ incomingWord3) := by rw [← rodata_incoming_split1, rodata_incoming_split2]
theorem incoming_alloc_split (p : BitVec 64) : memRegion p 28 = (∃∗ u0 : BitVec 64, p ↦₆₄ u0) ∗ (∃∗
      u1 : BitVec 64, (p + 8#64) ↦₆₄ u1) ∗ memRegion (p + 16#64) 12 := by
  rw [show (28 : Nat) = 8 + (8 + 12) by decide, memRegion_split p 8 20 (by decide),
    memRegion_split (p + 8#64) 8 12 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem incoming_overlap_prep (p w0 w1 : BitVec 64) : (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗
    memRegion (p + 16#64) 12 ⊢ memRegion p 12 ∗ (∃∗ u2 : BitVec 64, (p + 12#64) ↦₆₄ u2) ∗ (∃∗
      u3 : BitVec 64, (p + 20#64) ↦₆₄ u3) := by
  have hm0 : (p ↦₆₄ w0) ⊢ memRegion p 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right w0 (Entails.refl _)
  have hm1 : ((p + 8#64) ↦₆₄ w1) ⊢ memRegion (p + 8#64) 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right w1 (Entails.refl _)
  refine Entails.trans (sepConj_mono hm0 (sepConj_mono_left hm1)) ?_
  have heq : memRegion p 8 ∗ (memRegion (p + 8#64) 8 ∗ memRegion (p + 16#64) 12) =
      memRegion p 12 ∗ (∃∗ u2 : BitVec 64, (p + 12#64) ↦₆₄ u2) ∗ (∃∗ u3 : BitVec 64, (p +
        20#64) ↦₆₄ u3) := by
    rw [show p + 16#64 = p + 8#64 + BitVec.ofNat 64 8 by bv_omega, ←
      memRegion_split (p + 8#64) 8 12 (by decide), show p + 8#64 = p + BitVec.ofNat 64 8
      by bv_omega, ← memRegion_split p 8 20 (by decide), show (8 + 20 : Nat) = 12 + (8 +
        8) by decide, memRegion_split p 12 16 (by decide), memRegion_split (p +
        BitVec.ofNat 64 12) 8 8 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq heq
theorem uint8_ofNat_shift_mod_toBitVec (w : BitVec 64) (s : Nat) :
    BitVec.ofNat 8 (UInt8.ofNat ((w.toNat >>> s) % 256)).toNat = w.extractLsb' s 8 := by
  apply BitVec.eq_of_toNat_eq; simp [UInt8.ofNat, BitVec.toNat_ofNat, BitVec.extractLsb']
theorem bytesToBv8_encodeU64LE (w : BitVec 64) : bytesToBv8 (encodeU64LE w) = unpack64 w := by
  simp only [encodeU64LE, bytesToBv8, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    Nat.mul_zero, Nat.mul_succ, List.map_cons, List.map_nil, uint8_ofNat_shift_mod_toBitVec,
    unpack64]
theorem pointsToBytes_encodeU64LE (a w : BitVec 64) :
    (a ↦ₛ bytesToBv8 (encodeU64LE w)) = (a ↦₆₄ w) := by
  rw [bytesToBv8_encodeU64LE, ← pointsTo64_eq_pointsToBytes]
theorem bytesToBv8_head_tail (a : BitVec 64) (bs : List (BitVec 8)) (h : 1 ≤ bs.length) :
    (a ↦ₛ bs) = (a ↦₈ bs.getD 0 0#8) ∗ ((a + 1#64) ↦ₛ bs.drop 1) := by
  rcases bs with _ | ⟨b0, tail⟩
  · simp at h
  · simp [pointsToBytes_cons]
theorem opkBSk_getD_length {inp : AcceptKeysInput} (h : WellSizedAcceptKeysInput inp) :
    (inp.opkBSk?.getD (List.replicate 32 0)).length = 32 := by
  rcases h with ⟨_, _, _, _, hopk, _, _, _, _, _⟩
  cases hopk_eq : inp.opkBSk? with
  | none => simp | some sk => exact hopk sk hopk_eq
theorem bytesToBv8_fitBytes_length (n : Nat) (bs : Bytes) :
    (bytesToBv8 (fitBytes n bs)).length = n := by simp [bytesToBv8]
theorem bytesToBv8_encodeU64LE_length (w : BitVec 64) :
    (bytesToBv8 (encodeU64LE w)).length = 8 := by rw [bytesToBv8_encodeU64LE, unpack64_length]
theorem pointsToBytes_split_at (a : BitVec 64) (xs ys : Bytes) (n : Nat) (h : (bytesToBv8 xs).length
    = n) : (a ↦ₛ bytesToBv8 (xs ++ ys)) =
      (a ↦ₛ bytesToBv8 xs) ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bytesToBv8 ys) := by
  rw [bytesToBv8_append, pointsToBytes_append, h]
theorem outPtr_err104_split (outPtr : BitVec 64) : memRegion outPtr 104 = (∃∗ v0 : BitVec 32,
      outPtr ↦₃₂ v0) ∗ memRegion (outPtr + 4#64) 4 ∗ (∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗
        w3 : BitVec 64, ∃∗ w4 : BitVec 64, ((outPtr + 8#64) ↦₆₄ w1) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
        ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4)) ∗ (∃∗
        b40 : BitVec 8, (outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 := by
  rw [show (104 : Nat) = 4 + (4 + (32 + (1 + 63))) by decide, memRegion_split outPtr 4 100
    (by decide), memRegion_split (outPtr + 4#64) 4 96 (by decide), memRegion_split (outPtr + 4#64 +
    4#64) 32 64 (by decide), memRegion_split (outPtr + 4#64 + 4#64 + 32#64) 1 63 (by decide),
      memRegion_four outPtr, (memRegion_cells (outPtr + 4#64 + 4#64) 4 (by decide) :
        memRegion (outPtr + 4#64 + 4#64) 32 = cells (outPtr + 4#64 + 4#64) 4),
        memRegion_one (outPtr + 4#64 + 4#64 + 32#64)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
theorem pointsTo32_one_entails_tag_ne_zero (a : BitVec 64) : (a ↦₃₂ 1#32) ⊢
      (∃∗ tag : BitVec 8, ⌜tag ≠ 0#8⌝ ∗ (a ↦₈ tag)) ∗ memRegion (a + 1#64) 3 := by
  rw [pointsTo32_eq_pointsToBytes]; have hu : unpack32 1#32 = [1#8, 0#8, 0#8, 0#8] := rfl
  rw [hu, pointsToBytes_cons]
  have htag : (a ↦₈ 1#8) ⊢ ∃∗ tag : BitVec 8, ⌜tag ≠ 0#8⌝ ∗ (a ↦₈ tag) := by
    have hne : (1#8 : BitVec 8) ≠ 0#8 := (by decide); rw [← pure_sepConj_of_true hne (a ↦₈ 1#8)]
    exact Entails.sepExists_right 1#8 (Entails.refl _)
  exact sepConj_mono htag (pointsToBytes_entails_memRegion (a + 1#64) [0#8, 0#8, 0#8])
theorem outPtr_err104_merge (outPtr w1 w2 w3 w4 : BitVec 64) (b40 : BitVec 8) : (outPtr ↦₃₂ 1#32) ∗
    memRegion (outPtr + 4#64) 4 ∗ ((outPtr + 8#64) ↦₆₄ w1) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr +
      24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗ ((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr +
      41#64) 63 ⊢
      (∃∗ tag : BitVec 8, ⌜tag ≠ 0#8⌝ ∗ (outPtr ↦₈ tag)) ∗ memRegion (outPtr + 1#64) 103 := by
  have hc4 := cells_4_merge (outPtr + 8#64) w1 w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hc4
  rw [← (memRegion_cells (outPtr + 8#64) 4 (by decide) : memRegion (outPtr + 8#64) 32 =
    cells (outPtr + 8#64) 4)] at hc4
  have hb40 : ((outPtr + 40#64) ↦₈ b40) ⊢ memRegion (outPtr + 40#64) 1 := by
    rw [memRegion_one]; exact Entails.sepExists_right b40 (Entails.refl _)
  have h1 := pointsTo32_one_entails_tag_ne_zero outPtr
  have hm103 : memRegion (outPtr + 1#64) 3 ∗ (memRegion (outPtr + 4#64) 4 ∗ (memRegion (outPtr +
    8#64) 32 ∗ (memRegion (outPtr + 40#64) 1 ∗ memRegion (outPtr + 41#64) 63))) =
      memRegion (outPtr + 1#64) 103 := by
    rw [show outPtr + 41#64 = outPtr + 40#64 + BitVec.ofNat 64 1 by bv_omega, ←
      memRegion_split (outPtr + 40#64) 1 63 (by decide), show outPtr + 40#64 = outPtr + 8#64 +
      BitVec.ofNat 64 32 by bv_omega, ← memRegion_split (outPtr + 8#64) 32 64 (by decide),
        show outPtr + 8#64 = outPtr + 4#64 + BitVec.ofNat 64 4 by bv_omega, ←
        memRegion_split (outPtr + 4#64) 4 96 (by decide),
        show outPtr + 4#64 = outPtr + 1#64 + BitVec.ofNat 64 3 by bv_omega, ←
          memRegion_split (outPtr + 1#64) 3 100 (by decide)]
  rw [← hm103]; refine Entails.trans (sepConj_mono_left h1) ?_; rw [sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  have hswap : ((outPtr + 8#64) ↦₆₄ w1) ∗ (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗
    (((outPtr + 32#64) ↦₆₄ w4) ∗ (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63)))) =
      (((outPtr + 8#64) ↦₆₄ w1) ∗ (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗
        ((outPtr + 32#64) ↦₆₄ w4)))) ∗ (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr +
        41#64) 63) := by ac_rfl
  rw [hswap]; exact sepConj_mono hc4 (sepConj_mono_left hb40)
theorem outPtr_ok104_split (outPtr : BitVec 64) : memRegion outPtr 104 = (∃∗ v0 : BitVec 32,
      outPtr ↦₃₂ v0) ∗ cells (outPtr + 4#64) 12 ∗ (∃∗ v100 : BitVec 32,
        (outPtr + 100#64) ↦₃₂ v100) := by
  rw [show (104 : Nat) = 4 + 100 by decide, memRegion_split outPtr 4 100 (by decide),
    memRegion_four outPtr, memRegion_out_derive (outPtr + 4#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem outPtr_ok104_eq (outPtr : BitVec 64) (dk : DRKey) : (outPtr ↦₃₂ 0#32) ∗ ((outPtr +
    4#64) ↦ₛ bytesToBv8 (handshakeKeysBytes100 dk)) =
      (outPtr ↦ₛ bytesToBv8 (handshakeKeysResultOk104 dk)) := by
  unfold handshakeKeysResultOk104
  rw [bytesToBv8_append, pointsToBytes_append, pointsTo32_eq_pointsToBytes]; rfl
theorem sp_sub4912_orr_one {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 4912#64) ||| 1#64 = sp - 4911#64 := by revert h; bv_bits
theorem sp_sub1744_orr_one {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 1744#64) ||| 1#64 = sp - 1743#64 := by revert h; bv_bits
theorem subStack_to_alloc (sp : BitVec 64) : stackAt (sp - 4944#64) (pqxdhHookStack + 400) =
      memRegion (sp - 9440#64) 400 ∗ stackAt (sp - 4944#64) allocHookStack := by
  simp only [stackAt, pqxdhHookStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - 4944#64 - BitVec.ofNat 64 4496) (n := 400) (k := 4096)
    (b' := sp - 4944#64 - BitVec.ofNat 64 4096) rfl (by bv_omega) (by decide)]
  have h1 : sp - 4944#64 - BitVec.ofNat 64 4496 = sp - 9440#64 := (by bv_omega); rw [h1]
theorem subStack_to_calc (sp : BitVec 64) : stackAt (sp - 4944#64) (pqxdhHookStack + 400) =
      memRegion (sp - 9440#64) 240 ∗ stackAt (sp - 4944#64) calculateAgreementStack := by
  simp only [stackAt, pqxdhHookStack, calculateAgreementStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - 4944#64 - BitVec.ofNat 64 4496) (n := 240) (k := 4256)
    (b' := sp - 4944#64 - BitVec.ofNat 64 4256) rfl (by bv_omega) (by decide)]
  have h1 : sp - 4944#64 - BitVec.ofNat 64 4496 = sp - 9440#64 := (by bv_omega); rw [h1]
theorem subStack_to_vecAppend (sp : BitVec 64) : stackAt (sp - 4944#64) (pqxdhHookStack + 400) =
      memRegion (sp - 9440#64) 4448 ∗ cells (sp - 4992#64) 6 := by
  simp only [stackAt, pqxdhHookStack]
  rw [ProofLib.memRegion_split' (b := sp - 4944#64 - BitVec.ofNat 64 4496) (n := 4448) (k := 48)
    (b' := sp - 4992#64) rfl (by bv_omega) (by decide), (memRegion_cells (sp - 4992#64) 6
      (by decide) : memRegion (sp - 4992#64) 48 = cells (sp - 4992#64) 6)]
  have h1 : sp - 4944#64 - BitVec.ofNat 64 4496 = sp - 9440#64 := (by bv_omega); rw [h1]
theorem stackAt_pqxdh_accept_top (sp : BitVec 64) : stackAt sp pqxdhEntryStack = memRegion (sp -
      16384#64) 6944 ∗ stackAt (sp - 4944#64) (pqxdhHookStack + 400) ∗ cells (sp - 4944#64) 4 ∗
        memRegion (sp - 4912#64) 3168 ∗ memRegion (sp - 1744#64) 1568 ∗ memRegion (sp -
        176#64) 96 ∗ cells (sp - 80#64) 10 := by
  simp only [stackAt, pqxdhEntryStack, pqxdhHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16384) (n := 6944) (k := 9440) (b' :=
        sp - 9440#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 9440#64) (n := 4496) (k := 4944) (b' :=
        sp - 4944#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 4944#64) (n := 32) (k := 4912) (b' :=
        sp - 4912#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 4912#64) (n := 3168) (k := 1744) (b' :=
        sp - 1744#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 1744#64) (n := 1568) (k := 176) (b' :=
        sp - 176#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 176#64) (n := 96) (k := 80) (b' :=
        sp - 80#64) rfl (by bv_omega) (by decide), (memRegion_cells (sp - 4944#64) 4 (by decide) :
        memRegion (sp - 4944#64) 32 = cells (sp - 4944#64) 4), (memRegion_cells (sp - 80#64) 10
        (by decide) : memRegion (sp - 80#64) 80 = cells (sp - 80#64) 10)]
  have h1 : sp - 4944#64 - BitVec.ofNat 64 4496 = sp - 9440#64 := by bv_omega
  have h2 : sp - BitVec.ofNat 64 16384 = sp - 16384#64 := rfl; rw [h1, h2]
theorem pqsk_region_phaseA_split (sp : BitVec 64) : memRegion (sp - 4912#64) 3168 = memRegion (sp -
      4912#64) 24 ∗ memRegion (sp - 4888#64) 712 ∗ (∃∗ v_probe : BitVec 64, (sp -
        4176#64) ↦₆₄ v_probe) ∗ memRegion (sp - 4168#64) 2424 := by
  rw [ProofLib.memRegion_split' (b := sp - 4912#64) (n := 24) (k := 3144) (b' :=
        sp - 4888#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 4888#64) (n := 712) (k := 2432) (b' :=
        sp - 4176#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 4176#64) (n := 8) (k := 2424) (b' :=
        sp - 4168#64) rfl (by bv_omega) (by decide), memRegion_eight (sp - 4176#64)]
theorem pqsk_region_phaseA_merge (sp v_probe : BitVec 64) : memRegion (sp - 4912#64) 24 ∗
    memRegion (sp - 4888#64) 712 ∗ ((sp - 4176#64) ↦₆₄ v_probe) ∗ memRegion (sp - 4168#64) 2424 ⊢
      memRegion (sp - 4912#64) 3168 := by
  rw [pqsk_region_phaseA_split sp]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
  exact Entails.sepExists_right v_probe (Entails.refl _)
theorem pqsk_region_phaseA_cells_merge (sp w0 w1 w2 v_probe : BitVec 64) : ((sp - 4912#64) ↦₆₄ w0) ∗
    ((sp - 4904#64) ↦₆₄ w1) ∗ ((sp - 4896#64) ↦₆₄ w2) ∗ memRegion (sp - 4888#64) 712 ∗ ((sp -
      4176#64) ↦₆₄ v_probe) ∗ memRegion (sp - 4168#64) 2424 ⊢ memRegion (sp - 4912#64) 3168 := by
  have hc3 := cells_3_merge (sp - 4912#64) w0 w1 w2
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hc3
  rw [← (memRegion_cells (sp - 4912#64) 3 (by decide) : memRegion (sp - 4912#64) 24 = cells (sp -
    4912#64) 3)] at hc3; refine Entails.trans ?_ (pqsk_region_phaseA_merge sp v_probe)
  have hassoc : ((sp - 4912#64) ↦₆₄ w0) ∗ (((sp - 4904#64) ↦₆₄ w1) ∗ (((sp - 4896#64) ↦₆₄ w2) ∗
    (memRegion (sp - 4888#64) 712 ∗ (((sp - 4176#64) ↦₆₄ v_probe) ∗ memRegion (sp -
    4168#64) 2424)))) =
      (((sp - 4912#64) ↦₆₄ w0) ∗ (((sp - 4904#64) ↦₆₄ w1) ∗ ((sp - 4896#64) ↦₆₄ w2))) ∗
        (memRegion (sp - 4888#64) 712 ∗ (((sp - 4176#64) ↦₆₄ v_probe) ∗ memRegion (sp -
        4168#64) 2424)) := by ac_rfl
  rw [hassoc]; exact sepConj_mono_left hc3
theorem pqsk_region_phaseB_split (sp : BitVec 64) : memRegion (sp - 4912#64) 3168 =
      (∃∗ b0 : BitVec 8, (sp - 4912#64) ↦₈ b0) ∗ memRegion (sp - 4911#64) 3167 := by
  rw [ProofLib.memRegion_split' (b := sp - 4912#64) (n := 1) (k := 3167) (b' :=
        sp - 4911#64) rfl (by bv_omega) (by decide), memRegion_one (sp - 4912#64)]
theorem kemct_region_phaseB_split (sp : BitVec 64) : memRegion (sp - 1744#64) 1568 =
      (∃∗ b0 : BitVec 8, (sp - 1744#64) ↦₈ b0) ∗ memRegion (sp - 1743#64) 1567 := by
  rw [ProofLib.memRegion_split' (b := sp - 1744#64) (n := 1) (k := 1567) (b' :=
        sp - 1743#64) rfl (by bv_omega) (by decide), memRegion_one (sp - 1744#64)]
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
theorem accept_adrp_55604_1 {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) : ((b + 0x23920#64 +
    220#64 &&& 0xfffffffffffff000#64) + bv% (ls_str% "incoming base key is invalid" - 0x23000)) = b + bv% (ls_str% "incoming base key is invalid") := by revert hb; bv_bits
theorem accept_adrp_55604_2 {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) : ((b + 0x23920#64 +
    220#64 &&& 0xfffffffffffff000#64) + bv% (page% (ls_str% "incoming base key is invalid") - 0x23000) + bv% ((ls_str% "incoming base key is invalid") % 4096)) = b + bv% (ls_str% "incoming base key is invalid") := by
  revert hb; bv_bits
theorem accept_adrp_55267_1 {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) : ((b + 0x23920#64 +
    1064#64 &&& 0xfffffffffffff000#64) + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024" - 0x23000)) = b + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by revert hb; bv_bits
theorem accept_adrp_55267_2 {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) : ((b + 0x23920#64 +
    1064#64 &&& 0xfffffffffffff000#64) + bv% (page% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") - 0x23000) + bv% ((ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") % 4096)) = b + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
  revert hb; bv_bits
theorem pointsTo64_4_allOnes_eq_F_X25519 (a : BitVec 64) : (a ↦₆₄ 0xffffffffffffffff#64) ∗ ((a +
    8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((a + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((a +
      24#64) ↦₆₄ 0xffffffffffffffff#64) = (a ↦ₛ bytesToBv8 F_X25519) := by
  have hf : bytesToBv8 F_X25519 =
      unpack64 0xffffffffffffffff#64 ++ (unpack64 0xffffffffffffffff#64 ++
        (unpack64 0xffffffffffffffff#64 ++ unpack64 0xffffffffffffffff#64)) := by rfl_kernel
  rw [hf, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, unpack64_length, ←
    pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem cells4_eq (a : BitVec 64) : cells a 4 = ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗
      u2 : BitVec 64, ∃∗ u3 : BitVec 64, (a ↦₆₄ u0) ∗ ((a +
        8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
theorem memRegion_192_init_split (a : BitVec 64) : memRegion a 192 = (∃∗ u0 : BitVec 64, ∃∗
      u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a +
        16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3)) ∗ memRegion (a + 32#64) 32 ∗ memRegion (a +
        64#64) 32 ∗ memRegion (a + 96#64) 32 ∗ memRegion (a +
        128#64) 32 ∗ memRegion (a + 160#64) 32 := by
  rw [show (192 : Nat) = 32 + (32 + (32 + (32 + (32 + 32)))) by decide, memRegion_split a 32 160
    (by decide), memRegion_split (a + 32#64) 32 128 (by decide), memRegion_split (a + 32#64 +
    32#64) 32 96 (by decide), memRegion_split (a + 32#64 + 32#64 + 32#64) 32 64 (by decide),
      memRegion_split (a + 32#64 + 32#64 + 32#64 + 32#64) 32 32 (by decide), (memRegion_cells a 4
        (by decide) : memRegion a 32 = cells a 4), cells4_eq a]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem pointsToBytes_append_at (a : BitVec 64) (xs ys : Bytes) (n : Nat) (h : (bytesToBv8
    xs).length = n) : (a ↦ₛ bytesToBv8 xs) ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bytesToBv8 ys) =
      (a ↦ₛ bytesToBv8 (xs ++ ys)) := (pointsToBytes_split_at a xs ys n h).symm
theorem hmacState_merge_sub1744 (P : Primitives) (sp : BitVec 64) (prk : Bytes) {w0 w1 w2 w3 w4 w5
    w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64} (hhmac : PqxdhHmacGood P prk w0 w1 w2
    w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) : (((sp - 1744#64) ↦₆₄ w0) ∗ ((sp -
    1736#64) ↦₆₄ w1) ∗ ((sp - 1728#64) ↦₆₄ w2) ∗ ((sp - 1720#64) ↦₆₄ w3) ∗ ((sp - 1712#64) ↦₆₄ w4) ∗
      ((sp - 1704#64) ↦₆₄ w5) ∗ ((sp - 1696#64) ↦₆₄ w6) ∗ ((sp - 1688#64) ↦₆₄ w7) ∗ ((sp -
      1680#64) ↦₆₄ w8) ∗ ((sp - 1672#64) ↦₆₄ w9) ∗ ((sp - 1664#64) ↦₆₄ w10) ∗ ((sp -
      1656#64) ↦₆₄ w11) ∗ ((sp - 1648#64) ↦₆₄ w12) ∗ ((sp - 1640#64) ↦₆₄ w13) ∗ ((sp -
      1632#64) ↦₆₄ w14) ∗ ((sp - 1624#64) ↦₆₄ w15) ∗ ((sp - 1616#64) ↦₆₄ w16) ∗ ((sp -
        1608#64) ↦₆₄ w17)) ⊢ pqxdhHmacStateAt P (sp - 1744#64) prk := by
  have hmrg := hmacCore_merge P (sp - 1744#64) prk hhmac
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hmrg; exact hmrg
theorem acceptKeys_eq_none_of_not_canonical (P : Primitives) (inp : AcceptKeysInput) (htrust :
    inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = false) :
    Model.acceptKeys P inp = none := by
  simp only [Model.acceptKeys, htrust, hreplay, hik, hek, hcanon, beq_self_eq_true,
    Bool.false_eq_true, «guard», bind, pure, ↓reduceIte]; rfl
theorem acceptKeys_eq_none_of_dh1_zero (P : Primitives) (inp : AcceptKeysInput) (htrust :
    inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = true)
    (hdh1 : P.x25519 inp.spkBSk inp.hdr.ikAPk = List.replicate 32 0) :
    Model.acceptKeys P inp = none := by
  simp only [Model.acceptKeys, htrust, hreplay, hik, hek, hcanon, hdh1, beq_self_eq_true,
    bne_self_eq_false, Bool.false_eq_true, «guard», bind, pure, ↓reduceIte]; rfl
theorem acceptKeys_eq_none_of_dh2_zero (P : Primitives) (inp : AcceptKeysInput) (htrust :
    inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = true)
    (hdh1 : P.x25519 inp.spkBSk inp.hdr.ikAPk ≠ List.replicate 32 0)
    (hdh2 : P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0) :
    Model.acceptKeys P inp = none := by
  have hdh1_bne : (P.x25519 inp.spkBSk inp.hdr.ikAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh1
  simp only [Model.acceptKeys, htrust, hreplay, hik, hek, hcanon, hdh1_bne, hdh2, beq_self_eq_true,
    bne_self_eq_false, Bool.false_eq_true, «guard», bind, pure, ↓reduceIte]; rfl
theorem acceptKeys_eq_some_of_opk_none (P : Primitives) (inp : AcceptKeysInput) (ss : Bytes)
    (htrust : inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = true)
    (hdh1 : P.x25519 inp.spkBSk inp.hdr.ikAPk ≠ List.replicate 32 0)
    (hdh2 : P.x25519 inp.ikBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hdh3 : P.x25519 inp.spkBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hopk_eq : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome) (hopk : inp.opkBSk? = none)
    (hkem : P.kemDecaps inp.pqspkBSk inp.hdr.kemCt = some ss) : Model.acceptKeys P inp =
      some (Model.deriveDRKeys P (buildSecrets (P.x25519 inp.spkBSk inp.hdr.ikAPk) (P.x25519
        inp.ikBSk inp.hdr.ekAPk) (P.x25519 inp.spkBSk inp.hdr.ekAPk) none ss)) := by
  have hopkId : inp.hdr.opkId? = none := by cases h : inp.hdr.opkId? <;> simp_all
  have hdh1_bne : (P.x25519 inp.spkBSk inp.hdr.ikAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh1
  have hdh2_bne : (P.x25519 inp.ikBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh2
  have hdh3_bne : (P.x25519 inp.spkBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh3
  simp only [Model.acceptKeys, Model.deriveDRKeys, dhOptNonZero, htrust, hreplay, hik, hek, hcanon,
    hdh1_bne, hdh2_bne, hdh3_bne, hopk, hopkId, hkem, beq_self_eq_true, «guard», bind, pure,
    ↓reduceIte]; rfl
theorem acceptKeys_eq_some_of_opk_some (P : Primitives) (inp : AcceptKeysInput) (opkSk ss : Bytes)
    (htrust : inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = true)
    (hdh1 : P.x25519 inp.spkBSk inp.hdr.ikAPk ≠ List.replicate 32 0)
    (hdh2 : P.x25519 inp.ikBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hdh3 : P.x25519 inp.spkBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hopk_eq : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome) (hopk : inp.opkBSk? = some opkSk)
    (hdh4 : P.x25519 opkSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hkem : P.kemDecaps inp.pqspkBSk inp.hdr.kemCt = some ss) : Model.acceptKeys P inp =
      some (Model.deriveDRKeys P (buildSecrets (P.x25519 inp.spkBSk inp.hdr.ikAPk) (P.x25519
        inp.ikBSk inp.hdr.ekAPk) (P.x25519 inp.spkBSk inp.hdr.ekAPk)
        (some (P.x25519 opkSk inp.hdr.ekAPk)) ss)) := by
  obtain ⟨opkId, hopkId⟩ : ∃ id, inp.hdr.opkId? = some id := by
    cases h : inp.hdr.opkId? with
    | none => simp [h, hopk] at hopk_eq | some id => exact ⟨id, rfl⟩
  have hdh1_bne : (P.x25519 inp.spkBSk inp.hdr.ikAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh1
  have hdh2_bne : (P.x25519 inp.ikBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh2
  have hdh3_bne : (P.x25519 inp.spkBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh3
  have hdh4_bne : (P.x25519 opkSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh4
  simp only [Model.acceptKeys, Model.deriveDRKeys, dhOptNonZero, htrust, hreplay, hik, hek, hcanon,
    hdh1_bne, hdh2_bne, hdh3_bne, hopk, hopkId, hkem, beq_self_eq_true, «guard», bind, pure,
    ↓reduceIte]
  change (if (P.x25519 opkSk inp.hdr.ekAPk != List.replicate 32 0) =
    true then some () else failure).bind _ = _
  rw [hdh4_bne]; rfl
theorem err28_anyHeap_intro (A : RustAlloc) (ptr w2 w3 : BitVec 64) : memRegion ptr 12 ∗ ((ptr +
    12#64) ↦₆₄ w2) ∗ ((ptr + 20#64) ↦₆₄ w3) ∗ A.live ptr 28 1 ⊢ anyHeap := ent_anyHeap _
theorem emp_entails_anyHeap : emp ⊢ anyHeap := ent_anyHeap emp
theorem cells_sub4944_4_merge (sp v0 v1 v2 v3 : BitVec 64) : ((sp - 4944#64) ↦₆₄ v0) ∗ ((sp -
    4936#64) ↦₆₄ v1) ∗ ((sp - 4928#64) ↦₆₄ v2) ∗ ((sp - 4920#64) ↦₆₄ v3) ⊢
      cells (sp - 4944#64) 4 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using cells_4_merge (sp - 4944#64) v0 v1 v2 v3
theorem cells_sub80_10_merge (sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) : ((sp -
    80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗ ((sp - 56#64) ↦₆₄ c3) ∗
      ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗ ((sp - 32#64) ↦₆₄ c6) ∗ ((sp -
      24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗ ((sp - 8#64) ↦₆₄ c9) ⊢ cells (sp - 80#64) 10 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using cells_10_merge (sp -
    80#64) c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
theorem SepWP.pure_left_elim {prog : Program} {target : BitVec 64} {s : State} {φ : Prop} {P Q :
    SepProp} {post : State → SepProp → Prop} (h : φ → SepWP prog target s (P ∗ Q) post) :
    SepWP prog target s ((⌜φ⌝ ∗ P) ∗ Q) post := by rw [sepConj_assoc]; exact SepWP.pure_elim h
theorem SepWP.exists_left_elim {α : Type} {prog : Program} {target : BitVec 64} {s : State} {P : α →
    SepProp} {Q : SepProp} {post : State → SepProp → Prop} (h : ∀ x, SepWP prog target s (P x ∗
    Q) post) : SepWP prog target s ((∃∗ x, P x) ∗ Q) post := by
  rw [sepExists_sepConj_left]; exact SepWP.exists_elim h
theorem SepWPp.exists_left_elim {α : Type} {prog : Program} {ret : BitVec 64} {s : State} {P : α →
    SepProp} {Q : SepProp} {Qok Qp : State → SepProp → Prop} (h : ∀ x, SepWPp prog ret s (P x ∗
    Q) Qok Qp) : SepWPp prog ret s ((∃∗ x, P x) ∗ Q) Qok Qp := by
  rw [sepExists_sepConj_left]; exact SepWPp.exists_elim h
macro "sep_elim_exists'" : tactic =>
  `(tactic| (
    try (conv => arg 4; arg 1; simp only [sepExists_sepConj_left, sepExists_sepConj_right])
    repeat' (first
      | (with_reducible apply SepWPp.exists_left_elim; intro _)
      | (with_reducible apply SepWP.exists_left_elim; intro _)
      | (with_reducible apply SepWPp.exists_elim; intro _)
      | (with_reducible apply SepWP.exists_elim; intro _))))
theorem cells10_sub80_eq (sp : BitVec 64) : cells (sp - 80#64) 10 = ∃∗ c0 : BitVec 64, ∃∗
      c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗
        c6 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ((sp -
        80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗ ((sp - 56#64) ↦₆₄ c3) ∗
        ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗ ((sp - 32#64) ↦₆₄ c6) ∗ ((sp -
        24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗ ((sp - 8#64) ↦₆₄ c9) := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
theorem cells4_sub4944_eq (sp : BitVec 64) : cells (sp - 4944#64) 4 = ∃∗ v0 : BitVec 64, ∃∗
      v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64, ((sp - 4944#64) ↦₆₄ v0) ∗ ((sp -
        4936#64) ↦₆₄ v1) ∗ ((sp - 4928#64) ↦₆₄ v2) ∗ ((sp - 4920#64) ↦₆₄ v3) := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
theorem spAligned_sub_4944 {sp sp' : BitVec 64} (halign : (sp &&& 15#64 == 0#64) = true)
    (hsp : sp' = sp - 4944#64) : (sp' &&& 15#64 == 0#64) = true := by
  subst hsp; revert halign; bv_bits
theorem allocFailedIn_of_trace_eq {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  rcases h with ⟨ha, hp⟩; unfold allocFailedIn at ha ⊢; rw [← htr]; exact ⟨ha, hp⟩
theorem subroutine_ok_inImage_rodata4 {α : Type} {prog : Program} {entry : BitVec 64} {img :
    Obj.Image} {roAddr1 roAddr2 roAddr3 roAddr4 : BitVec 64} {roBytes1 roBytes2 roBytes3 roBytes4 :
    List (BitVec 8)} {spec : Spec α} (hro1 : ∀ {m : Memory} (_ : img.RoDataLoaded m) {P : SepProp},
      (m ⊨ P) → (m ⊨ (roAddr1 ↦ᵣ roBytes1) ∗ P))
    (hro2 : ∀ {m : Memory} (_ : img.RoDataLoaded m) {P : SepProp},
      (m ⊨ P) → (m ⊨ (roAddr2 ↦ᵣ roBytes2) ∗ P))
    (hro3 : ∀ {m : Memory} (_ : img.RoDataLoaded m) {P : SepProp},
      (m ⊨ P) → (m ⊨ (roAddr3 ↦ᵣ roBytes3) ∗ P))
    (hro4 : ∀ {m : Memory} (_ : img.RoDataLoaded m) {P : SepProp},
      (m ⊨ P) → (m ⊨ (roAddr4 ↦ᵣ roBytes4) ∗ P)) (h : subroutine_ok prog entry { spec with
        pre := fun x s => ⌜FrozenRo img s.mem⌝ ∗ (roAddr1 ↦ᵣ roBytes1) ∗ (roAddr2 ↦ᵣ roBytes2) ∗
        (roAddr3 ↦ᵣ roBytes3) ∗ (roAddr4 ↦ᵣ roBytes4) ∗ spec.pre x s
        post := fun x s0 sf =>
        (roAddr1 ↦ᵣ roBytes1) ∗ (roAddr2 ↦ᵣ roBytes2) ∗ (roAddr3 ↦ᵣ roBytes3) ∗
        (roAddr4 ↦ᵣ roBytes4) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hL, hpre⟩
  have hpre' : s0.mem ⊨ (⌜FrozenRo img s0.mem⌝ ∗ (roAddr1 ↦ᵣ roBytes1) ∗ (roAddr2 ↦ᵣ roBytes2) ∗
    (roAddr3 ↦ᵣ roBytes3) ∗ (roAddr4 ↦ᵣ roBytes4) ∗ spec.pre x s0) ∗ R := by
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hL.1.roData⟩, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    exact hro1 hL.1.roData (hro2 hL.1.roData (hro3 hL.1.roData (hro4 hL.1.roData hpre)))
  refine h.mono_outcome x R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩; dsimp only at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc] at hq
    exact Satisfies.of_sep_right (Satisfies.of_sep_right (Satisfies.of_sep_right
      (Satisfies.of_sep_right hq)))
  · exact Or.inr hrest
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
theorem acceptKeys_eq_none_of_dh3_zero (P : Primitives) (inp : AcceptKeysInput) (htrust :
    inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = true)
    (hdh1 : P.x25519 inp.spkBSk inp.hdr.ikAPk ≠ List.replicate 32 0)
    (hdh2 : P.x25519 inp.ikBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hdh3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0) :
    Model.acceptKeys P inp = none := by
  have hdh1_bne : (P.x25519 inp.spkBSk inp.hdr.ikAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh1
  have hdh2_bne : (P.x25519 inp.ikBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh2
  simp only [Model.acceptKeys, htrust, hreplay, hik, hek, hcanon, hdh1_bne, hdh2_bne, hdh3,
    beq_self_eq_true, bne_self_eq_false, Bool.false_eq_true, «guard», bind, pure, ↓reduceIte]; rfl
theorem acceptKeys_eq_none_of_dh4_zero (P : Primitives) (inp : AcceptKeysInput) (opkSk : Bytes)
    (htrust : inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = true)
    (hdh1 : P.x25519 inp.spkBSk inp.hdr.ikAPk ≠ List.replicate 32 0)
    (hdh2 : P.x25519 inp.ikBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hdh3 : P.x25519 inp.spkBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hopk_eq : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome) (hopk : inp.opkBSk? = some opkSk)
    (hdh4 : P.x25519 opkSk inp.hdr.ekAPk = List.replicate 32 0) :
    Model.acceptKeys P inp = none := by
  obtain ⟨opkId, hopkId⟩ : ∃ id, inp.hdr.opkId? = some id := by
    cases h : inp.hdr.opkId? with
    | none => simp [h, hopk] at hopk_eq | some id => exact ⟨id, rfl⟩
  have hdh1_bne : (P.x25519 inp.spkBSk inp.hdr.ikAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh1
  have hdh2_bne : (P.x25519 inp.ikBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh2
  have hdh3_bne : (P.x25519 inp.spkBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh3
  simp only [Model.acceptKeys, dhOptNonZero, htrust, hreplay, hik, hek, hcanon, hdh1_bne, hdh2_bne,
    hdh3_bne, hopk, hopkId, hdh4, beq_self_eq_true, «guard», bind, pure, ↓reduceIte]; rfl
theorem cells3_sub4912_to_memRegion24 (sp w0 w1 w2 : BitVec 64) : ((sp - 4912#64) ↦₆₄ w0) ∗ ((sp -
    4904#64) ↦₆₄ w1) ∗ ((sp - 4896#64) ↦₆₄ w2) ⊢ memRegion (sp - 4912#64) 24 := by
  have hc3 := cells_3_merge (sp - 4912#64) w0 w1 w2
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hc3
  rw [← (memRegion_cells (sp - 4912#64) 3 (by decide) : memRegion (sp - 4912#64) 24 = cells (sp -
    4912#64) 3)] at hc3; exact hc3
theorem alloc_to_calc_stack (sp : BitVec 64) : memRegion (sp - 9440#64) 400 ∗ stackAt (sp -
    4944#64) allocHookStack = memRegion (sp - 9440#64) 240 ∗ stackAt (sp -
      4944#64) calculateAgreementStack := (subStack_to_alloc sp).symm.trans (subStack_to_calc sp)
theorem calc_to_alloc_stack (sp : BitVec 64) : memRegion (sp - 9440#64) 240 ∗ stackAt (sp -
    4944#64) calculateAgreementStack = memRegion (sp - 9440#64) 400 ∗ stackAt (sp -
      4944#64) allocHookStack := (subStack_to_calc sp).symm.trans (subStack_to_alloc sp)
theorem vec_err_dh1_merge (a : BitVec 64) : (a ↦ₛ bytesToBv8 F_X25519) ∗ memRegion (a + 32#64) 32 ∗
    memRegion (a + 64#64) 32 ∗ memRegion (a + 96#64) 32 ∗ memRegion (a + 128#64) 32 ∗ memRegion (a +
      160#64) 32 ⊢ memRegion a 192 := by
  have h32 : (bytesToBv8 F_X25519).length = 32 := by decide
  refine Entails.trans (sepConj_mono_left (h32 ▸
    pointsToBytes_entails_memRegion a (bytesToBv8 F_X25519))) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 32) (k := 160) (b' :=
    a + 32#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := a + 32#64) (n :=
    32) (k := 128) (b' := a + 64#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      a + 64#64) (n := 32) (k := 96) (b' :=
        a + 96#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := a + 96#64) (n :=
        32) (k := 64) (b' := a + 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 128#64) (n := 32) (k := 32) (b' :=
        a + 160#64) rfl (by bv_omega) (by decide)]; exact Entails.refl _
theorem vec_err_dh2_merge (a : BitVec 64) {bs : Bytes} (hbs : bs.length = 64) :
    (a ↦ₛ bytesToBv8 bs) ∗ memRegion (a + 64#64) 32 ∗ memRegion (a + 96#64) 32 ∗ memRegion (a +
      128#64) 32 ∗ memRegion (a + 160#64) 32 ⊢ memRegion a 192 := by
  have h64 : (bytesToBv8 bs).length = 64 := by simp [bytesToBv8, hbs]
  refine Entails.trans (sepConj_mono_left (h64 ▸
    pointsToBytes_entails_memRegion a (bytesToBv8 bs))) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 64) (k := 128) (b' :=
    a + 64#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := a + 64#64) (n :=
    32) (k := 96) (b' := a + 96#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      a + 96#64) (n := 32) (k := 64) (b' :=
        a + 128#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := a + 128#64) (n :=
        32) (k := 32) (b' := a + 160#64) rfl (by bv_omega) (by decide)]; exact Entails.refl _
theorem vec_err_dh3_merge (a : BitVec 64) {bs : Bytes} (hbs : bs.length = 96) :
    (a ↦ₛ bytesToBv8 bs) ∗ memRegion (a + 96#64) 32 ∗ memRegion (a + 128#64) 32 ∗ memRegion (a +
      160#64) 32 ⊢ memRegion a 192 := by
  have h96 : (bytesToBv8 bs).length = 96 := by simp [bytesToBv8, hbs]
  refine Entails.trans (sepConj_mono_left (h96 ▸
    pointsToBytes_entails_memRegion a (bytesToBv8 bs))) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 96) (k := 96) (b' :=
    a + 96#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := a + 96#64) (n :=
    32) (k := 64) (b' := a + 128#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      a + 128#64) (n := 32) (k := 32) (b' := a + 160#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _
theorem vec_err_dh4_merge (a : BitVec 64) {bs : Bytes} (hbs : bs.length = 128) :
    (a ↦ₛ bytesToBv8 bs) ∗ memRegion (a + 128#64) 32 ∗ memRegion (a + 160#64) 32 ⊢
      memRegion a 192 := by
  have h128 : (bytesToBv8 bs).length = 128 := by simp [bytesToBv8, hbs]
  refine Entails.trans (sepConj_mono_left (h128 ▸
    pointsToBytes_entails_memRegion a (bytesToBv8 bs))) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 128) (k := 64) (b' :=
    a + 128#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := a + 128#64) (n :=
    32) (k := 32) (b' := a + 160#64) rfl (by bv_omega) (by decide)]; exact Entails.refl _
theorem calcErr_entails_at_sub4912 (sp : BitVec 64) : ((sp - 4912#64) ↦₆₄ 1#64) ∗ (∃∗
    hi : BitVec 56, (sp - 4904#64) ↦₆₄ (hi ++ 3#8)) ∗ (∃∗ u2 : BitVec 64, (sp - 4896#64) ↦₆₄ u2) ⊢
      ∃∗ u2 : BitVec 64, ∃∗ hi : BitVec 56, ((sp - 4912#64) ↦₆₄ 1#64) ∗ ((sp - 4904#64) ↦₆₄ (hi ++
        3#8)) ∗ ((sp - 4896#64) ↦₆₄ u2) := by
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; exact Entails.refl _
theorem boxSliceU8_32_entails_at_sub4912 (A : RustAlloc) (sp : BitVec 64) {bs : List (BitVec 8)}
    (hbs : bs.length = 32) : ((sp - 4912#64) ↦₆₄ 0#64) ∗ boxSliceU8 A (sp - 4904#64) bs ⊢ ∃∗
      dh_ptr : BitVec 64, ((sp - 4912#64) ↦₆₄ 0#64) ∗ ((sp - 4904#64) ↦₆₄ dh_ptr) ∗ ((sp -
        4896#64) ↦₆₄ 32#64) ∗ (dh_ptr ↦ₛ bs) ∗ A.live dh_ptr 32 1 := by
  refine Entails.trans (sepConj_mono_right (boxSliceU8_32_entails A (sp - 4904#64) bs hbs)) ?_
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun dh_ptr => Entails.sepExists_right dh_ptr ?_
  simp only [bv_sub_add_lit', BitVec.reduceSub]; exact Entails.of_eq (by ac_rfl)
theorem calc_to_vecAppend_stack (sp : BitVec 64) : memRegion (sp - 9440#64) 240 ∗ stackAt (sp -
    4944#64) calculateAgreementStack = memRegion (sp - 9440#64) 4448 ∗ cells (sp - 4992#64) 6 :=
  (subStack_to_calc sp).symm.trans (subStack_to_vecAppend sp)
theorem vecAppend_to_alloc_stack (sp : BitVec 64) : memRegion (sp - 9440#64) 4448 ∗ cells (sp -
    4992#64) 6 = memRegion (sp - 9440#64) 400 ∗ stackAt (sp - 4944#64) allocHookStack :=
  (subStack_to_vecAppend sp).symm.trans (subStack_to_alloc sp)
theorem vec_ok_160_merge (a : BitVec 64) {bs : Bytes} (hbs : bs.length = 160) :
    (a ↦ₛ bytesToBv8 bs) ∗ memRegion (a + 160#64) 32 ⊢ memRegion a 192 := by
  have h160 : (bytesToBv8 bs).length = 160 := by simp [bytesToBv8, hbs]
  refine Entails.trans (sepConj_mono_left (h160 ▸
    pointsToBytes_entails_memRegion a (bytesToBv8 bs))) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 160) (k := 32) (b' :=
    a + 160#64) rfl (by bv_omega) (by decide)]; exact Entails.refl _
theorem vec_ok_192_merge (a : BitVec 64) {bs : Bytes} (hbs : bs.length = 192) :
    (a ↦ₛ bytesToBv8 bs) ⊢ memRegion a 192 := by
  have h192 : (bytesToBv8 bs).length = 192 := by simp [bytesToBv8, hbs]
  exact h192 ▸ pointsToBytes_entails_memRegion a (bytesToBv8 bs)
theorem pqsk_head_tail_merge (sp : BitVec 64) {sk : Bytes} (h : sk.length = 3168) : ((sp -
    4912#64) ↦₈ (bytesToBv8 sk).getD 0 0#8) ∗ ((sp - 4911#64) ↦ₛ (bytesToBv8 sk).drop 1) ⊢
      ((sp - 4912#64) ↦ₛ bytesToBv8 sk) := by
  have h1 : sp - 4912#64 + 1#64 = sp - 4911#64 := by bv_omega
  rw [← h1, ← bytesToBv8_head_tail (sp - 4912#64) (bytesToBv8 sk) (by simp [bytesToBv8, h])]
  exact Entails.refl _
theorem kemct_head_tail_merge (sp : BitVec 64) {ct : Bytes} (h : ct.length = 1568) : ((sp -
    1744#64) ↦₈ (bytesToBv8 ct).getD 0 0#8) ∗ ((sp - 1743#64) ↦ₛ (bytesToBv8 ct).drop 1) ⊢
      ((sp - 1744#64) ↦ₛ bytesToBv8 ct) := by
  have h1 : sp - 1744#64 + 1#64 = sp - 1743#64 := by bv_omega
  rw [← h1, ← bytesToBv8_head_tail (sp - 1744#64) (bytesToBv8 ct) (by simp [bytesToBv8, h])]
  exact Entails.refl _
theorem sub176_split_32_64 (sp : BitVec 64) : memRegion (sp - 176#64) 96 = memRegion (sp -
      176#64) 32 ∗ (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗
        u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64, ((sp -
        144#64) ↦₆₄ u0) ∗ ((sp - 136#64) ↦₆₄ u1) ∗ ((sp - 128#64) ↦₆₄ u2) ∗ ((sp - 120#64) ↦₆₄ u3) ∗
        ((sp - 112#64) ↦₆₄ u4) ∗ ((sp - 104#64) ↦₆₄ u5) ∗ ((sp - 96#64) ↦₆₄ u6) ∗
        ((sp - 88#64) ↦₆₄ u7)) := by
  rw [ProofLib.memRegion_split' (b := sp - 176#64) (n := 32) (k := 64) (b' :=
        sp - 144#64) rfl (by bv_omega) (by decide), (memRegion_cells (sp - 144#64) 8 (by decide) :
        memRegion (sp - 144#64) 64 = cells (sp - 144#64) 8)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
theorem pqsk_to_extract_region (sp : BitVec 64) {sk : Bytes} (h : sk.length = 3168) : ((sp -
    4912#64) ↦ₛ bytesToBv8 sk) ⊢ memRegion (sp - 4912#64) 176 ∗ memRegion (sp - 4736#64) 2992 := by
  have hlen : (bytesToBv8 sk).length = 3168 := by simp [bytesToBv8, h]
  refine Entails.trans (hlen ▸ pointsToBytes_entails_memRegion (sp - 4912#64) (bytesToBv8 sk)) ?_
  rw [ProofLib.memRegion_split' (b := sp - 4912#64) (n := 176) (k := 2992) (b' :=
        sp - 4736#64) rfl (by bv_omega) (by decide)]; exact Entails.refl _
theorem kemct_to_hmac18_region (sp : BitVec 64) {ct : Bytes} (h : ct.length = 1568) : ((sp -
    1744#64) ↦ₛ bytesToBv8 ct) ⊢ (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗
      u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗
        u8 : BitVec 64, ∃∗ u9 : BitVec 64, ∃∗ u10 : BitVec 64, ∃∗ u11 : BitVec 64, ∃∗
       u12 : BitVec 64, ∃∗ u13 : BitVec 64, ∃∗ u14 : BitVec 64, ∃∗ u15 : BitVec 64, ∃∗
       u16 : BitVec 64, ∃∗ u17 : BitVec 64, ((sp - 1744#64) ↦₆₄ u0) ∗ ((sp - 1736#64) ↦₆₄ u1) ∗
       ((sp - 1728#64) ↦₆₄ u2) ∗ ((sp - 1720#64) ↦₆₄ u3) ∗ ((sp - 1712#64) ↦₆₄ u4) ∗ ((sp -
       1704#64) ↦₆₄ u5) ∗ ((sp - 1696#64) ↦₆₄ u6) ∗ ((sp - 1688#64) ↦₆₄ u7) ∗ ((sp -
       1680#64) ↦₆₄ u8) ∗ ((sp - 1672#64) ↦₆₄ u9) ∗ ((sp - 1664#64) ↦₆₄ u10) ∗ ((sp -
        1656#64) ↦₆₄ u11) ∗ ((sp - 1648#64) ↦₆₄ u12) ∗ ((sp - 1640#64) ↦₆₄ u13) ∗ ((sp -
        1632#64) ↦₆₄ u14) ∗ ((sp - 1624#64) ↦₆₄ u15) ∗ ((sp - 1616#64) ↦₆₄ u16) ∗ ((sp -
        1608#64) ↦₆₄ u17)) ∗ memRegion (sp - 1600#64) 1424 := by
  have hlen : (bytesToBv8 ct).length = 1568 := by simp [bytesToBv8, h]
  refine Entails.trans (hlen ▸ pointsToBytes_entails_memRegion (sp - 1744#64) (bytesToBv8 ct)) ?_
  rw [ProofLib.memRegion_split' (b := sp - 1744#64) (n := 144) (k := 1424) (b' :=
        sp - 1600#64) rfl (by bv_omega) (by decide), (memRegion_cells (sp - 1744#64) 18
        (by decide) : memRegion (sp - 1744#64) 144 = cells (sp - 1744#64) 18)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
  exact Entails.refl _
theorem sub1680_split_32_48 (sp : BitVec 64) : memRegion (sp - 1680#64) 80 = (∃∗ u0 : BitVec 64, ∃∗
      u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ((sp - 1680#64) ↦₆₄ u0) ∗ ((sp -
        1672#64) ↦₆₄ u1) ∗ ((sp - 1664#64) ↦₆₄ u2) ∗ ((sp -
        1656#64) ↦₆₄ u3)) ∗ memRegion (sp - 1648#64) 48 := by
  rw [ProofLib.memRegion_split' (b := sp - 1680#64) (n := 32) (k := 48) (b' :=
        sp - 1648#64) rfl (by bv_omega) (by decide), (memRegion_cells (sp - 1680#64) 4 (by decide) :
        memRegion (sp - 1680#64) 32 = cells (sp - 1680#64) 4)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
theorem sub4912_post_kdf_merge (sp : BitVec 64) (p0 p1 p2 p3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
    w12 w13 w14 w15 w16 w17 : BitVec 64) : ((sp - 4912#64) ↦₆₄ p0) ∗ ((sp - 4904#64) ↦₆₄ p1) ∗
    ((sp - 4896#64) ↦₆₄ p2) ∗ ((sp - 4888#64) ↦₆₄ p3) ∗ ((sp - 4880#64) ↦₆₄ w0) ∗ ((sp -
      4872#64) ↦₆₄ w1) ∗ ((sp - 4864#64) ↦₆₄ w2) ∗ ((sp - 4856#64) ↦₆₄ w3) ∗ ((sp -
      4848#64) ↦₆₄ w4) ∗ ((sp - 4840#64) ↦₆₄ w5) ∗ ((sp - 4832#64) ↦₆₄ w6) ∗ ((sp -
      4824#64) ↦₆₄ w7) ∗ ((sp - 4816#64) ↦₆₄ w8) ∗ ((sp - 4808#64) ↦₆₄ w9) ∗ ((sp -
        4800#64) ↦₆₄ w10) ∗ ((sp - 4792#64) ↦₆₄ w11) ∗ ((sp - 4784#64) ↦₆₄ w12) ∗ ((sp -
        4776#64) ↦₆₄ w13) ∗ ((sp - 4768#64) ↦₆₄ w14) ∗ ((sp - 4760#64) ↦₆₄ w15) ∗ ((sp -
        4752#64) ↦₆₄ w16) ∗ ((sp - 4744#64) ↦₆₄ w17) ∗ memRegion (sp - 4736#64) 2992 ⊢
      memRegion (sp - 4912#64) 3168 := by
  have hc4 := cells_4_merge (sp - 4912#64) p0 p1 p2 p3
  have hc8 := cells_8_merge (sp - 4880#64) w0 w1 w2 w3 w4 w5 w6 w7
  have hc10 := cells_10_merge (sp - 4816#64) w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hc4 hc8 hc10
  rw [← (memRegion_cells (sp - 4912#64) 4 (by decide) : memRegion (sp - 4912#64) 32 = cells (sp -
    4912#64) 4)] at hc4
  rw [← (memRegion_cells (sp - 4880#64) 8 (by decide) : memRegion (sp - 4880#64) 64 = cells (sp -
    4880#64) 8)] at hc8
  rw [← (memRegion_cells (sp - 4816#64) 10 (by decide) : memRegion (sp - 4816#64) 80 = cells (sp -
    4816#64) 10)] at hc10
  rw [ProofLib.memRegion_split' (b := sp - 4912#64) (n := 32) (k := 3136) (b' :=
    sp - 4880#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := sp - 4880#64) (n :=
    64) (k := 3072) (b' := sp - 4816#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 4816#64) (n := 80) (k := 2992) (b' :=
        sp - 4736#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans ?_ (sepConj_mono_left hc4)
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left hc8))
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hc10)))
  exact Entails.of_eq (by ac_rfl)
theorem sub1744_post_kdf_merge (sp : BitVec 64) (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 : BitVec 64)
    : ((sp - 1744#64) ↦₆₄ u0) ∗ ((sp - 1736#64) ↦₆₄ u1) ∗ ((sp - 1728#64) ↦₆₄ u2) ∗ ((sp -
      1720#64) ↦₆₄ u3) ∗ ((sp - 1712#64) ↦₆₄ u4) ∗ ((sp - 1704#64) ↦₆₄ u5) ∗ ((sp -
      1696#64) ↦₆₄ u6) ∗ ((sp - 1688#64) ↦₆₄ u7) ∗ ((sp - 1680#64) ↦₆₄ u8) ∗ ((sp -
      1672#64) ↦₆₄ u9) ∗ ((sp - 1664#64) ↦₆₄ u10) ∗ ((sp - 1656#64) ↦₆₄ u11) ∗ memRegion (sp -
        1648#64) 48 ∗ memRegion (sp - 1600#64) 1424 ⊢ memRegion (sp - 1744#64) 1568 := by
  have hc12 := cells_12_merge (sp - 1744#64) u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hc12
  rw [← (memRegion_cells (sp - 1744#64) 12 (by decide) : memRegion (sp - 1744#64) 96 = cells (sp -
    1744#64) 12)] at hc12
  rw [ProofLib.memRegion_split' (b := sp - 1744#64) (n := 96) (k := 1472) (b' :=
    sp - 1648#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := sp - 1648#64) (n :=
    48) (k := 1424) (b' := sp - 1600#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans ?_ (sepConj_mono_left hc12); exact Entails.of_eq (by ac_rfl)
theorem sub176_post_kdf_merge (sp : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) :
    ((sp - 176#64) ↦₆₄ w0) ∗ ((sp - 168#64) ↦₆₄ w1) ∗ ((sp - 160#64) ↦₆₄ w2) ∗ ((sp -
      152#64) ↦₆₄ w3) ∗ ((sp - 144#64) ↦₆₄ w4) ∗ ((sp - 136#64) ↦₆₄ w5) ∗ ((sp - 128#64) ↦₆₄ w6) ∗
      ((sp - 120#64) ↦₆₄ w7) ∗ ((sp - 112#64) ↦₆₄ w8) ∗ ((sp - 104#64) ↦₆₄ w9) ∗ ((sp -
      96#64) ↦₆₄ w10) ∗ ((sp - 88#64) ↦₆₄ w11) ⊢ memRegion (sp - 176#64) 96 := by
  have hc12 := cells_12_merge (sp - 176#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hc12
  rw [← (memRegion_cells (sp - 176#64) 12 (by decide) : memRegion (sp - 176#64) 96 = cells (sp -
    176#64) 12)] at hc12; exact hc12
theorem kyberDecaps_some_and_fitBv8_eq {P : Primitives} (hWF : StructuralPrims P) {sk ct : Bytes}
    (hsk : sk.length = 3168) (hct : ct.length = 1568) : ∃ ss : Bytes, P.kemDecaps sk ct = some ss ∧
    ss.length = 32 ∧ fitBv8 32 (kyberDecapsOutBytes P sk ct) = bytesToBv8 ss := by
  have his := hWF.kemDecaps_isSome sk ct hsk hct
  cases h : P.kemDecaps sk ct with
  | none => simp [h] at his
  | some ss =>
    have hlen := hWF.kemDecaps_len sk ct ss h
    exact ⟨ss, rfl, hlen, fitBv8_kyberDecapsOutBytes_eq h hlen⟩
theorem allowPanic_hag {P : Primitives} {A : RustAlloc} {img : Obj.Image} {s0 s : State} {F R :
    SepProp} {x : BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64} (htr : s.trace =
    s0.trace) : ∀ sf, sf.status = .Panicked → (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))
        sf ((pqxdhCalculateAgreementSpec P A img).onPanic x s sf ∗ F) := by
  intro sf _ hm; dsimp only [pqxdhCalculateAgreementSpec, rustPanicOnOom] at hm
  exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm
theorem outPtr_ok104_cells_split (outPtr : BitVec 64) : memRegion outPtr 104 = (∃∗ v0 : BitVec 32,
      outPtr ↦₃₂ v0) ∗ (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
        ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗
       c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64, ((outPtr +
       4#64) ↦₆₄ c0) ∗ ((outPtr + 12#64) ↦₆₄ c1) ∗ ((outPtr + 20#64) ↦₆₄ c2) ∗ ((outPtr +
       28#64) ↦₆₄ c3) ∗ ((outPtr + 36#64) ↦₆₄ c4) ∗ ((outPtr + 44#64) ↦₆₄ c5) ∗ ((outPtr +
       52#64) ↦₆₄ c6) ∗ ((outPtr + 60#64) ↦₆₄ c7) ∗ ((outPtr + 68#64) ↦₆₄ c8) ∗ ((outPtr +
        76#64) ↦₆₄ c9) ∗ ((outPtr + 84#64) ↦₆₄ c10) ∗ ((outPtr + 92#64) ↦₆₄ c11)) ∗ (∃∗
        v100 : BitVec 32, (outPtr + 100#64) ↦₃₂ v100) := by
  rw [outPtr_ok104_split outPtr]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
theorem outPtr_ok104_cells_merge {P : Primitives} {secrets : Bytes} (outPtr : BitVec 64) {w0 w1 w2
    w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64} (hout : ∀ a : BitVec 64,
      (a ↦ₛ bytesToBv8 (handshakeKeysBytes100 (Model.deriveDRKeys P secrets))) = (a ↦₆₄ w0) ∗ ((a +
        8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w8) ∗ ((a +
        40#64) ↦₆₄ w9) ∗ ((a + 48#64) ↦₆₄ w10) ∗ ((a + 56#64) ↦₆₄ w11) ∗ ((a + 64#64) ↦₆₄ w4) ∗
        ((a + 72#64) ↦₆₄ w5) ∗ ((a + 80#64) ↦₆₄ w6) ∗ ((a + 88#64) ↦₆₄ w7) ∗ ((a +
        96#64) ↦₃₂ 0#32)) : (outPtr ↦₃₂ 0#32) ∗ ((outPtr + 4#64) ↦₆₄ w0) ∗ ((outPtr +
    12#64) ↦₆₄ w1) ∗ ((outPtr + 20#64) ↦₆₄ w2) ∗ ((outPtr + 28#64) ↦₆₄ w3) ∗ ((outPtr +
      36#64) ↦₆₄ w8) ∗ ((outPtr + 44#64) ↦₆₄ w9) ∗ ((outPtr + 52#64) ↦₆₄ w10) ∗ ((outPtr +
      60#64) ↦₆₄ w11) ∗ ((outPtr + 68#64) ↦₆₄ w4) ∗ ((outPtr + 76#64) ↦₆₄ w5) ∗ ((outPtr +
      84#64) ↦₆₄ w6) ∗ ((outPtr + 92#64) ↦₆₄ w7) ∗ ((outPtr + 100#64) ↦₃₂ 0#32) ⊢
      (outPtr ↦ₛ bytesToBv8 (handshakeKeysResultOk104 (Model.deriveDRKeys P secrets))) := by
  have h := hout (outPtr + 4#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [← outPtr_ok104_eq outPtr (Model.deriveDRKeys P secrets), h]; exact Entails.of_eq (by ac_rfl)
theorem ss_sub176_eq (sp : BitVec 64) {ss : Bytes} {s0_w s1_w s2_w s3_w : BitVec 64} (hss_cells : ∀
    a : BitVec 64, (a ↦ₛ bytesToBv8 ss) = (a ↦₆₄ s0_w) ∗ ((a + 8#64) ↦₆₄ s1_w) ∗ ((a +
        16#64) ↦₆₄ s2_w) ∗ ((a + 24#64) ↦₆₄ s3_w)) : ((sp - 176#64) ↦ₛ bytesToBv8 ss) = ((sp -
      176#64) ↦₆₄ s0_w) ∗ ((sp - 168#64) ↦₆₄ s1_w) ∗ ((sp - 160#64) ↦₆₄ s2_w) ∗ ((sp -
        152#64) ↦₆₄ s3_w) := by
  have h := hss_cells (sp - 176#64); simp only [bv_sub_add_lit', BitVec.reduceSub] at h; exact h
theorem ss_vec_add128_merge (vec_ptr : BitVec 64) {ss : Bytes} {s0_w s1_w s2_w s3_w : BitVec 64}
    (hss_cells : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 ss) = (a ↦₆₄ s0_w) ∗ ((a + 8#64) ↦₆₄ s1_w) ∗
        ((a + 16#64) ↦₆₄ s2_w) ∗ ((a + 24#64) ↦₆₄ s3_w)) : ((vec_ptr + 128#64) ↦₆₄ s0_w) ∗
    ((vec_ptr + 136#64) ↦₆₄ s1_w) ∗ ((vec_ptr + 144#64) ↦₆₄ s2_w) ∗ ((vec_ptr + 152#64) ↦₆₄ s3_w) ⊢
      ((vec_ptr + 128#64) ↦ₛ bytesToBv8 ss) := by
  have h := hss_cells (vec_ptr + 128#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [h]; exact Entails.refl _
theorem ss_vec_add160_merge (vec_ptr : BitVec 64) {ss : Bytes} {s0_w s1_w s2_w s3_w : BitVec 64}
    (hss_cells : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 ss) = (a ↦₆₄ s0_w) ∗ ((a + 8#64) ↦₆₄ s1_w) ∗
        ((a + 16#64) ↦₆₄ s2_w) ∗ ((a + 24#64) ↦₆₄ s3_w)) : ((vec_ptr + 160#64) ↦₆₄ s0_w) ∗
    ((vec_ptr + 168#64) ↦₆₄ s1_w) ∗ ((vec_ptr + 176#64) ↦₆₄ s2_w) ∗ ((vec_ptr + 184#64) ↦₆₄ s3_w) ⊢
      ((vec_ptr + 160#64) ↦ₛ bytesToBv8 ss) := by
  have h := hss_cells (vec_ptr + 160#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [h]; exact Entails.refl _
theorem prk_sub4912_eq (sp : BitVec 64) {prk : Bytes} {p0 p1 p2 p3 : BitVec 64} (hprk : ∀ a : BitVec
    64, (a ↦ₛ bytesToBv8 prk) = (a ↦₆₄ p0) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ p2) ∗ ((a +
        24#64) ↦₆₄ p3)) : ((sp - 4912#64) ↦ₛ bytesToBv8 prk) ⊢ ((sp - 4912#64) ↦₆₄ p0) ∗ ((sp -
      4904#64) ↦₆₄ p1) ∗ ((sp - 4896#64) ↦₆₄ p2) ∗ ((sp - 4888#64) ↦₆₄ p3) := by
  have h := hprk (sp - 4912#64); simp only [bv_sub_add_lit', BitVec.reduceSub] at h
  rw [h]; exact Entails.refl _
theorem okm_sub176_eq (sp : BitVec 64) {okm : Bytes} {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec
    64} (hokm : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 okm) = (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a +
        16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a +
        48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗
        ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11)) : ((sp - 176#64) ↦ₛ bytesToBv8 okm) ⊢
      ((sp - 176#64) ↦₆₄ w0) ∗ ((sp - 168#64) ↦₆₄ w1) ∗ ((sp - 160#64) ↦₆₄ w2) ∗ ((sp -
        152#64) ↦₆₄ w3) ∗ ((sp - 144#64) ↦₆₄ w4) ∗ ((sp - 136#64) ↦₆₄ w5) ∗ ((sp - 128#64) ↦₆₄ w6) ∗
        ((sp - 120#64) ↦₆₄ w7) ∗ ((sp - 112#64) ↦₆₄ w8) ∗
      ((sp - 104#64) ↦₆₄ w9) ∗ ((sp - 96#64) ↦₆₄ w10) ∗ ((sp - 88#64) ↦₆₄ w11) := by
  have h := hokm (sp - 176#64); simp only [bv_sub_add_lit', BitVec.reduceSub] at h
  rw [h]; exact Entails.refl _
theorem cells4_to_memRegion32 (a v0 v1 v2 v3 : BitVec 64) : (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a +
    16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢ memRegion a 32 := by
  rw [(memRegion_cells a 4 (by decide) : memRegion a 32 = cells a 4)]
  exact cells_4_merge a v0 v1 v2 v3
theorem hmacCore_split_sub4880 (P : Primitives) (sp : BitVec 64) (prk : Bytes) : pqxdhHmacStateAt P
    (sp - 4880#64) prk ⊢ ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
        ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗
      w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗
        w17 : BitVec 64,
        ⌜PqxdhHmacGood P prk w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17⌝ ∗ ((sp -
        4880#64) ↦₆₄ w0) ∗ ((sp - 4872#64) ↦₆₄ w1) ∗ ((sp - 4864#64) ↦₆₄ w2) ∗ ((sp -
        4856#64) ↦₆₄ w3) ∗ ((sp - 4848#64) ↦₆₄ w4) ∗ ((sp - 4840#64) ↦₆₄ w5) ∗ ((sp -
        4832#64) ↦₆₄ w6) ∗ ((sp - 4824#64) ↦₆₄ w7) ∗ ((sp - 4816#64) ↦₆₄ w8) ∗ ((sp -
        4808#64) ↦₆₄ w9) ∗ ((sp - 4800#64) ↦₆₄ w10) ∗ ((sp - 4792#64) ↦₆₄ w11) ∗ ((sp -
        4784#64) ↦₆₄ w12) ∗ ((sp - 4776#64) ↦₆₄ w13) ∗ ((sp - 4768#64) ↦₆₄ w14) ∗ ((sp -
        4760#64) ↦₆₄ w15) ∗ ((sp - 4752#64) ↦₆₄ w16) ∗ ((sp - 4744#64) ↦₆₄ w17) := by
  have h := hmacCore_split P (sp - 4880#64) prk; simp only [bv_sub_add_lit', BitVec.reduceSub] at h
  exact h
theorem ss_and_vec128_split (ss_ptr vec_ptr : BitVec 64) : memRegion ss_ptr 32 ∗
    memRegion (vec_ptr + 128#64) 32 = (∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗
      d3 : BitVec 64, (ss_ptr ↦₆₄ d0) ∗ ((ss_ptr + 8#64) ↦₆₄ d1) ∗ ((ss_ptr + 16#64) ↦₆₄ d2) ∗
        ((ss_ptr + 24#64) ↦₆₄ d3)) ∗ (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗
        e3 : BitVec 64, ((vec_ptr + 128#64) ↦₆₄ e0) ∗ ((vec_ptr + 136#64) ↦₆₄ e1) ∗ ((vec_ptr +
        144#64) ↦₆₄ e2) ∗ ((vec_ptr + 152#64) ↦₆₄ e3)) := by
  rw [(memRegion_cells ss_ptr 4 (by decide) : memRegion ss_ptr 32 = cells ss_ptr 4),
    cells4_eq ss_ptr, (memRegion_cells (vec_ptr + 128#64) 4 (by decide) : memRegion (vec_ptr +
    128#64) 32 = cells (vec_ptr + 128#64) 4), cells4_eq (vec_ptr + 128#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem ss_and_vec160_split (ss_ptr vec_ptr : BitVec 64) : memRegion ss_ptr 32 ∗
    memRegion (vec_ptr + 160#64) 32 = (∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗
      d3 : BitVec 64, (ss_ptr ↦₆₄ d0) ∗ ((ss_ptr + 8#64) ↦₆₄ d1) ∗ ((ss_ptr + 16#64) ↦₆₄ d2) ∗
        ((ss_ptr + 24#64) ↦₆₄ d3)) ∗ (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗
        e3 : BitVec 64, ((vec_ptr + 160#64) ↦₆₄ e0) ∗ ((vec_ptr + 168#64) ↦₆₄ e1) ∗ ((vec_ptr +
        176#64) ↦₆₄ e2) ∗ ((vec_ptr + 184#64) ↦₆₄ e3)) := by
  rw [(memRegion_cells ss_ptr 4 (by decide) : memRegion ss_ptr 32 = cells ss_ptr 4),
    cells4_eq ss_ptr, (memRegion_cells (vec_ptr + 160#64) 4 (by decide) : memRegion (vec_ptr +
    160#64) 32 = cells (vec_ptr + 160#64) 4), cells4_eq (vec_ptr + 160#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem SepWP.rw_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp} {Q : State →
    SepProp → Prop} (hP : P = P') (h : SepWP prog ret s P' Q) :
    SepWP prog ret s P Q := hP ▸ h
theorem stack_to_kdf (sp : BitVec 64) : memRegion (sp - 16384#64) 6944 ∗ memRegion (sp -
    9440#64) 400 = memRegion (sp - 16384#64) 3248 ∗ memRegion (sp - 13136#64) 3936 ∗ memRegion (sp -
        9200#64) 160 := by
  rw [← ProofLib.memRegion_split' (b := sp - 16384#64) (n := 6944) (k := 400) (b' :=
        sp - 9440#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 16384#64) (n := 3248) (k := 4096) (b' :=
        sp - 13136#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 13136#64) (n := 3936) (k := 160) (b' := sp - 9200#64) rfl (by bv_omega) (by decide)]
theorem subStack_to_alloc_of_eq (sp sp' : BitVec 64) (h : sp' = sp - 4944#64) : memRegion (sp -
    9440#64) 400 ∗ stackAt sp' allocHookStack ⊢ stackAt (sp - 4944#64) (pqxdhHookStack + 400) := by
  rw [h, ← subStack_to_alloc sp]; exact Entails.refl _
theorem alloc_to_calc_stack_of_eq (sp sp' : BitVec 64) (h : sp' = sp - 4944#64) : memRegion (sp -
    9440#64) 400 ∗ stackAt sp' allocHookStack ⊢
      memRegion (sp - 9440#64) 240 ∗ stackAt (sp - 4944#64) calculateAgreementStack := by
  rw [h, alloc_to_calc_stack sp]; exact Entails.refl _
theorem alloc_to_alloc_stack_of_eq (sp sp' : BitVec 64) (h : sp' = sp - 4944#64) :
    stackAt sp' allocHookStack ⊢ stackAt (sp - 4944#64) allocHookStack := by
  rw [h]; exact Entails.refl _
theorem vecAppend_to_alloc_stack_of_eq (sp sp' : BitVec 64) (h : sp' = sp - 4992#64) :
    memRegion (sp - 9440#64) 4448 ∗ cells sp' 6 ⊢
      memRegion (sp - 9440#64) 400 ∗ stackAt (sp - 4944#64) allocHookStack := by
  rw [h, vecAppend_to_alloc_stack sp]; exact Entails.refl _
theorem SepWPp_call_hag {prog : Program} {ret : BitVec 64} {s : State} {P_pre : SepProp} {Q Qp :
    State → SepProp → Prop} {s0 : State} {F : SepProp} {entry ret_pc : BitVec 64} {P : Primitives}
    {A : RustAlloc} {img : Obj.Image} (hWF : StructuralPrims P) (hag : subroutine_ok prog (entry +
    110016#64) (pqxdhCalculateAgreementSpec P A img)) (hF : FrozenRo img s.mem) (ourA : BitVec 64)
    (our : Bytes) (theirA : BitVec 64) (their : Bytes) (hpc : s.pc = entry +
    110016#64) (hrun : s.status = .Running) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = s0.sp - 4944#64) (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hx : s.readReg64 Reg.x0 = ourA ∧ s.readReg64 Reg.x1 = theirA ∧ s.readReg64 Reg.x8 = s0.sp -
      4912#64 ∧ s.sp = s0.sp - 4944#64 ∧ our.length = 32 ∧ their.length = 32) (hP : P_pre =
    ((ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗ memRegion (s0.sp - 4912#64) 24 ∗
      A.pool ∗ stackAt (s0.sp - 4944#64) calculateAgreementStack ∗ ((img.base +
      bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8)) ∗ F) (hpanic : ∀ sf, sf.status = .Panicked →
      Qp sf ((pqxdhCalculateAgreementSpec P A img).onPanic (ourA, our, theirA, their, s0.sp -
        4912#64, s0.sp - 4944#64) s sf ∗ F)) (herr : P.x25519 our their = List.replicate 32 0 →
      ∀ (sf : State) (hi : BitVec 56) (u2 : BitVec 64), sf.pc = ret_pc → sf.status =
        .Running → sf.sp = s0.sp - 4944#64 → CalleeSavedPreserved s sf → sf.trace = s0.trace →
        SepWPp prog ret sf (((s0.sp - 4912#64) ↦₆₄ 1#64) ∗ ((s0.sp - 4904#64) ↦₆₄ (hi ++ 3#8)) ∗
          ((s0.sp - 4896#64) ↦₆₄ u2) ∗ (ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗
          A.pool ∗ stackAt (s0.sp - 4944#64) calculateAgreementStack ∗ ((img.base +
          bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗ F) Q Qp) (hok : P.x25519 our their ≠
    List.replicate 32 0 → ∀ (sf : State) (dh_ptr : BitVec 64), sf.pc = ret_pc → sf.status =
      .Running → sf.sp = s0.sp - 4944#64 → CalleeSavedPreserved s sf → sf.trace =
        s0.trace → FrozenRo img sf.mem → SepWPp prog ret sf (((s0.sp - 4912#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 4904#64) ↦₆₄ dh_ptr) ∗ ((s0.sp - 4896#64) ↦₆₄ 32#64) ∗
          (dh_ptr ↦ₛ bytesToBv8 (P.x25519 our their)) ∗ A.live dh_ptr 32 1 ∗
          (ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗ A.pool ∗ stackAt (s0.sp -
          4944#64) calculateAgreementStack ∗ ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
          F) Q Qp) : SepWPp prog ret s P_pre Q Qp := by
  refine SepWPp.call_frame_keepsFrozen (x := (ourA, our, theirA, their, s0.sp - 4912#64, s0.sp -
    4944#64))
    hag hpc hrun (spAligned_sub_4944 hsp_align hsp_eq) hlr rfl hx hP
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    hpanic
    (fun sf hpc_f hrun_f hsp_f hcs_f hkf_f => ?_)
  dsimp only [pqxdhCalculateAgreementSpec, pqxdhCalculateAgreementResultAt]
  rw [htr, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_sf => ?_; by_cases hdh : P.x25519 our their = List.replicate 32 0
  · simp only [hdh, ↓reduceIte, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    refine SepWPp.fold (calcErr_entails_at_sub4912 s0.sp) (by sep_focus) ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun u2 => ?_; rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun hi => ?_; simp only [sepConj_assoc]
    exact herr hdh sf hi u2 hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f htr_sf
  · have hdh_bv_len : (bytesToBv8 (P.x25519 our their)).length = 32 := by
      simp [bytesToBv8, hWF.x25519_len our their]
    simp only [hdh, ↓reduceIte, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    refine SepWPp.fold (boxSliceU8_32_entails_at_sub4912 A s0.sp hdh_bv_len) (by sep_focus) ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun dh_ptr => ?_
    simp only [sepConj_assoc]
    exact hok hdh sf dh_ptr hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f htr_sf (hF.of_keepsFrozen hkf_f)
theorem pointsToBytes_append_at_dh3 (p : BitVec 64) (b1 b2 b3 : Bytes) (h : (F_X25519 ++ b1 ++
    b2).length = 96) : (p ↦ₛ bytesToBv8 (F_X25519 ++ (b1 ++ b2))) ∗ ((p + 96#64) ↦ₛ bytesToBv8 b3) =
      (p ↦ₛ bytesToBv8 (F_X25519 ++ b1 ++ b2 ++ b3)) := by
  rw [← List.append_assoc F_X25519 b1 b2]
  exact pointsToBytes_append_at p (F_X25519 ++ b1 ++ b2) b3 96 (by simp only [bytesToBv8,
    List.length_map, h])
attribute [-arm64_norm] List.append_assoc
abbrev pqxdhAcceptErrStrongAt (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₃₂ 1#32) ∗ memRegion (outPtr + 4#64) 4 ∗ (∃∗ w1 : BitVec 64, ⌜w1 ≠ pollReadyOkWord⌝ ∗
    ((outPtr + 8#64) ↦₆₄ w1)) ∗ memRegion (outPtr + 16#64) 88
theorem outPtr_err104_strong_merge (outPtr w1 w2 w3 w4 : BitVec 64) (b40 : BitVec 8) (hw1 : w1 ≠
    pollReadyOkWord) : (outPtr ↦₃₂ 1#32) ∗ memRegion (outPtr + 4#64) 4 ∗ ((outPtr + 8#64) ↦₆₄ w1) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗ ((outPtr +
      40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 ⊢ pqxdhAcceptErrStrongAt outPtr := by
  unfold pqxdhAcceptErrStrongAt; refine sepConj_mono_right (sepConj_mono_right ?_)
  have hw1_ent : ((outPtr + 8#64) ↦₆₄ w1) ⊢
      ∃∗ w1' : BitVec 64, ⌜w1' ≠ pollReadyOkWord⌝ ∗ ((outPtr + 8#64) ↦₆₄ w1') := by
    rw [← pure_sepConj_of_true hw1 ((outPtr + 8#64) ↦₆₄ w1)]
    exact Entails.sepExists_right w1 (Entails.refl _)
  have hc3 : ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ⊢
      memRegion (outPtr + 16#64) 24 := by
    rw [show (24 : Nat) = 8 + (8 + 8) by decide, memRegion_split (outPtr + 16#64) 8 16 (by decide),
      memRegion_split (outPtr + 16#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ w2) (sepConj_mono
      (pointsTo64_entails_memRegion _ w3) (pointsTo64_entails_memRegion _ w4))
  have hb40 : ((outPtr + 40#64) ↦₈ b40) ⊢ memRegion (outPtr + 40#64) 1 := by
    rw [memRegion_one]; exact Entails.sepExists_right b40 (Entails.refl _)
  have hm88 : memRegion (outPtr + 16#64) 24 ∗ (memRegion (outPtr + 40#64) 1 ∗ memRegion (outPtr +
    41#64) 63) = memRegion (outPtr + 16#64) 88 := by
    rw [show outPtr + 41#64 = outPtr + 40#64 + BitVec.ofNat 64 1 by bv_omega, ←
      memRegion_split (outPtr + 40#64) 1 63 (by decide), show outPtr + 40#64 = outPtr + 16#64 +
      BitVec.ofNat 64 24 by bv_omega, ← memRegion_split (outPtr + 16#64) 24 64 (by decide)]
  rw [← hm88]; refine sepConj_mono hw1_ent ?_
  have hswap : ((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
    (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63))) =
      (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4))) ∗
        (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63) := (by ac_rfl); rw [hswap]
  exact sepConj_mono hc3 (sepConj_mono_left hb40)
theorem pqxdhAcceptErrStrongAt_entails (outPtr : BitVec 64) : pqxdhAcceptErrStrongAt outPtr ⊢
      (∃∗ tag : BitVec 8, ⌜tag ≠ 0#8⌝ ∗ (outPtr ↦₈ tag)) ∗ memRegion (outPtr + 1#64) 103 := by
  have h1 := pointsTo32_one_entails_tag_ne_zero outPtr
  have hw1 : (∃∗ w1 : BitVec 64, ⌜w1 ≠ pollReadyOkWord⌝ ∗ ((outPtr + 8#64) ↦₆₄ w1)) ⊢
      memRegion (outPtr + 8#64) 8 := Entails.sepExists_elim fun w1 => Entails.pure_left fun _ =>
      pointsTo64_entails_memRegion (outPtr + 8#64) w1
  have hm103 : memRegion (outPtr + 1#64) 3 ∗ (memRegion (outPtr + 4#64) 4 ∗ (memRegion (outPtr +
    8#64) 8 ∗ memRegion (outPtr + 16#64) 88)) = memRegion (outPtr + 1#64) 103 := by
    rw [show outPtr + 16#64 = outPtr + 8#64 + BitVec.ofNat 64 8 by bv_omega, ←
      memRegion_split (outPtr + 8#64) 8 88 (by decide), show outPtr + 8#64 = outPtr + 4#64 +
      BitVec.ofNat 64 4 by bv_omega, ← memRegion_split (outPtr + 4#64) 4 96 (by decide),
        show outPtr + 4#64 = outPtr + 1#64 + BitVec.ofNat 64 3 by bv_omega, ←
        memRegion_split (outPtr + 1#64) 3 100 (by decide)]
  unfold pqxdhAcceptErrStrongAt; rw [← hm103]; refine Entails.trans (sepConj_mono_left h1) ?_
  rw [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hw1)))
def pqxdhAcceptStrongSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec AcceptKeysCallGhost := Spec.inImage {
    pre := fun g s => ⌜s.readReg64 .x0 = g.argPtr ∧ s.readReg64 .x8 = g.outPtr ∧ g.inp.trustedPeer =
      true ∧ g.inp.replayOk = true ∧ g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
        WellSizedAcceptKeysInput g.inp⌝ ∗
        (g.argPtr ↦ₛ bytesToBv8 (serializeAcceptKeysInputAt g.argPtr g.inp)) ∗
        memRegion g.outPtr 104 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s.sp pqxdhEntryStack ∗
        A.pool
    post := fun g s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗ (g.argPtr ↦ₛ bytesToBv8 (serializeAcceptKeysInputAt g.argPtr g.inp)) ∗
        (match Model.acceptKeys P g.inp with
       | some drKey =>
         g.outPtr ↦ₛ bytesToBv8 (handshakeKeysResultOk104 drKey)
       | none =>
         pqxdhAcceptErrStrongAt g.outPtr ∗ anyHeap) ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
         stackAt s0.sp pqxdhEntryStack ∗ A.pool
    onPanic := rustPanicOnOom img
  } img
theorem subroutine_ok_weaken_post {α : Type} {prog : Program} {entry : BitVec 64} {spec1 spec2 :
    Spec α} (hpre : ∀ x s, spec2.pre x s = spec1.pre x s) (hpost : ∀ x s0 sf,
    spec1.post x s0 sf ⊢ spec2.post x s0 sf) (hpanic : ∀ x s0 sf, spec1.onPanic x s0 sf =
    spec2.onPanic x s0 sf) (hexit : ∀ x code s0 sf, spec1.onExit x code s0 sf =
    spec2.onExit x code s0 sf) (h : subroutine_ok prog entry spec1)
    (hoom : ∀ x s0 sf, spec1.onOom x s0 sf = spec2.onOom x s0 sf := by intros; rfl) :
    subroutine_ok prog entry spec2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hsp => ?_
  rw [hpre] at hpre0
  refine h.mono_outcome x R s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom_st, hq⟩
  · exact Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩); rwa [← hpanic]
  · refine Or.inr (Or.inr (Or.inl ⟨code, hex, ?_⟩)); rwa [← hexit]
  · refine Or.inr (Or.inr (Or.inr ⟨hoom_st, ?_⟩)); rwa [← hoom]
theorem pqxdhAcceptStrongSpec_post_entails (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (g : AcceptKeysCallGhost) (s0 sf : State) : (pqxdhAcceptStrongSpec P A img).post g s0 sf ⊢
      (pqxdhAcceptSpec P A img).post g s0 sf := by
  unfold pqxdhAcceptStrongSpec pqxdhAcceptSpec Spec.inImage; dsimp only
  cases Model.acceptKeys P g.inp
  · refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)); rw [← sepConj_assoc]
    exact sepConj_mono_left (pqxdhAcceptErrStrongAt_entails g.outPtr)
  · exact Entails.refl _
def pqxdhAcceptErrStrong2At (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₃₂ 1#32) ∗ memRegion (outPtr + 4#64) 4 ∗ (∃∗ w1 : BitVec 64, ⌜w1 ≠ pollReadyOkWord ∧ w1 ≠
    0xfffffffffffffffd#64⌝ ∗ ((outPtr + 8#64) ↦₆₄ w1)) ∗ memRegion (outPtr + 16#64) 88
theorem outPtr_err104_strong2_merge (outPtr w1 w2 w3 w4 : BitVec 64) (b40 : BitVec 8) (hw1 : w1 ≠
    pollReadyOkWord ∧ w1 ≠ 0xfffffffffffffffd#64) : (outPtr ↦₃₂ 1#32) ∗ memRegion (outPtr +
    4#64) 4 ∗ ((outPtr + 8#64) ↦₆₄ w1) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr + 24#64) ↦₆₄ w3) ∗
      ((outPtr + 32#64) ↦₆₄ w4) ∗ ((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 ⊢
      pqxdhAcceptErrStrong2At outPtr := by
  unfold pqxdhAcceptErrStrong2At; refine sepConj_mono_right (sepConj_mono_right ?_)
  have hw1_ent : ((outPtr + 8#64) ↦₆₄ w1) ⊢
      ∃∗ w1' : BitVec 64, ⌜w1' ≠ pollReadyOkWord ∧ w1' ≠ 0xfffffffffffffffd#64⌝ ∗ ((outPtr +
        8#64) ↦₆₄ w1') := by
    rw [← pure_sepConj_of_true hw1 ((outPtr + 8#64) ↦₆₄ w1)]
    exact Entails.sepExists_right w1 (Entails.refl _)
  have hc3 : ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ⊢
      memRegion (outPtr + 16#64) 24 := by
    rw [show (24 : Nat) = 8 + (8 + 8) by decide, memRegion_split (outPtr + 16#64) 8 16 (by decide),
      memRegion_split (outPtr + 16#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ w2) (sepConj_mono
      (pointsTo64_entails_memRegion _ w3) (pointsTo64_entails_memRegion _ w4))
  have hb40 : ((outPtr + 40#64) ↦₈ b40) ⊢ memRegion (outPtr + 40#64) 1 := by
    rw [memRegion_one]; exact Entails.sepExists_right b40 (Entails.refl _)
  have hm88 : memRegion (outPtr + 16#64) 24 ∗ (memRegion (outPtr + 40#64) 1 ∗ memRegion (outPtr +
    41#64) 63) = memRegion (outPtr + 16#64) 88 := by
    rw [show outPtr + 41#64 = outPtr + 40#64 + BitVec.ofNat 64 1 by bv_omega, ←
      memRegion_split (outPtr + 40#64) 1 63 (by decide), show outPtr + 40#64 = outPtr + 16#64 +
      BitVec.ofNat 64 24 by bv_omega, ← memRegion_split (outPtr + 16#64) 24 64 (by decide)]
  rw [← hm88]; refine sepConj_mono hw1_ent ?_
  have hswap : ((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
    (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63))) =
      (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4))) ∗
        (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63) := (by ac_rfl); rw [hswap]
  exact sepConj_mono hc3 (sepConj_mono_left hb40)
def pqxdhAcceptFieldsAt (basePtr pqskPtr ctSlicePtr ctBufPtr : BitVec 64) (inp : AcceptKeysInput) :
    SepProp :=
  ((basePtr + 32#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗ ((basePtr + 96#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
    ((basePtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗ ((basePtr +
    160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((basePtr + 208#64) ↦₆₄ pqskPtr) ∗ ((basePtr +
    216#64) ↦₆₄ 3168#64) ∗ ((basePtr + 224#64) ↦₆₄ ctSlicePtr) ∗ ((basePtr +
    232#64) ↦₈ (if (match inp.opkBSk? with
    | some _ => true | none => false) = true then 1#8 else 0#8)) ∗
  ((basePtr + 265#64) ↦ₛ bytesToBv8 (inp.opkBSk?.getD (List.replicate 32 0))) ∗
    (pqskPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗ ((pqskPtr +
    1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗ (ctSlicePtr ↦₆₄ ctBufPtr) ∗ ((ctSlicePtr +
    8#64) ↦₆₄ 1569#64) ∗ (ctBufPtr ↦₈ 8#8) ∗ ((ctBufPtr +
    1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗ ((ctBufPtr +
    2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1)
structure AcceptFieldsCallGhost where
  inp : AcceptKeysInput
  argPtr : BitVec 64
  pqskPtr : BitVec 64
  ctSlicePtr : BitVec 64
  ctBufPtr : BitVec 64
  outPtr : BitVec 64
def pqxdhAcceptFieldsSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec AcceptFieldsCallGhost := Spec.inImage {
    pre := fun (g : AcceptFieldsCallGhost) s =>
      ⌜s.readReg64 .x0 = g.argPtr ∧ s.readReg64 .x8 = g.outPtr ∧ g.inp.trustedPeer = true ∧
        g.inp.replayOk = true ∧ g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
        WellSizedAcceptKeysInput g.inp⌝ ∗
        pqxdhAcceptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
        memRegion g.outPtr 104 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s.sp pqxdhEntryStack ∗
        A.pool
    post := fun (g : AcceptFieldsCallGhost) s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗ pqxdhAcceptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
        (match Model.acceptKeys P g.inp with
       | some drKey =>
         g.outPtr ↦ₛ bytesToBv8 (handshakeKeysResultOk104 drKey)
       | none =>
         pqxdhAcceptErrStrong2At g.outPtr ∗ anyHeap) ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
         stackAt s0.sp pqxdhEntryStack ∗ A.pool
    onPanic := rustPanicOnOom img
  } img
open Model
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
def pqxdhAcceptOptFieldsAt (basePtr pqskPtr ctSlicePtr ctBufPtr : BitVec 64) (inp : AcceptKeysInput)
    : SepProp :=
  ((basePtr + 32#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗ ((basePtr + 96#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
    ((basePtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗ ((basePtr +
    160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((basePtr + 208#64) ↦₆₄ pqskPtr) ∗ ((basePtr +
    216#64) ↦₆₄ 3168#64) ∗ ((basePtr + 224#64) ↦₆₄ ctSlicePtr) ∗ ((basePtr +
    232#64) ↦₈ (if (match inp.opkBSk? with
    | some _ => true | none => false) = true then 1#8 else 0#8)) ∗
  (match inp.opkBSk? with | some opkSk => (basePtr + 265#64) ↦ₛ bytesToBv8 opkSk | none => .emp) ∗
    (pqskPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗ ((pqskPtr +
    1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗ (ctSlicePtr ↦₆₄ ctBufPtr) ∗ ((ctSlicePtr +
    8#64) ↦₆₄ 1569#64) ∗ (ctBufPtr ↦₈ 8#8) ∗ ((ctBufPtr +
    1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗ ((ctBufPtr +
    2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1)
def pqxdhAcceptOptFieldsSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec AcceptFieldsCallGhost := Spec.inImage {
    pre := fun (g : AcceptFieldsCallGhost) s =>
      ⌜s.readReg64 .x0 = g.argPtr ∧ s.readReg64 .x8 = g.outPtr ∧ g.inp.trustedPeer = true ∧
        g.inp.replayOk = true ∧ g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
        WellSizedAcceptKeysInput g.inp⌝ ∗
        pqxdhAcceptOptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
        memRegion g.outPtr 104 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s.sp pqxdhEntryStack ∗
        A.pool
    post := fun (g : AcceptFieldsCallGhost) s0 sf => ⌜sf.trace = s0.trace⌝ ∗
        pqxdhAcceptOptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
        (match Model.acceptKeys P g.inp with
       | some drKey =>
         g.outPtr ↦ₛ bytesToBv8 (handshakeKeysResultOk104 drKey)
       | none =>
         pqxdhAcceptErrStrong2At g.outPtr ∗ anyHeap) ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
         stackAt s0.sp pqxdhEntryStack ∗ A.pool
    onPanic := rustPanicOnOom img
  } img
set_option maxHeartbeats 48000000 in
private theorem pqxdhAccept_opt_fields_base_ok_gen {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hfn : libsignalSessionCode.fnOff pqxdhAcceptSym = 0x23920)
    (hcanon : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym + BitVec.ofNat 64 107556)
      (ecPubKeyIsCanonicalCallSpec P))
    (hag' : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym + BitVec.ofNat 64 110016)
      (pqxdhCalculateAgreementSpec P A img))
    (hvec_append : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym + BitVec.ofNat 64 18446744073709516340)
      pqxdhVecAppendElementsFastSpec)
    (hext_none : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym + BitVec.ofNat 64 18446744073709515800)
      (pqxdhHkdfExtractNoneSpec P img))
    (hexp : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym + BitVec.ofNat 64 18446744073709514580)
      (pqxdhHkdfExpandCellsSpec P img 12))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x23920)))
      pqxdhShimSpec)
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - 0x23920)))
      (rustAllocSpec A))
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - 0x23920)))
      (rustDeallocSpec A))
    (hmemcpy : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" - 0x23920)))
      pqxdhMemcpyRegionSpec)
    (hdecaps : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym +
        BitVec.ofNat 64 (num% (ls_off% "libcrux_ml_kem::mlkem1024::kyber::decapsulate" - 0x23920)))
      (kyberDecapsStubSpec P))
    (hpan_rawvec : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym +
        BitVec.ofNat 64 (num% (ls_off% "alloc::raw_vec::handle_error" - 0x23920))) = some Rust.panicked)
    (hpan_alloc : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym +
        BitVec.ofNat 64 (num% (ls_off% "alloc::alloc::handle_alloc_error" - 0x23920))) = some Rust.panicked) :
    subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpec P A img) := by
  have hb := base_aligned_of_loads himg
  refine subroutine_ok_inImage_rodata4 (rodata_0x7c604 himg) (rodata_0x7c267 himg) (rodata_0x7ff6a
    himg) (rodata_0x81028 himg) ?_; unfold rustPanicOnOom
  have hexp' := hexp
  simp only [pqxdhHkdfExpandCellsSpec, cells, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  have hadrp_fa8_1 : (((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym +
    220#64 &&& 0xfffffffffffff000#64) + bv% (ls_str% "incoming base key is invalid" - 0x23000)) = img.base + bv% (ls_str% "incoming base key is invalid") := by
    rw [Program.fnAddr_rebase, hfn]; exact accept_adrp_55604_1 hb
  have hadrp_fa8_2 : (((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym +
    220#64 &&& 0xfffffffffffff000#64) + bv% (page% (ls_str% "incoming base key is invalid") - 0x23000) + bv% ((ls_str% "incoming base key is invalid") % 4096)) = img.base + bv% (ls_str% "incoming base key is invalid") := by
    rw [Program.fnAddr_rebase, hfn]; exact accept_adrp_55604_2 hb
  have hadrp_dbf_1 : (((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym +
    1064#64 &&& 0xfffffffffffff000#64) + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024" - 0x23000)) = img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
    rw [Program.fnAddr_rebase, hfn]; exact accept_adrp_55267_1 hb
  have hadrp_dbf_2 : (((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym +
    1064#64 &&& 0xfffffffffffff000#64) + bv% (page% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") - 0x23000) + bv% ((ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") % 4096)) = img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
    rw [Program.fnAddr_rebase, hfn]; exact accept_adrp_55267_2 hb
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.E2E.Pqxdh.pqxdhAccept
    img.base
    (Rust.withPanics ext) hfn 0x23920 1728
  clear himg hexp hfn hb
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pqxdhAcceptSym = entry
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches; wpp_init x s0
  rcases x with ⟨inp, argPtr, pqskPtr, ctSlicePtr, ctBufPtr, outPtr⟩; dsimp only at *
  subst ‹s0.readReg64 (.gpr 0#5) = argPtr› ‹s0.readReg64 (.gpr 8#5) = outPtr›
  have hws : WellSizedAcceptKeysInput inp := ‹WellSizedAcceptKeysInput inp›
  rcases hws with ⟨hikBSk, _hikBPk, hspkBSk, _hspkBPk, _hopk_sz, hpqSk, _hpqPk, hikAPk, hekAPk,
    hkemCt⟩; rw (occs := .pos [1]) [stackAt_pqxdh_accept_top s0.sp]
  refine SepWPp.fold (Entails.of_eq (pqsk_region_phaseA_split s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells4_sub4944_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells10_sub80_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; have hF0 : FrozenRo img s0.mem := ‹FrozenRo img s0.mem›
  unfold pqxdhAcceptOptFieldsAt; refine SepWPp.of_sepWP_frozen hF0 (mid := entry + 52#64) ?_
  wp_steps; wp_call hcanon ⟨s0.readReg64 (.gpr 0#5) + 160#64, inp.hdr.ekAPk⟩
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF1; try simp only [arm64_norm] at hF1
  cases hcanon_b : P.isCanonical inp.hdr.ekAPk
  · have hacc_none : acceptKeys P inp = none :=
      acceptKeys_eq_none_of_not_canonical P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
        hikAPk hekAPk hcanon_b; have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = false := hcanon_b
    simp only [hcanon_ec, Bool.false_eq_true, ↓reduceIte] at *; rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP (mid := entry + 216#64) ?_; wp_steps; wp_call hshim (); wp_steps
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call halloc (28, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs) (fun halloc0 htr0 =>
      ?_) (fun halloc0 halign0 htr0 => ?_)
    · refine SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x23920)) ?_; wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
        (by sep_focus) ?_; sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (incoming_alloc_split _)) (by sep_focus) ?_
      sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (rodata_incoming_split1 (img.base + bv% (ls_str% "incoming base key is invalid"))))
        (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
      wp_simp_pre_fast [hadrp_fa8_1, hadrp_fa8_2, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps; refine SepWP.fold (Entails.of_eq (rodata_incoming_1_to_2 (img.base + bv% (ls_str% "incoming base key is invalid"))))
        (by sep_focus) ?_; wp_steps
      refine SepWP.fold (Entails.of_eq (rodata_incoming_split2 (img.base + bv% (ls_str% "incoming base key is invalid"))).symm)
        (by sep_focus) ?_; refine SepWP.fold (incoming_overlap_prep _ _ _) (by sep_focus) ?_
      sep_elim_exists'; wp_steps; refine SepWP.fold (err28_anyHeap_intro A _ _ _) (by sep_focus) ?_
      refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5)) 0x8000000000000018#64
        _ _ _ _ (by decide)) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (pqsk_region_phaseA_merge s0.sp _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
      rw [hacc_none]
      clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
        hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done
  · have hsp_align_eq : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_align
    have hsp_orr1 : (s0.sp - 4912#64) ||| 1#64 = s0.sp - 4911#64 := sp_sub4912_orr_one hsp_align_eq
    have hsp_orr2 : (s0.sp - 1744#64) ||| 1#64 = s0.sp - 1743#64 := sp_sub1744_orr_one hsp_align_eq
    obtain ⟨ss, hss, hss_len, hfit_ss⟩ := kyberDecaps_some_and_fitBv8_eq hWF hpqSk hkemCt
    have hdecaps_some : (P.kemDecaps inp.pqspkBSk inp.hdr.kemCt).isSome = true := by simp [hss]
    have hss_bv_len : (bytesToBv8 ss).length = 32 := by simp [bytesToBv8, hss_len]
    have hpqSk_drop_len : ((bytesToBv8 inp.pqspkBSk).drop 1).length = 3167 := by
      simp [bytesToBv8, hpqSk]
    have hkemCt_drop_len : ((bytesToBv8 inp.hdr.kemCt).drop 1).length = 1567 := by
      simp [bytesToBv8, hkemCt]
    obtain ⟨s0_w, s1_w, s2_w, s3_w, -, hss_cells⟩ := exists_unpack64_of_length_32 hss_bv_len
    have hro_dbf : infoPqxdh = INFO_PQXDH := by rfl_kernel
    have hinfo_len : BitVec.ofNat 64 INFO_PQXDH.length = 46#64 := by rfl_kernel
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = true := hcanon_b
    simp only [hcanon_ec, ↓reduceIte] at hpost; rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP_frozen hF1 (mid := entry + 72#64) ?_; wp_steps; wp_call hshim ()
    wp_steps; have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call halloc (192, 1)
    apply SepWP.done (by wp_norm_goal)
      (by wp_norm_goal); intro hF2; try simp only [arm64_norm] at hF2
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs) (fun halloc192 htr192 =>
      ?_) (fun halloc192 halign192 htr192 => ?_)
    · refine SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x23920)) ?_; wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (memRegion_192_init_split _)) (by sep_focus) ?_
      sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (alloc_to_calc_stack s0.sp)) (by sep_focus) ?_
      refine SepWPp.of_sepWP_frozen hF2 (mid := entry + 110016#64) ?_; wp_steps
      refine SepWP.fold (Entails.of_eq (pointsTo64_4_allOnes_eq_F_X25519 _)) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal)
        (by wp_norm_goal); intro hF3; try simp only [arm64_norm] at hF3
      refine SepWPp_call_hag hWF hag' hF3 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
        (s0.readReg64 (.gpr 0#5) + 128#64) inp.hdr.ikAPk (by wp_norm_lhs) (by wp_norm_lhs) hsp_align
        (by wp_norm_lhs) (ret_pc := entry + 120#64) (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hikAPk⟩
        (by sep_focus) (allowPanic_hag (by wp_norm_lhs))
        (fun hdh1 sf1 hi1 u2_1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
        (fun hdh1 sf1 dh1_ptr hpc1 hrun1 hsp1 hcs1 htr1 hF4 => ?_)
      · have hacc_none : acceptKeys P inp = none :=
          acceptKeys_eq_none_of_dh1_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true› hikAPk
          hekAPk hcanon_b hdh1; dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
          hcs29⟩
        simp only [arm64_norm] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29
        refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
          (by sep_focus) ?_; sep_elim_exists'
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.fold (vec_err_dh1_merge _) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
        wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
        refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
        refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
          0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
        refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
        rw [hacc_none]
        clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
          hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done
      · have hdh1_len : (P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 32 := hWF.x25519_len _ _
        have hdh1_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)).length = 32 := by
          simp [bytesToBv8, hdh1_len]
        have hpfx1_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 64 := by
          simp [F_X25519, hdh1_len]
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
          hcs29⟩
        simp only [arm64_norm] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.of_sepWP_frozen hF4 (mid := entry + 110016#64) ?_; wp_steps
        wp_call hmemcpy ⟨_, dh1_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)⟩; wp_steps
        refine SepWP.fold (hdh1_bv_len ▸ pointsToBytes_entails_memRegion dh1_ptr _)
          (by sep_focus) ?_; wp_call hdealloc (dh1_ptr, 32, 1); wp_steps
        refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh1_ptr 32#64) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ F_X25519 (P.x25519 inp.spkBSk
          inp.hdr.ikAPk) 32 (by decide))) (by sep_focus) ?_
        refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        apply SepWP.done (by wp_norm_goal)
          (by wp_norm_goal); intro hF5; try simp only [arm64_norm] at hF5
        refine SepWPp_call_hag hWF hag' hF5 (s0.readReg64 (.gpr 0#5) + 32#64) inp.ikBSk
          (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
          (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc :=
          entry + 304#64) (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hikBSk, hekAPk⟩
          (by sep_focus) (allowPanic_hag (by wp_norm_lhs))
          (fun hdh2 sf2 hi2 u2_2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
          (fun hdh2 sf2 dh2_ptr hpc2 hrun2 hsp2 hcs2 htr2 hF6 => ?_)
        · have hacc_none : acceptKeys P inp = none :=
            acceptKeys_eq_none_of_dh2_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
            hikAPk hekAPk hcanon_b hdh1 hdh2; dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
               hcs2_29
          refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
            (by sep_focus) ?_; sep_elim_exists'
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.fold (vec_err_dh2_merge _ hpfx1_len) (by sep_focus) ?_
          apply SepWPp.of_sepWP_ret; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
          refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
          refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
            0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
          refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
          rw [hacc_none]
          clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
            hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done
        · have hdh2_len : (P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
          have hdh2_bv_len : (bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)).length = 32 := by
            simp [bytesToBv8, hdh2_len]
          have hpfx2_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
            P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 96 := by simp [F_X25519, hdh1_len, hdh2_len]
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
               hcs2_29
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.of_sepWP_frozen hF6 (mid := entry + 110016#64) ?_; wp_steps
          wp_call hmemcpy ⟨_, dh2_ptr, bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)⟩; wp_steps
          refine SepWP.fold (hdh2_bv_len ▸ pointsToBytes_entails_memRegion dh2_ptr _)
            (by sep_focus) ?_; wp_call hdealloc (dh2_ptr, 32, 1); wp_steps
          refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh2_ptr 32#64)
            (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
            P.x25519 inp.spkBSk inp.hdr.ikAPk) (P.x25519 inp.ikBSk inp.hdr.ekAPk) 64
            (by simp only [bytesToBv8, List.length_map, hpfx1_len]))) (by sep_focus) ?_
          refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          apply SepWP.done (by wp_norm_goal)
            (by wp_norm_goal); intro hF7; try simp only [arm64_norm] at hF7
          refine SepWPp_call_hag hWF hag' hF7 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
            (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
            (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc :=
            entry + 404#64) (by wp_norm_lhs) (by wp_norm_lhs)
            ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hekAPk⟩
            (by sep_focus) (allowPanic_hag (by wp_norm_lhs))
            (fun hdh3 sf3 hi3 u2_3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
            (fun hdh3 sf3 dh3_ptr hpc3 hrun3 hsp3 hcs3 htr3 hF8 => ?_)
          · have hacc_none : acceptKeys P inp = none :=
              acceptKeys_eq_none_of_dh3_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
              hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
            dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
                 hcs3_29
            refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
              (by sep_focus) ?_; sep_elim_exists'
            refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
            refine SepWPp.fold (vec_err_dh3_merge _ hpfx2_len) (by sep_focus) ?_
            apply SepWPp.of_sepWP_ret; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
            refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
            refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
              0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
            refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
              (by sep_focus) ?_; rw [hacc_none]
            clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
              hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done
          · have hdh3_len : (P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
            have hdh3_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)).length = 32 := by
              simp [bytesToBv8, hdh3_len]
            have hpfx3_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
              P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 128 :=
              by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len]
            dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
                 hcs3_29
            cases hopk_eq : inp.opkBSk? with
            | none =>
              have hikm160_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                ss).length = 160 := by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, hss_len]
              have hikm160_bv : BitVec.ofNat 64 (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                ss).length = 160#64 := by rw [hikm160_len]
              have hacc_some : acceptKeys P inp = some (Model.deriveDRKeys P (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss)) :=
                acceptKeys_eq_some_of_opk_none P inp ss ‹inp.trustedPeer = true›
                ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hss
              have hprk160_len : (bytesToBv8 (hkdfExtractRef P none (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss))).length = 32 := by
                simp [bytesToBv8, hkdfExtractRef_length]
              have hprk160_len32 : (hkdfExtractRef P none (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss)).length = 32 :=
                hkdfExtractRef_length P none _
              obtain ⟨p0, p1, p2, p3, -, hprk160⟩ := exists_unpack64_of_length_32 hprk160_len
              obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm160, hout160⟩ :=
                exists_unpack64_hkdfDerive96 P hWF (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss)
              simp only [Bool.false_eq_true, ↓reduceIte, emp_sepConj]
              refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
              refine SepWPp.of_sepWP_frozen hF8 (mid := entry + 944#64) ?_; wp_steps
              wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩; wp_steps
              refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
                (by sep_focus) ?_; wp_call hdealloc (dh3_ptr, 32, 1)
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk) (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
                (by simp only [bytesToBv8, List.length_map, hpfx2_len]))) (by sep_focus) ?_
              refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp 0#64 dh3_ptr 32#64 0#64)
                (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (pqsk_region_phaseB_split s0.sp)) (by sep_focus) ?_
              sep_elim_exists'
              refine SepWP.fold (Entails.of_eq (kemct_region_phaseB_split s0.sp)) (by sep_focus) ?_
              sep_elim_exists'
              refine SepWP.fold (Entails.of_eq (sub176_split_32_64 s0.sp)) (by sep_focus) ?_
              sep_elim_exists'; wp_steps
              wp_call hmemcpy ⟨s0.sp - 4911#64, pqskPtr + 1#64, (bytesToBv8 inp.pqspkBSk).drop 1⟩
              wp_steps
              wp_call hmemcpy ⟨s0.sp - 1743#64, ctBufPtr + 2#64, (bytesToBv8 inp.hdr.kemCt).drop 1⟩
              refine SepWP.fold (pqsk_head_tail_merge s0.sp hpqSk) (by sep_focus) ?_
              refine SepWP.fold (kemct_head_tail_merge s0.sp hkemCt) (by sep_focus) ?_; wp_steps
              wp_call hdecaps ⟨s0.sp - 4912#64, inp.pqspkBSk, s0.sp - 1744#64, inp.hdr.kemCt,
                s0.sp - 176#64⟩; wp_steps; wp_call hshim (); wp_steps; wp_call halloc (32, 1)
              apply SepWP.done (by wp_norm_goal)
                (by wp_norm_goal); intro hF9; try simp only [arm64_norm] at hF9
              refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
                (fun halloc32 htr32 => ?_) (fun halloc32 halign32 htr32 => ?_)
              · refine SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - 0x23920)) ?_; wp_steps
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
                exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
              · (conv => arg 4; rw [hfit_ss, ss_sub176_eq s0.sp hss_cells, hro_dbf])
                refine SepWPp.fold (pqsk_to_extract_region s0.sp hpqSk) (by sep_focus) ?_
                refine SepWPp.fold (kemct_to_hmac18_region s0.sp hkemCt) (by sep_focus) ?_
                sep_elim_exists'
                refine SepWPp.fold (Entails.of_eq (ss_and_vec128_split _ _)) (by sep_focus) ?_
                sep_elim_exists'; apply SepWPp.of_sepWP_ret; apply SepWP.of_sepWP_frozen hF9
                wp_steps
                refine SepWP.fold (cells4_to_memRegion32 _ s0_w s1_w s2_w s3_w) (by sep_focus) ?_
                wp_call hdealloc (_, 32, 1)
                refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (ss_vec_add128_merge _ hss_cells) (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk) ss 128 (by simp only [bytesToBv8,
                  List.length_map, hpfx3_len]))) (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (stack_to_kdf s0.sp)) (by sep_focus) ?_; wp_steps
                apply SepWP.checkpoint_frozen (by wp_norm_lhs)
                  (by wp_norm_lhs); intro hF10; try simp only [arm64_norm] at hF10
                wp_call hext_none (s0.sp - 4912#64, _, F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss, s0.sp - 4944#64)
                refine SepWP.fold (vec_ok_160_merge _ hikm160_len) (by sep_focus) ?_
                refine SepWP.fold (prk_sub4912_eq s0.sp hprk160) (by sep_focus) ?_
                try (conv => arg 4; simp only [bv_sub_add_lit', BitVec.reduceSub])
                refine SepWP.fold (hmacCore_split_sub4880 P s0.sp _) (by sep_focus) ?_
                sep_elim_exists'; refine SepWP.pure_left_elim fun hhmac160 => ?_; wp_steps
                apply SepWP.done_frozen (by wp_norm_lhs)
                  (by wp_norm_lhs); intro hF11; try simp only [arm64_norm] at hF11
                refine SepWP.fold (hmacState_merge_sub1744 P s0.sp _ hhmac160) (by sep_focus) ?_
                (conv => arg 4; simp only [hadrp_dbf_1, hadrp_dbf_2, arm64_norm, ← hinfo_len])
                wp_call hexp' (s0.sp - 1744#64, hkdfExtractRef P none (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss), s0.sp - 4912#64, img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"),
                  INFO_PQXDH, s0.sp - 176#64, s0.sp - 4944#64); sep_elim_exists'
                try (conv => arg 4; simp only [bv_sub_add_lit', BitVec.reduceSub])
                refine SepWP.fold (Entails.of_eq (stack_to_kdf s0.sp).symm) (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (outPtr_ok104_cells_split (s0.readReg64 (.gpr
                  8#5)))) (by sep_focus) ?_; sep_elim_exists'
                refine SepWP.fold (okm_sub176_eq s0.sp hokm160) (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (sub1680_split_32_48 s0.sp)) (by sep_focus) ?_
                sep_elim_exists'; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
                refine SepWP.fold (outPtr_ok104_cells_merge (s0.readReg64 (.gpr 8#5)) hout160)
                  (by sep_focus) ?_
                refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (sub4912_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (sub1744_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
                  (by sep_focus) ?_
                refine SepWP.fold (sub176_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
                  (by sep_focus) ?_
                refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
                  (by sep_focus) ?_; (conv => arg 4; rw [← hro_dbf]); rw [hacc_some]
                clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
                  hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done
            | some opkSk =>
              have hopkSk : opkSk.length = 32 := _hopk_sz opkSk hopk_eq; simp only [↓reduceIte]
              refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
              refine SepWPp.of_sepWP_frozen hF8 (mid := entry + 110016#64) ?_; wp_steps
              wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩; wp_steps
              refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
                (by sep_focus) ?_; wp_call hdealloc (dh3_ptr, 32, 1)
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              wp_steps; refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh3_ptr 32#64)
                (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk) (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
                (by simp only [bytesToBv8, List.length_map, hpfx2_len]))) (by sep_focus) ?_
              refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              apply SepWP.done (by wp_norm_goal)
                (by wp_norm_goal); intro hF8_1; try simp only [arm64_norm] at hF8_1
              refine SepWPp_call_hag hWF hag' hF8_1 (s0.readReg64 (.gpr 0#5) + 265#64) opkSk
                (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
                (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc :=
                entry + 720#64) (by wp_norm_lhs) (by wp_norm_lhs)
                ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hopkSk, hekAPk⟩
                (by sep_focus) (allowPanic_hag (by wp_norm_lhs))
                (fun hdh4 sf4 hi4 u2_4 hpc4 hrun4 hsp4 hcs4 htr4 => ?_)
                (fun hdh4 sf4 dh4_ptr hpc4 hrun4 hsp4 hcs4 htr4 hF8_2 => ?_)
              · have hacc_none : acceptKeys P inp = none :=
                  acceptKeys_eq_none_of_dh4_zero P inp opkSk ‹inp.trustedPeer = true›
                  ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                  ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hdh4
                dsimp only [CalleeSavedPreserved, Reg.fp] at hcs4
                rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25,
                  hcs4_26, hcs4_27, hcs4_28, hcs4_29⟩
                simp only [arm64_norm]
                  at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28
                     hcs4_29
                refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
                  (by sep_focus) ?_; sep_elim_exists'
                refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
                refine SepWPp.fold (vec_err_dh4_merge _ hpfx3_len) (by sep_focus) ?_
                apply SepWPp.of_sepWP_ret; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
                refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
                refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
                  0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
                refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
                  (by sep_focus) ?_; rw [hacc_none]
                clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
                  hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done
              · have hdh4_len : (P.x25519 opkSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
                have hdh4_bv_len : (bytesToBv8 (P.x25519 opkSk inp.hdr.ekAPk)).length = 32 := by
                  simp [bytesToBv8, hdh4_len]
                have hpfx4_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                  P.x25519 opkSk inp.hdr.ekAPk).length = 160 := by
                  simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, hdh4_len]
                have hikm192_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                  P.x25519 opkSk inp.hdr.ekAPk ++ ss).length = 192 := by
                  simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, hdh4_len, hss_len]
                have hikm192_bv : BitVec.ofNat 64 (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                  P.x25519 opkSk inp.hdr.ekAPk ++ ss).length = 192#64 := by rw [hikm192_len]
                have hacc_some : acceptKeys P inp = some (Model.deriveDRKeys P (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss)) :=
                  acceptKeys_eq_some_of_opk_some P inp opkSk ss ‹inp.trustedPeer = true›
                  ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                  ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hdh4 hss
                have hprk192_len : (bytesToBv8 (hkdfExtractRef P none (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++
                  ss))).length = 32 := by simp [bytesToBv8, hkdfExtractRef_length]
                have hprk192_len32 : (hkdfExtractRef P none (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss)).length =
                  32 := hkdfExtractRef_length P none _
                obtain ⟨p0, p1, p2, p3, -, hprk192⟩ := exists_unpack64_of_length_32 hprk192_len
                obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm192, hout192⟩ :=
                  exists_unpack64_hkdfDerive96 P hWF (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss)
                dsimp only [CalleeSavedPreserved, Reg.fp] at hcs4
                rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25,
                  hcs4_26, hcs4_27, hcs4_28, hcs4_29⟩
                simp only [arm64_norm]
                  at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28
                     hcs4_29
                refine SepWPp.fold (Entails.of_eq (calc_to_vecAppend_stack s0.sp)) (by sep_focus) ?_
                refine SepWPp.of_sepWP_frozen hF8_2 (mid := entry + 944#64) ?_; wp_steps
                wp_call hvec_append (s0.sp - 4936#64, _, dh4_ptr,
                  bytesToBv8 (P.x25519 opkSk inp.hdr.ekAPk))
                refine SepWP.fold (vecAppend_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                wp_steps
                refine SepWP.fold (hdh4_bv_len ▸ pointsToBytes_entails_memRegion dh4_ptr _)
                  (by sep_focus) ?_; wp_call hdealloc (dh4_ptr, 32, 1)
                refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk) (P.x25519 opkSk inp.hdr.ekAPk) 128
                  (by simp only [bytesToBv8, List.length_map, hpfx3_len]))) (by sep_focus) ?_
                refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp 0#64 dh4_ptr 32#64 0#64)
                  (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (pqsk_region_phaseB_split s0.sp)) (by sep_focus) ?_
                sep_elim_exists'
                refine SepWP.fold (Entails.of_eq (kemct_region_phaseB_split s0.sp))
                  (by sep_focus) ?_; sep_elim_exists'
                refine SepWP.fold (Entails.of_eq (sub176_split_32_64 s0.sp)) (by sep_focus) ?_
                sep_elim_exists'; wp_steps
                wp_call hmemcpy ⟨s0.sp - 4911#64, pqskPtr + 1#64, (bytesToBv8 inp.pqspkBSk).drop 1⟩
                wp_steps; wp_call hmemcpy ⟨s0.sp - 1743#64, ctBufPtr + 2#64,
                  (bytesToBv8 inp.hdr.kemCt).drop 1⟩
                refine SepWP.fold (pqsk_head_tail_merge s0.sp hpqSk) (by sep_focus) ?_
                refine SepWP.fold (kemct_head_tail_merge s0.sp hkemCt) (by sep_focus) ?_; wp_steps
                wp_call hdecaps ⟨s0.sp - 4912#64, inp.pqspkBSk, s0.sp - 1744#64, inp.hdr.kemCt,
                  s0.sp - 176#64⟩; wp_steps; wp_call hshim (); wp_steps; wp_call halloc (32, 1)
                apply SepWP.done (by wp_norm_goal)
                  (by wp_norm_goal); intro hF9; try simp only [arm64_norm] at hF9
                refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
                  (fun halloc32 htr32 => ?_) (fun halloc32 halign32 htr32 => ?_)
                · refine SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - 0x23920)) ?_; wp_steps
                  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                  apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
                  exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
                · (conv => arg 4; rw [hfit_ss, ss_sub176_eq s0.sp hss_cells, hro_dbf])
                  refine SepWPp.fold (pqsk_to_extract_region s0.sp hpqSk) (by sep_focus) ?_
                  refine SepWPp.fold (kemct_to_hmac18_region s0.sp hkemCt) (by sep_focus) ?_
                  sep_elim_exists'
                  refine SepWPp.fold (Entails.of_eq (ss_and_vec160_split _ _)) (by sep_focus) ?_
                  sep_elim_exists'; apply SepWPp.of_sepWP_ret; apply SepWP.of_sepWP_frozen hF9
                  wp_steps
                  refine SepWP.fold (cells4_to_memRegion32 _ s0_w s1_w s2_w s3_w) (by sep_focus) ?_
                  wp_call hdealloc (_, 32, 1)
                  refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                  · simp only [arm64_norm, *]
                  refine SepWP.fold (ss_vec_add160_merge _ hss_cells) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                    P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                    P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk) ss 160
                    (by simp only [bytesToBv8, List.length_map, hpfx4_len]))) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (stack_to_kdf s0.sp)) (by sep_focus) ?_; wp_steps
                  apply SepWP.checkpoint_frozen (by wp_norm_lhs)
                    (by wp_norm_lhs); intro hF10; try simp only [arm64_norm] at hF10
                  wp_call hext_none (s0.sp - 4912#64, _, F_X25519 ++
                    P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                    P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss,
                    s0.sp - 4944#64)
                  refine SepWP.fold (vec_ok_192_merge _ hikm192_len) (by sep_focus) ?_
                  refine SepWP.fold (prk_sub4912_eq s0.sp hprk192) (by sep_focus) ?_
                  try (conv => arg 4; simp only [bv_sub_add_lit', BitVec.reduceSub])
                  refine SepWP.fold (hmacCore_split_sub4880 P s0.sp _) (by sep_focus) ?_
                  sep_elim_exists'; refine SepWP.pure_left_elim fun hhmac192 => ?_; wp_steps
                  apply SepWP.done_frozen (by wp_norm_lhs)
                    (by wp_norm_lhs); intro hF11; try simp only [arm64_norm] at hF11
                  refine SepWP.fold (hmacState_merge_sub1744 P s0.sp _ hhmac192) (by sep_focus) ?_
                  (conv => arg 4; simp only [hadrp_dbf_1, hadrp_dbf_2, arm64_norm, ← hinfo_len])
                  wp_call hexp' (s0.sp - 1744#64, hkdfExtractRef P none (F_X25519 ++
                    P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                    P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss),
                    s0.sp - 4912#64, img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"), INFO_PQXDH, s0.sp - 176#64, s0.sp -
                    4944#64); sep_elim_exists'
                  try (conv => arg 4; simp only [bv_sub_add_lit', BitVec.reduceSub])
                  refine SepWP.fold (Entails.of_eq (stack_to_kdf s0.sp).symm) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (outPtr_ok104_cells_split (s0.readReg64 (.gpr
                    8#5)))) (by sep_focus) ?_; sep_elim_exists'
                  refine SepWP.fold (okm_sub176_eq s0.sp hokm192) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (sub1680_split_32_48 s0.sp)) (by sep_focus) ?_
                  sep_elim_exists'; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
                  refine SepWP.fold (outPtr_ok104_cells_merge (s0.readReg64 (.gpr 8#5)) hout192)
                    (by sep_focus) ?_
                  refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
                  refine SepWP.fold (sub4912_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    _ _ _ _ _) (by sep_focus) ?_
                  refine SepWP.fold (sub1744_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
                    (by sep_focus) ?_
                  refine SepWP.fold (sub176_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
                    (by sep_focus) ?_
                  refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
                    (by sep_focus) ?_
                  refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
                  · simp only [arm64_norm, *]
                  refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
                    (by sep_focus) ?_; (conv => arg 4; rw [← hro_dbf]); rw [hacc_some]
                  clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy
                    hdecaps hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done

theorem pqxdhAccept_opt_fields_base_ok_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image} {C :
    Crypto} {absHooks : String → Option (State → State)} (himg : Obj.Loads
    libsignalSessionImage img) (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks)
    (hext : PqxdhHkdfExtractOk_trap P img C absHooks) (hexp : PqxdhHkdfExpandMultiInfoOk_trap P img C absHooks) (hag : PqxdhCalculateAgreementOk_trap P A img C absHooks) : subroutine_ok
    (trTrapProgAt img.base C absHooks) ((trTrapProgAt img.base C absHooks).fnAddr pqxdhAcceptSym) (pqxdhAcceptOptFieldsSpec P A img) := by
  have hfn : libsignalSessionCode.fnOff pqxdhAcceptSym = 0x23920 :=
    libsignalSessionCode_fnOff_0x23920
  exact pqxdhAccept_opt_fields_base_ok_gen himg hWF hfn
    (subroutine_ok_rel_pqxdh_trap (ecPubKeyIsCanonical_call_ok_trap (C := C) hWF hH)
      libsignalSessionCode_fnOff_0x3dd44 hfn (k := 107556) (by decide))
    (subroutine_ok_rel_pqxdh_trap hag libsignalSessionCode_fnOff_0x3e6e0 hfn (k :=
      110016) (by decide))
    (subroutine_ok_rel_pqxdh_trap (vecAppendElements_fast_ok_trap (b := img.base) (C :=
      C) (absHooks := absHooks))
      libsignalSessionCode_fnOff_0x1af54 hfn (k := 18446744073709516340) (by decide))
    (subroutine_ok_rel_pqxdh_trap hext.1 libsignalSessionCode_fnOff_0x1ad38 hfn (k :=
      18446744073709515800) (by decide))
    (subroutine_ok_rel_pqxdh_trap (hexp 12) libsignalSessionCode_fnOff_0x1a874 hfn (k :=
      18446744073709514580) (by decide))
    (pqxdh_shim_ok_at_trap (b := img.base) (C := C) (absHooks := absHooks)
      (name := pqxdhAcceptSym) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x23920)) (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]))
    (pqxdh_alloc_ok_at_trap (b := img.base) (C := C) (absHooks := absHooks)
      hH.alloc (name := pqxdhAcceptSym) (k := num% (ls_off% "__rustc::__rust_alloc" - 0x23920)) (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")]))
    (pqxdh_dealloc_ok_at_trap (b := img.base) (C := C) (absHooks := absHooks)
      hH.alloc (name := pqxdhAcceptSym) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x23920)) (by rw [hfn, (ls_stub% "__rustc::__rust_dealloc")]))
    (pqxdh_memcpy_region_ok_at_trap (b := img.base) (C := C) (absHooks := absHooks)
      (name := pqxdhAcceptSym) (k := num% (ls_off% "memcpy" - 0x23920)) (by rw [hfn, (ls_stub% "memcpy")]))
    (kyberDecaps_ok_at_trap (C := C) hH (name := pqxdhAcceptSym) (k := num% (ls_off% "libcrux_ml_kem::mlkem1024::kyber::decapsulate" - 0x23920))
      (by rw [hfn, (ls_stub% "libcrux_ml_kem::mlkem1024::kyber::decapsulate")]))
    (pqxdh_panic_at_raw_vec_handle_error_trap (b := img.base) (C := C) (absHooks := absHooks)
      (name := pqxdhAcceptSym) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x23920)) (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")]))
    (pqxdh_panic_at_handle_alloc_error_trap (b := img.base) (C := C) (absHooks := absHooks)
      (name := pqxdhAcceptSym) (k := num% (ls_off% "alloc::alloc::handle_alloc_error" - 0x23920)) (by rw [hfn, (ls_stub% "alloc::alloc::handle_alloc_error")]))

theorem pqxdhAccept_opt_fields_base_ok {P : Primitives} {A : RustAlloc} {img : Obj.Image} {C :
    Crypto} {ctl : BitVec 64} {absHooks : String → Option (State → State)} (himg : Obj.Loads
    libsignalSessionImage img) (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks)
    (hext : PqxdhHkdfExtractOk P img C ctl absHooks) (hexp : PqxdhHkdfExpandMultiInfoOk P img C ctl
    absHooks) (hag : PqxdhCalculateAgreementOk P A img C ctl absHooks) : subroutine_ok
    (tripleRatchetProgAt img.base C ctl absHooks) ((tripleRatchetProgAt img.base C ctl
      absHooks).fnAddr pqxdhAcceptSym) (pqxdhAcceptOptFieldsSpec P A img) := by
  have hfn : libsignalSessionCode.fnOff pqxdhAcceptSym = 0x23920 :=
    libsignalSessionCode_fnOff_0x23920
  exact pqxdhAccept_opt_fields_base_ok_gen himg hWF hfn
    (subroutine_ok_rel_pqxdh (ecPubKeyIsCanonical_call_ok (C := C) (ctl := ctl) hWF hH)
      libsignalSessionCode_fnOff_0x3dd44 hfn (k := 107556) (by decide))
    (subroutine_ok_rel_pqxdh hag libsignalSessionCode_fnOff_0x3e6e0 hfn (k :=
      110016) (by decide))
    (subroutine_ok_rel_pqxdh (vecAppendElements_fast_ok (b := img.base) (C :=
      C) (ctl := ctl) (absHooks := absHooks))
      libsignalSessionCode_fnOff_0x1af54 hfn (k := 18446744073709516340) (by decide))
    (subroutine_ok_rel_pqxdh hext.1 libsignalSessionCode_fnOff_0x1ad38 hfn (k :=
      18446744073709515800) (by decide))
    (subroutine_ok_rel_pqxdh (hexp 12) libsignalSessionCode_fnOff_0x1a874 hfn (k :=
      18446744073709514580) (by decide))
    (pqxdh_shim_ok_at (b := img.base) (C := C) (ctl := ctl) (absHooks := absHooks)
      (name := pqxdhAcceptSym) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x23920)) (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]))
    (pqxdh_alloc_ok_at (b := img.base) (C := C) (ctl := ctl) (absHooks := absHooks)
      hH.alloc (name := pqxdhAcceptSym) (k := num% (ls_off% "__rustc::__rust_alloc" - 0x23920)) (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")]))
    (pqxdh_dealloc_ok_at (b := img.base) (C := C) (ctl := ctl) (absHooks := absHooks)
      hH.alloc (name := pqxdhAcceptSym) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x23920)) (by rw [hfn, (ls_stub% "__rustc::__rust_dealloc")]))
    (pqxdh_memcpy_region_ok_at (b := img.base) (C := C) (ctl := ctl) (absHooks := absHooks)
      (name := pqxdhAcceptSym) (k := num% (ls_off% "memcpy" - 0x23920)) (by rw [hfn, (ls_stub% "memcpy")]))
    (kyberDecaps_ok_at (C := C) (ctl := ctl) hH (name := pqxdhAcceptSym) (k := num% (ls_off% "libcrux_ml_kem::mlkem1024::kyber::decapsulate" - 0x23920))
      (by rw [hfn, (ls_stub% "libcrux_ml_kem::mlkem1024::kyber::decapsulate")]))
    (pqxdh_panic_at_raw_vec_handle_error (b := img.base) (C := C) (ctl := ctl) (absHooks := absHooks)
      (name := pqxdhAcceptSym) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x23920)) (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")]))
    (pqxdh_panic_at_handle_alloc_error (b := img.base) (C := C) (ctl := ctl) (absHooks := absHooks)
      (name := pqxdhAcceptSym) (k := num% (ls_off% "alloc::alloc::handle_alloc_error" - 0x23920)) (by rw [hfn, (ls_stub% "alloc::alloc::handle_alloc_error")]))

/-! ## Contract-Backed `tripleRatchetProgAtExt` Generalization -/

section Ext

export CryptoVerification.E2E.Pqxdh.Initiator
  (pqxdhHookStackExt pqxdhEntryStackExt pqxdhHkdfStackExt)

abbrev calculateAgreementSubStackExt : Nat := 64 + pqxdhHookStackExt
abbrev calculateAgreementStackExt : Nat := 160 + calculateAgreementSubStackExt

/-- `pqxdhMemcpyRegionSpec` with `allocHookStack` (`4096` B = `CliExt.memHookStack`) stack budget. -/
def pqxdhMemcpyRegionExtSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ bs.length < 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp allocHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack

/-- `kyberDecapsStubSpec` with `pqxdhHookStackExt` (`16384` B = `extHookStack`) stack budget. -/
def kyberDecapsStubSpecExt (P : Primitives) : Spec KyberDecapsCall where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.skPtr ∧ s.readReg64 .x1 = g.ctPtr ∧ s.readReg64 .x8 = g.outPtr ∧
      g.sk3168.length = 3168 ∧ g.ct1568.length = 1568 ∧
      (P.kemDecaps g.sk3168 g.ct1568).isSome⌝ ∗
      (g.skPtr ↦ₛ bytesToBv8 g.sk3168) ∗ (g.ctPtr ↦ₛ bytesToBv8 g.ct1568) ∗
      memRegion g.outPtr 32 ∗ stackAt s.sp pqxdhHookStackExt
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.skPtr ↦ₛ bytesToBv8 g.sk3168) ∗ (g.ctPtr ↦ₛ bytesToBv8 g.ct1568) ∗
      (g.outPtr ↦ₛ fitBv8 32 (kyberDecapsOutBytes P g.sk3168 g.ct1568)) ∗
      stackAt s0.sp pqxdhHookStackExt

/-- `dalekMontToEdStubSpec` with `pqxdhHookStackExt` (`16384` B = `extHookStack`) stack budget. -/
def dalekMontToEdStubSpecExt (P : Primitives) (_img : Obj.Image := default) :
    Spec DalekMontToEdGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧
      (s.readReg64 .x1).setWidth 8 = BitVec.ofNat 8 g.signBit.toNat ∧
      s.readReg64 .x8 = g.outPtr ∧ g.inBytes.length = 32⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ memRegion g.outPtr 168 ∗ stackAt s.sp pqxdhHookStackExt
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      dalekMontToEdOutAt P g.outPtr g.inBytes (g.signBit &&& 1) ∗ stackAt s0.sp pqxdhHookStackExt

/-- `cryptoBoolRegStubSpec` with 32-bit `w0` return (`CliExt.torsionFreeSpec`) and
`pqxdhHookStackExt` (`16384` B = `extHookStack`) stack budget. -/
def cryptoBoolRegStubSpecExt (pred : Bytes → Bool) (inLen : Nat) (_img : Obj.Image := default) :
    Spec CryptoUnaryGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧ g.inBytes.length = inLen⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ stackAt s.sp pqxdhHookStackExt
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 32 = (if pred g.inBytes then 1#32 else 0#32)⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ stackAt s0.sp pqxdhHookStackExt

def ecPubKeyIsCanonicalCallSpecExt (P : Primitives) : Spec KeyCanonicalGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.keyPtr ∧ g.keyBytes.length = 32⌝ ∗
      (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗ stackAt s.sp (pqxdhHookStackExt + 400)
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 8 = (if P.isCanonicalEC g.keyBytes then 1#8 else 0#8)⌝ ∗
      (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗ stackAt s0.sp (pqxdhHookStackExt + 400)

/-- Contract-backed external hook bundle for `ResponderCore` (`Pqxdh::accept`,
`is_canonical`, `Vec::append_elements`) on `tripleRatchetProgAtExt` at `extHookStack = 16384`. -/
structure PqxdhHookContractsExt (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) : Prop where
  alloc            : AllocHooks A absHooks
  shim             : HookSat absHooks "__rustc::__rust_no_alloc_shim_is_unstable_v2"
                       SignalSession.CliExt.shimSpec
  memcpy           : HookSat absHooks "memcpy" SignalSession.CliExt.memcpySpec
  kyberDecaps      : HookSat absHooks kyberDecapsStub (kyberDecapsStubSpecExt P)
  dalekMontToEd    : HookSat absHooks dalekMontToEdStub (dalekMontToEdStubSpecExt P img)
  dalekTorsionFree : HookSat absHooks dalekTorsionFreeStub
                       (cryptoBoolRegStubSpecExt P.isTorsionFree 160 img)

theorem PqxdhHookContractsExt.of_hooks_eq {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext hooks : String → Option (State → State)}
    (h : PqxdhHookContractsExt P A img ext)
    (halloc : hooks "__rustc::__rust_alloc" = ext "__rustc::__rust_alloc")
    (hdealloc : hooks "__rustc::__rust_dealloc" = ext "__rustc::__rust_dealloc")
    (hrealloc : hooks "__rustc::__rust_realloc" = ext "__rustc::__rust_realloc")
    (hshim : hooks "__rustc::__rust_no_alloc_shim_is_unstable_v2" =
      ext "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (hmemcpy : hooks "memcpy" = ext "memcpy")
    (hdec : hooks kyberDecapsStub = ext kyberDecapsStub)
    (hmont : hooks dalekMontToEdStub = ext dalekMontToEdStub)
    (htors : hooks dalekTorsionFreeStub = ext dalekTorsionFreeStub) :
    PqxdhHookContractsExt P A img hooks where
  alloc := {
    alloc   := let ⟨fn, hfn, hok⟩ := h.alloc.alloc; ⟨fn, halloc.trans hfn, hok⟩
    dealloc := let ⟨fn, hfn, hok⟩ := h.alloc.dealloc; ⟨fn, hdealloc.trans hfn, hok⟩
    realloc := let ⟨fn, hfn, hok⟩ := h.alloc.realloc; ⟨fn, hrealloc.trans hfn, hok⟩
  }
  shim             := let ⟨fn, hfn, hok⟩ := h.shim; ⟨fn, hshim.trans hfn, hok⟩
  memcpy           := let ⟨fn, hfn, hok⟩ := h.memcpy; ⟨fn, hmemcpy.trans hfn, hok⟩
  kyberDecaps      := let ⟨fn, hfn, hok⟩ := h.kyberDecaps; ⟨fn, hdec.trans hfn, hok⟩
  dalekMontToEd    := let ⟨fn, hfn, hok⟩ := h.dalekMontToEd; ⟨fn, hmont.trans hfn, hok⟩
  dalekTorsionFree := let ⟨fn, hfn, hok⟩ := h.dalekTorsionFree; ⟨fn, htors.trans hfn, hok⟩

theorem hookOk_map_ext {α β : Type} {f : State → State} {specB : Spec β} {specA : Spec α}
    (g : α → β)
    (hok : HookOk f specB)
    (hpre : ∀ x R s0, s0.mem ⊨ specA.pre x s0 ∗ R → s0.mem ⊨ specB.pre (g x) s0 ∗ R)
    (hpost : ∀ x R s0 sf,
      s0.mem ⊨ specA.pre x s0 ∗ R →
      sf.mem ⊨ specB.post (g x) s0 sf ∗ R →
      sf.mem ⊨ specA.post x s0 sf ∗ R)
    (hpan : ∀ x R s0 sf, sf.mem ⊨ specB.onPanic (g x) s0 sf ∗ R →
      sf.mem ⊨ specA.onPanic x s0 sf ∗ R := by intros _ _ _ _ h; exact h)
    (hexit : ∀ x code R s0 sf, sf.mem ⊨ specB.onExit (g x) code s0 sf ∗ R →
      sf.mem ⊨ specA.onExit x code s0 sf ∗ R := by intros _ _ _ _ _ h; exact h)
    (hoom : ∀ x R s0 sf, sf.mem ⊨ specB.onOom (g x) s0 sf ∗ R →
      sf.mem ⊨ specA.onOom x s0 sf ∗ R := by intros _ _ _ _ h; exact h) :
    HookOk f specA := by
  intro x R s0 hrun hp hsp
  rcases hok (g x) R s0 hrun (hpre x R s0 hp) hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hq⟩ | ⟨hst, hq⟩ | ⟨code, hst, hq⟩ | ⟨hst, hq⟩⟩
  · exact ⟨hkf, hsym, Or.inl ⟨hret, hcc, hpost x R s0 (f s0) hp hq⟩⟩
  · exact ⟨hkf, hsym, Or.inr (Or.inl ⟨hst, hpan x R s0 (f s0) hq⟩)⟩
  · exact ⟨hkf, hsym, Or.inr (Or.inr (Or.inl ⟨code, hst, hexit x code R s0 (f s0) hq⟩))⟩
  · exact ⟨hkf, hsym, Or.inr (Or.inr (Or.inr ⟨hst, hoom x R s0 (f s0) hq⟩))⟩

private theorem hookSat_shim_pqxdh {ext : String → Option (State → State)}
    (h : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" SignalSession.CliExt.shimSpec) :
    HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" pqxdhShimSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, hookOk_map_ext id hok (fun _ _ _ hp => hp) (fun _ _ _ _ _ hq => hq)⟩

private theorem hookSat_memcpy_pqxdh {ext : String → Option (State → State)}
    (h : HookSat ext "memcpy" SignalSession.CliExt.memcpySpec) :
    HookSat ext "memcpy" pqxdhMemcpyRegionExtSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, hookOk_map_ext (fun x => x) hok ?_ ?_⟩
  · rintro ⟨dst, src, bs⟩ R s0 hpre
    simp only [pqxdhMemcpyRegionExtSpec, SignalSession.CliExt.memcpySpec, libcMemcpySpec,
      SignalSession.CliExt.memHookStack, allocHookStack, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hlt⟩, hmem⟩
    have hx2_nat : (s0.readReg64 .x2).toNat = bs.length := by
      rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    exact ⟨⟨hx0, hx1, hx2_nat⟩, by ac_nf at hmem ⊢⟩
  · rintro ⟨dst, src, bs⟩ R s0 sf _ hpost
    simp only [pqxdhMemcpyRegionExtSpec, SignalSession.CliExt.memcpySpec, libcMemcpySpec,
      SignalSession.CliExt.memHookStack, allocHookStack, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem⟩
    exact ⟨hp, by ac_nf at hmem ⊢⟩

theorem pqxdh_shim_ok_at_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hH : PqxdhHookContractsExt P A img ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k) pqxdhShimSpec :=
  hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol])
    (hookSat_shim_pqxdh hH.shim)

theorem pqxdh_memcpy_region_ok_at_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hH : PqxdhHookContractsExt P A img ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      pqxdhMemcpyRegionExtSpec :=
  hook_ok_at (hname := "memcpy") rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol])
    (hookSat_memcpy_pqxdh hH.memcpy)

theorem pqxdh_alloc_ok_at_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocHooks A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  hook_ok_at (hname := "__rustc::__rust_alloc") rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol]) hA.alloc

theorem pqxdh_dealloc_ok_at_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocHooks A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  hook_ok_at (hname := "__rustc::__rust_dealloc") rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol]) hA.dealloc

theorem pqxdh_panic_at_raw_vec_handle_error_ext {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::raw_vec::handle_error" := by fnoff_eq) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_handle_error_ext b ext name k hk

theorem pqxdh_panic_at_handle_alloc_error_ext {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by fnoff_eq) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_handle_alloc_error_ext b ext name k hk

theorem kyberDecaps_ok_at_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hH : PqxdhHookContractsExt P A img ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff kyberDecapsStub := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (kyberDecapsStubSpecExt P) :=
  hook_ok_at (hname := kyberDecapsStub) rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, kyberDecapsStub])
    hH.kyberDecaps

theorem ecPubKeyIsCanonical_call_ok_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hH : PqxdhHookContractsExt P A img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ecPubKeyIsCanonicalSym)
      (ecPubKeyIsCanonicalCallSpecExt P) := by
  obtain ⟨fnM, hfnM, hokM⟩ := hH.dalekMontToEd
  obtain ⟨fnT, hfnT, hokT⟩ := hH.dalekTorsionFree
  have hSub := CryptoVerification.E2E.Pqxdh.Shared.ecPubKeyIsCanonical_call_ok'_ext
    (P := toSignalPqxdhPrimitives P) (img := img)
    hWF.isCanonical_eq_isCanonicalRef hWF.montToEd_len
    ⟨fnM, hfnM, fun gm Rm sm hrunm hprem hspm =>
      hokM ⟨gm.inBytes, gm.signBit, gm.inPtr, gm.outPtr⟩ Rm sm hrunm hprem hspm⟩
    ⟨fnT, hfnT, fun gt Rt st hrunt hpret hspt =>
      hokT ⟨gt.inPtr, gt.inBytes⟩ Rt st hrunt hpret hspt⟩
  exact subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp =>
    hSub.mono_outcome ⟨g.keyPtr, g.keyBytes⟩ R s0 hpc hrun hpre hsp fun _ hout => hout

/-- Fast-path contract for `<Vec<u8>>::append_elements` (`0x1af54`) with stacked
`memcpy` (`allocHookStack = 4096` B below `s.sp - 48`). -/
def pqxdhVecAppendElementsFastSpecExt :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (vecHdr, vecPtr, srcPtr, bs) s =>
    ⌜s.readReg64 .x0 = vecHdr ∧ s.readReg64 .x1 = srcPtr ∧
      s.readReg64 .x2 = 32#64 ∧ bs.length = 32⌝ ∗
    (vecHdr ↦₆₄ 192#64) ∗ ((vecHdr + 8#64) ↦₆₄ vecPtr) ∗ ((vecHdr + 16#64) ↦₆₄ 128#64) ∗
    memRegion (vecPtr + 128#64) bs.length ∗ (srcPtr ↦ₛ bs) ∗
    stackAt (s.sp - 48#64) allocHookStack ∗ cells (s.sp - 48#64) 6
  post := fun (vecHdr, vecPtr, srcPtr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (vecHdr ↦₆₄ 192#64) ∗ ((vecHdr + 8#64) ↦₆₄ vecPtr) ∗ ((vecHdr + 16#64) ↦₆₄ 160#64) ∗
    ((vecPtr + 128#64) ↦ₛ bs) ∗ (srcPtr ↦ₛ bs) ∗
    stackAt (s0.sp - 48#64) allocHookStack ∗ cells (s0.sp - 48#64) 6

theorem vecAppendElements_fast_ok_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hH : PqxdhHookContractsExt P A img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Shared.vecAppendElementsSym)
      pqxdhVecAppendElementsFastSpecExt := by
  unfold pqxdhVecAppendElementsFastSpecExt
  cells_unfold
  have hfn : libsignalSessionCode.fnOff Shared.vecAppendElementsSym = 0x1af54 :=
    libsignalSessionCode_fnOff_0x1af54
  have hmemcpy := pqxdh_memcpy_region_ok_at_ext hH
    (name := Shared.vecAppendElementsSym) (k := num% (ls_off% "memcpy" - 0x1af54))
    (by rw [hfn, (ls_stub% "memcpy")])
  dsimp only [pqxdhMemcpyRegionExtSpec] at hmemcpy
  code_fetches CryptoVerification.libsignalSessionCode Shared.vecAppendElements img.base
    (Rust.withPanics ext) hfn 0x1af54 88
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨vecHdr, vecPtr, srcPtr, bs⟩ := x
  dsimp only at *
  subst h_1 h_2
  wp_steps
  rw [← h]
  wp_call hmemcpy ⟨vecPtr + 128#64, s0.readReg64 (.gpr 1#5), bs⟩
  simp only [h] at *
  wp_steps
  wp_done

def pqxdhCalculateAgreementBaseSpecExt (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64) where
  pre := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s =>
    ⌜s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧ s.readReg64 .x8 = ret ∧ s.sp = sp ∧
      ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗
    (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗ memRegion ret 24 ∗ A.pool ∗
      stackAt sp calculateAgreementStackExt
  post := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
      pqxdhCalculateAgreementResultAt P A ret ourSk32 theirPk32 ∗ A.pool ∗
      stackAt sp calculateAgreementStackExt
  onPanic := rustPanicOnOom img

def pqxdhCalculateAgreementSpecExt (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64) where
  pre := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s =>
    ⌜s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧ s.readReg64 .x8 = ret ∧ s.sp = sp ∧
      ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗
    (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗ memRegion ret 24 ∗ A.pool ∗
      stackAt sp calculateAgreementStackExt ∗
      ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8)
  post := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
      pqxdhCalculateAgreementResultAt P A ret ourSk32 theirPk32 ∗ A.pool ∗
      stackAt sp calculateAgreementStackExt ∗
      ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8)
  onPanic := rustPanicOnOom img

def PqxdhCalculateAgreementOkExt (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr calculateAgreementSym)
    (pqxdhCalculateAgreementSpecExt P A img)

theorem allowPanic_hag_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image} {s0 s : State}
    {F R : SepProp} {x : BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64}
    (htr : s.trace = s0.trace) :
    ∀ sf, sf.status = .Panicked →
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))
        sf ((pqxdhCalculateAgreementSpecExt P A img).onPanic x s sf ∗ F) := by
  intro sf _ hm; dsimp only [pqxdhCalculateAgreementSpecExt, rustPanicOnOom] at hm
  exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm

theorem SepWPp_call_hag_ext {prog : Program} {ret : BitVec 64} {s : State} {P_pre : SepProp}
    {Q Qp : State → SepProp → Prop} {s0 : State} {F : SepProp} {entry ret_pc : BitVec 64}
    {P : Primitives} {A : RustAlloc} {img : Obj.Image} (hWF : StructuralPrims P)
    (hag : subroutine_ok prog (entry + 110016#64) (pqxdhCalculateAgreementSpecExt P A img))
    (hF : FrozenRo img s.mem) (ourA : BitVec 64) (our : Bytes) (theirA : BitVec 64) (their : Bytes)
    (hpc : s.pc = entry + 110016#64) (hrun : s.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hsp_eq : s.sp = s0.sp - 4944#64)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hx : s.readReg64 Reg.x0 = ourA ∧ s.readReg64 Reg.x1 = theirA ∧
      s.readReg64 Reg.x8 = s0.sp - 4912#64 ∧ s.sp = s0.sp - 4944#64 ∧
      our.length = 32 ∧ their.length = 32)
    (hP : P_pre = ((ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗
      memRegion (s0.sp - 4912#64) 24 ∗ A.pool ∗
      stackAt (s0.sp - 4944#64) calculateAgreementStackExt ∗
      ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8)) ∗ F)
    (hpanic : ∀ sf, sf.status = .Panicked →
      Qp sf ((pqxdhCalculateAgreementSpecExt P A img).onPanic
        (ourA, our, theirA, their, s0.sp - 4912#64, s0.sp - 4944#64) s sf ∗ F))
    (herr : P.x25519 our their = List.replicate 32 0 →
      ∀ (sf : State) (hi : BitVec 56) (u2 : BitVec 64), sf.pc = ret_pc → sf.status = .Running →
        sf.sp = s0.sp - 4944#64 → CalleeSavedPreserved s sf → sf.trace = s0.trace →
        SepWPp prog ret sf (((s0.sp - 4912#64) ↦₆₄ 1#64) ∗ ((s0.sp - 4904#64) ↦₆₄ (hi ++ 3#8)) ∗
          ((s0.sp - 4896#64) ↦₆₄ u2) ∗ (ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗
          A.pool ∗ stackAt (s0.sp - 4944#64) calculateAgreementStackExt ∗
          ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗ F) Q Qp)
    (hok : P.x25519 our their ≠ List.replicate 32 0 →
      ∀ (sf : State) (dh_ptr : BitVec 64), sf.pc = ret_pc → sf.status = .Running →
        sf.sp = s0.sp - 4944#64 → CalleeSavedPreserved s sf → sf.trace = s0.trace →
        FrozenRo img sf.mem →
        SepWPp prog ret sf (((s0.sp - 4912#64) ↦₆₄ 0#64) ∗ ((s0.sp - 4904#64) ↦₆₄ dh_ptr) ∗
          ((s0.sp - 4896#64) ↦₆₄ 32#64) ∗ (dh_ptr ↦ₛ bytesToBv8 (P.x25519 our their)) ∗
          A.live dh_ptr 32 1 ∗ (ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗
          A.pool ∗ stackAt (s0.sp - 4944#64) calculateAgreementStackExt ∗
          ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗ F) Q Qp) :
    SepWPp prog ret s P_pre Q Qp := by
  refine SepWPp.call_frame_keepsFrozen
    (x := (ourA, our, theirA, their, s0.sp - 4912#64, s0.sp - 4944#64))
    hag hpc hrun (spAligned_sub_4944 hsp_align hsp_eq) hlr rfl hx hP
    (fun _ _ _ _ hm => allowPanic_not_exited hm) hpanic
    (fun sf hpc_f hrun_f hsp_f hcs_f hkf_f => ?_)
  dsimp only [pqxdhCalculateAgreementSpecExt, pqxdhCalculateAgreementResultAt]
  rw [htr, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_sf => ?_
  by_cases hdh : P.x25519 our their = List.replicate 32 0
  · simp only [hdh, ↓reduceIte, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    refine SepWPp.fold (calcErr_entails_at_sub4912 s0.sp) (by sep_focus) ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun u2 => ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun hi => ?_
    simp only [sepConj_assoc]
    exact herr hdh sf hi u2 hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f htr_sf
  · have hdh_bv_len : (bytesToBv8 (P.x25519 our their)).length = 32 := by
      simp [bytesToBv8, hWF.x25519_len our their]
    simp only [hdh, ↓reduceIte, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    refine SepWPp.fold (boxSliceU8_32_entails_at_sub4912 A s0.sp hdh_bv_len) (by sep_focus) ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun dh_ptr => ?_
    simp only [sepConj_assoc]
    exact hok hdh sf dh_ptr hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f htr_sf (hF.of_keepsFrozen hkf_f)

theorem subStack_to_alloc_ext (sp : BitVec 64) :
    stackAt (sp - 4944#64) (pqxdhHookStackExt + 400) =
      memRegion (sp - 21728#64) 12688 ∗ stackAt (sp - 4944#64) allocHookStack := by
  simp only [stackAt, pqxdhHookStackExt, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - 4944#64 - BitVec.ofNat 64 16784) (n := 12688) (k := 4096)
    (b' := sp - 4944#64 - BitVec.ofNat 64 4096) rfl (by bv_omega) (by decide)]
  have h1 : sp - 4944#64 - BitVec.ofNat 64 16784 = sp - 21728#64 := by bv_omega
  rw [h1]

theorem subStack_to_calc_ext (sp : BitVec 64) :
    stackAt (sp - 4944#64) (pqxdhHookStackExt + 400) =
      memRegion (sp - 21728#64) 176 ∗ stackAt (sp - 4944#64) calculateAgreementStackExt := by
  simp only [stackAt, pqxdhHookStackExt, calculateAgreementStackExt, calculateAgreementSubStackExt]
  rw [ProofLib.memRegion_split' (b := sp - 4944#64 - BitVec.ofNat 64 16784) (n := 176) (k := 16608)
    (b' := sp - 4944#64 - BitVec.ofNat 64 16608) rfl (by bv_omega) (by decide)]
  have h1 : sp - 4944#64 - BitVec.ofNat 64 16784 = sp - 21728#64 := by bv_omega
  rw [h1]

theorem subStack_to_vecAppend_ext (sp : BitVec 64) :
    stackAt (sp - 4944#64) (pqxdhHookStackExt + 400) =
      memRegion (sp - 21728#64) 12640 ∗ stackAt (sp - 4992#64) allocHookStack ∗
        cells (sp - 4992#64) 6 := by
  simp only [stackAt, pqxdhHookStackExt, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - 4944#64 - BitVec.ofNat 64 16784) (n := 12640) (k := 4144)
      (b' := sp - 4992#64 - BitVec.ofNat 64 4096) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 4992#64 - BitVec.ofNat 64 4096) (n := 4096) (k := 48)
      (b' := sp - 4992#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (sp - 4992#64) 6 (by decide) : memRegion (sp - 4992#64) 48 = cells (sp - 4992#64) 6)]
  have hb : sp - 4944#64 - BitVec.ofNat 64 16784 = sp - 21728#64 := by bv_omega
  rw [hb]

theorem stackAt_pqxdh_accept_top_ext (sp : BitVec 64) :
    stackAt sp pqxdhEntryStackExt =
      memRegion (sp - 32768#64) 11040 ∗ stackAt (sp - 4944#64) (pqxdhHookStackExt + 400) ∗
        cells (sp - 4944#64) 4 ∗ memRegion (sp - 4912#64) 3168 ∗
        memRegion (sp - 1744#64) 1568 ∗ memRegion (sp - 176#64) 96 ∗ cells (sp - 80#64) 10 := by
  simp only [stackAt, pqxdhEntryStackExt, pqxdhHookStackExt]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 32768) (n := 11040) (k := 21728)
      (b' := sp - 21728#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 21728#64) (n := 16784) (k := 4944)
      (b' := sp - 4944#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 4944#64) (n := 32) (k := 4912)
      (b' := sp - 4912#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 4912#64) (n := 3168) (k := 1744)
      (b' := sp - 1744#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 1744#64) (n := 1568) (k := 176)
      (b' := sp - 176#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 176#64) (n := 96) (k := 80)
      (b' := sp - 80#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (sp - 4944#64) 4 (by decide) : memRegion (sp - 4944#64) 32 = cells (sp - 4944#64) 4),
    (memRegion_cells (sp - 80#64) 10 (by decide) : memRegion (sp - 80#64) 80 = cells (sp - 80#64) 10)]
  have h1 : sp - 4944#64 - BitVec.ofNat 64 16784 = sp - 21728#64 := by bv_omega
  have h2 : sp - BitVec.ofNat 64 32768 = sp - 32768#64 := rfl
  rw [h1, h2]

theorem alloc_to_calc_stack_ext (sp : BitVec 64) :
    memRegion (sp - 21728#64) 12688 ∗ stackAt (sp - 4944#64) allocHookStack =
      memRegion (sp - 21728#64) 176 ∗ stackAt (sp - 4944#64) calculateAgreementStackExt := by
  rw [← subStack_to_alloc_ext sp, subStack_to_calc_ext sp]

theorem calc_to_alloc_stack_ext (sp : BitVec 64) :
    memRegion (sp - 21728#64) 176 ∗ stackAt (sp - 4944#64) calculateAgreementStackExt =
      memRegion (sp - 21728#64) 12688 ∗ stackAt (sp - 4944#64) allocHookStack :=
  (alloc_to_calc_stack_ext sp).symm

theorem calc_to_vecAppend_stack_ext (sp : BitVec 64) :
    memRegion (sp - 21728#64) 176 ∗ stackAt (sp - 4944#64) calculateAgreementStackExt =
      memRegion (sp - 21728#64) 12640 ∗ stackAt (sp - 4992#64) allocHookStack ∗
        cells (sp - 4992#64) 6 := by
  rw [← subStack_to_calc_ext sp, subStack_to_vecAppend_ext sp]

theorem vecAppend_to_alloc_stack_ext (sp : BitVec 64) :
    memRegion (sp - 21728#64) 12640 ∗ stackAt (sp - 4992#64) allocHookStack ∗
      cells (sp - 4992#64) 6 =
      memRegion (sp - 21728#64) 12688 ∗ stackAt (sp - 4944#64) allocHookStack := by
  rw [← subStack_to_vecAppend_ext sp, subStack_to_alloc_ext sp]

theorem alloc_to_decaps_stack_ext (sp : BitVec 64) :
    memRegion (sp - 21728#64) 12688 ∗ stackAt (sp - 4944#64) allocHookStack =
      memRegion (sp - 21728#64) 400 ∗ stackAt (sp - 4944#64) pqxdhHookStackExt := by
  rw [← subStack_to_alloc_ext sp]
  simp only [stackAt, pqxdhHookStackExt]
  rw [ProofLib.memRegion_split' (b := sp - 4944#64 - BitVec.ofNat 64 16784) (n := 400) (k := 16384)
    (b' := sp - 4944#64 - BitVec.ofNat 64 16384) rfl (by bv_omega) (by decide)]
  have h1 : sp - 4944#64 - BitVec.ofNat 64 16784 = sp - 21728#64 := by bv_omega
  rw [h1]

theorem decaps_to_alloc_stack_ext (sp : BitVec 64) :
    memRegion (sp - 21728#64) 400 ∗ stackAt (sp - 4944#64) pqxdhHookStackExt =
      memRegion (sp - 21728#64) 12688 ∗ stackAt (sp - 4944#64) allocHookStack :=
  (alloc_to_decaps_stack_ext sp).symm

theorem stack_to_kdf_ext (sp : BitVec 64) :
    memRegion (sp - 32768#64) 11040 ∗ memRegion (sp - 21728#64) 12688 ∗
      stackAt (sp - 4944#64) allocHookStack =
      memRegion (sp - 32768#64) 3248 ∗ stackAt (sp - 4944#64) pqxdhHkdfStackExt := by
  simp only [stackAt, allocHookStack, pqxdhHkdfStackExt]
  rw [← sepConj_assoc,
    ← ProofLib.memRegion_split' (b := sp - 32768#64) (n := 11040) (k := 12688)
      (b' := sp - 21728#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := sp - 32768#64) (n := 23728) (k := 4096)
      (b' := sp - 4944#64 - BitVec.ofNat 64 4096) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 32768#64) (n := 3248) (k := 24576)
      (b' := sp - 4944#64 - BitVec.ofNat 64 24576) rfl (by bv_omega) (by decide)]

theorem subStack_to_alloc_of_eq_ext (sp sp' : BitVec 64) (h : sp' = sp - 4944#64) :
    memRegion (sp - 21728#64) 12688 ∗ stackAt sp' allocHookStack ⊢
      stackAt (sp - 4944#64) (pqxdhHookStackExt + 400) := by
  rw [h, ← subStack_to_alloc_ext sp]; exact Entails.refl _

theorem alloc_to_calc_stack_of_eq_ext (sp sp' : BitVec 64) (h : sp' = sp - 4944#64) :
    memRegion (sp - 21728#64) 12688 ∗ stackAt sp' allocHookStack ⊢
      memRegion (sp - 21728#64) 176 ∗ stackAt (sp - 4944#64) calculateAgreementStackExt := by
  rw [h, alloc_to_calc_stack_ext sp]; exact Entails.refl _

theorem vecAppend_to_alloc_stack_of_eq_ext (sp sp' : BitVec 64) (h : sp' = sp - 4992#64) :
    memRegion (sp - 21728#64) 12640 ∗ stackAt sp' allocHookStack ∗ cells sp' 6 ⊢
      memRegion (sp - 21728#64) 12688 ∗ stackAt (sp - 4944#64) allocHookStack := by
  rw [h, vecAppend_to_alloc_stack_ext sp]; exact Entails.refl _

theorem decaps_to_alloc_stack_of_eq_ext (sp sp' : BitVec 64) (h : sp' = sp - 4944#64) :
    memRegion (sp - 21728#64) 400 ∗ stackAt sp' pqxdhHookStackExt ⊢
      memRegion (sp - 21728#64) 12688 ∗ stackAt (sp - 4944#64) allocHookStack := by
  rw [h, decaps_to_alloc_stack_ext sp]; exact Entails.refl _

def pqxdhAcceptFieldsSpecExt (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec AcceptFieldsCallGhost := Spec.inImage {
    pre := fun (g : AcceptFieldsCallGhost) s =>
      ⌜s.readReg64 .x0 = g.argPtr ∧ s.readReg64 .x8 = g.outPtr ∧ g.inp.trustedPeer = true ∧
        g.inp.replayOk = true ∧ g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
        WellSizedAcceptKeysInput g.inp⌝ ∗
        pqxdhAcceptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
        memRegion g.outPtr 104 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s.sp pqxdhEntryStackExt ∗
        A.pool
    post := fun (g : AcceptFieldsCallGhost) s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗ pqxdhAcceptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
        (match Model.acceptKeys P g.inp with
       | some drKey =>
         g.outPtr ↦ₛ bytesToBv8 (handshakeKeysResultOk104 drKey)
       | none =>
         pqxdhAcceptErrStrong2At g.outPtr ∗ anyHeap) ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
         stackAt s0.sp pqxdhEntryStackExt ∗ A.pool
    onPanic := rustPanicOnOom img
  } img

def pqxdhAcceptOptFieldsSpecExt (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec AcceptFieldsCallGhost := Spec.inImage {
    pre := fun (g : AcceptFieldsCallGhost) s =>
      ⌜s.readReg64 .x0 = g.argPtr ∧ s.readReg64 .x8 = g.outPtr ∧ g.inp.trustedPeer = true ∧
        g.inp.replayOk = true ∧ g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
        WellSizedAcceptKeysInput g.inp⌝ ∗
        pqxdhAcceptOptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
        memRegion g.outPtr 104 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s.sp pqxdhEntryStackExt ∗
        A.pool
    post := fun (g : AcceptFieldsCallGhost) s0 sf => ⌜sf.trace = s0.trace⌝ ∗
        pqxdhAcceptOptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
        (match Model.acceptKeys P g.inp with
       | some drKey =>
         g.outPtr ↦ₛ bytesToBv8 (handshakeKeysResultOk104 drKey)
       | none =>
         pqxdhAcceptErrStrong2At g.outPtr ∗ anyHeap) ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
          stackAt s0.sp pqxdhEntryStackExt ∗ A.pool
    onPanic := rustPanicOnOom img
  } img

set_option maxHeartbeats 48000000 in
/-- Generalized `Pqxdh::accept` (`0x23920`) optional-fields contract on `tripleRatchetProgAtExt`
(`pqxdhEntryStackExt = 32768` B). -/
theorem pqxdhAccept_opt_fields_base_ok_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : PqxdhHookContractsExt P A img ext)
    (hext : PqxdhHkdfExtractOk_ext P img ext) (hexp : PqxdhHkdfExpandMultiInfoOk_ext P img ext)
    (hag : PqxdhCalculateAgreementOkExt P A img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpecExt P A img) := by
  have hb := base_aligned_of_loads himg; have hA := hH.alloc
  refine subroutine_ok_inImage_rodata4 (rodata_0x7c604 himg) (rodata_0x7c267 himg) (rodata_0x7ff6a
    himg) (rodata_0x81028 himg) ?_; unfold rustPanicOnOom
  have hfn : libsignalSessionCode.fnOff pqxdhAcceptSym = 0x23920 :=
    libsignalSessionCode_fnOff_0x23920
  have hcanon := subroutine_ok_rel_pqxdh_ext (ecPubKeyIsCanonical_call_ok_ext hWF hH)
    libsignalSessionCode_fnOff_0x3dd44 hfn (k := 107556) (by decide)
  have hag' := subroutine_ok_rel_pqxdh_ext hag libsignalSessionCode_fnOff_0x3e6e0 hfn (k :=
    110016) (by decide)
  have hvec_append := subroutine_ok_rel_pqxdh_ext (vecAppendElements_fast_ok_ext hH)
    libsignalSessionCode_fnOff_0x1af54 hfn (k := 18446744073709516340) (by decide)
  have hext_none := subroutine_ok_rel_pqxdh_ext hext.1 libsignalSessionCode_fnOff_0x1ad38 hfn (k :=
    18446744073709515800) (by decide)
  have hexp' := subroutine_ok_rel_pqxdh_ext (hexp 12) libsignalSessionCode_fnOff_0x1a874 hfn (k :=
    18446744073709514580) (by decide)
  simp only [pqxdhHkdfExpandCellsSpecExt, pqxdhHkdfExpandCellsSpecAt, cells, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  have hshim := pqxdh_shim_ok_at_ext hH
    (name := pqxdhAcceptSym)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x23920))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := pqxdh_alloc_ok_at_ext (b := img.base) hH.alloc
    (name := pqxdhAcceptSym) (k := num% (ls_off% "__rustc::__rust_alloc" - 0x23920))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  have hdealloc := pqxdh_dealloc_ok_at_ext (b := img.base) hH.alloc
    (name := pqxdhAcceptSym) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x23920))
    (by rw [hfn, (ls_stub% "__rustc::__rust_dealloc")])
  have hmemcpy := pqxdh_memcpy_region_ok_at_ext hH
    (name := pqxdhAcceptSym) (k := num% (ls_off% "memcpy" - 0x23920))
    (by rw [hfn, (ls_stub% "memcpy")])
  have hdecaps := kyberDecaps_ok_at_ext hH
    (name := pqxdhAcceptSym)
    (k := num% (ls_off% "libcrux_ml_kem::mlkem1024::kyber::decapsulate" - 0x23920))
    (by rw [hfn, (ls_stub% "libcrux_ml_kem::mlkem1024::kyber::decapsulate")])
  have hpan_rawvec := pqxdh_panic_at_raw_vec_handle_error_ext (b := img.base) (ext := ext)
    (name := pqxdhAcceptSym) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x23920))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hpan_alloc := pqxdh_panic_at_handle_alloc_error_ext (b := img.base) (ext := ext)
    (name := pqxdhAcceptSym) (k := num% (ls_off% "alloc::alloc::handle_alloc_error" - 0x23920))
    (by rw [hfn, (ls_stub% "alloc::alloc::handle_alloc_error")])
  have hadrp_fa8_1 : (((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym +
    220#64 &&& 0xfffffffffffff000#64) + bv% (ls_str% "incoming base key is invalid" - 0x23000)) =
      img.base + bv% (ls_str% "incoming base key is invalid") := by
    rw [Program.fnAddr_rebase, hfn]; exact accept_adrp_55604_1 hb
  have hadrp_fa8_2 : (((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym +
    220#64 &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_str% "incoming base key is invalid") - 0x23000) +
      bv% ((ls_str% "incoming base key is invalid") % 4096)) =
      img.base + bv% (ls_str% "incoming base key is invalid") := by
    rw [Program.fnAddr_rebase, hfn]; exact accept_adrp_55604_2 hb
  have hadrp_dbf_1 : (((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym +
    1064#64 &&& 0xfffffffffffff000#64) +
      bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024" - 0x23000)) =
      img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
    rw [Program.fnAddr_rebase, hfn]; exact accept_adrp_55267_1 hb
  have hadrp_dbf_2 : (((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym +
    1064#64 &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") - 0x23000) +
      bv% ((ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") % 4096)) =
      img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
    rw [Program.fnAddr_rebase, hfn]; exact accept_adrp_55267_2 hb
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.E2E.Pqxdh.pqxdhAccept
    img.base (Rust.withPanics ext) hfn 0x23920 1728
  dsimp only [tripleRatchetProgAtExt]
    at hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps hpan_rawvec
       hpan_alloc hadrp_fa8_1 hadrp_fa8_2 hadrp_dbf_1 hadrp_dbf_2 ⊢
  clear himg hag hext hexp hA hH hfn hb
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    pqxdhAcceptSym = entry
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches; wpp_init x s0
  rcases x with ⟨inp, argPtr, pqskPtr, ctSlicePtr, ctBufPtr, outPtr⟩; dsimp only at *
  subst ‹s0.readReg64 (.gpr 0#5) = argPtr› ‹s0.readReg64 (.gpr 8#5) = outPtr›
  have hws : WellSizedAcceptKeysInput inp := ‹WellSizedAcceptKeysInput inp›
  rcases hws with ⟨hikBSk, _hikBPk, hspkBSk, _hspkBPk, _hopk_sz, hpqSk, _hpqPk, hikAPk, hekAPk,
    hkemCt⟩; rw (occs := .pos [1]) [stackAt_pqxdh_accept_top_ext s0.sp]
  refine SepWPp.fold (Entails.of_eq (pqsk_region_phaseA_split s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells4_sub4944_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells10_sub80_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; have hF0 : FrozenRo img s0.mem := ‹FrozenRo img s0.mem›
  unfold pqxdhAcceptOptFieldsAt; refine SepWPp.of_sepWP_frozen hF0 (mid := entry + 52#64) ?_
  wp_steps; wp_call hcanon ⟨s0.readReg64 (.gpr 0#5) + 160#64, inp.hdr.ekAPk⟩
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF1; try simp only [arm64_norm] at hF1
  cases hcanon_b : P.isCanonical inp.hdr.ekAPk
  · have hacc_none : acceptKeys P inp = none :=
      acceptKeys_eq_none_of_not_canonical P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
        hikAPk hekAPk hcanon_b; have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = false := hcanon_b
    simp only [hcanon_ec, Bool.false_eq_true, ↓reduceIte] at *; rw [subStack_to_alloc_ext s0.sp]
    refine SepWPp.of_sepWP (mid := entry + 216#64) ?_; wp_steps; wp_call hshim (); wp_steps
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call halloc (28, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs) (fun halloc0 htr0 =>
      ?_) (fun halloc0 halign0 htr0 => ?_)
    · refine SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x23920)) ?_; wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
        (by sep_focus) ?_; sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (incoming_alloc_split _)) (by sep_focus) ?_
      sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (rodata_incoming_split1
        (img.base + bv% (ls_str% "incoming base key is invalid"))))
        (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
      wp_simp_pre_fast [hadrp_fa8_1, hadrp_fa8_2, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps; refine SepWP.fold (Entails.of_eq (rodata_incoming_1_to_2
        (img.base + bv% (ls_str% "incoming base key is invalid"))))
        (by sep_focus) ?_; wp_steps
      refine SepWP.fold (Entails.of_eq (rodata_incoming_split2
        (img.base + bv% (ls_str% "incoming base key is invalid"))).symm)
        (by sep_focus) ?_; refine SepWP.fold (incoming_overlap_prep _ _ _) (by sep_focus) ?_
      sep_elim_exists'; wp_steps; refine SepWP.fold (err28_anyHeap_intro A _ _ _) (by sep_focus) ?_
      refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5)) 0x8000000000000018#64
        _ _ _ _ (by decide)) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (pqsk_region_phaseA_merge s0.sp _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top_ext s0.sp).symm) (by sep_focus) ?_
      rw [hacc_none]
      clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
        hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done
  · have hsp_align_eq : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_align
    have hsp_orr1 : (s0.sp - 4912#64) ||| 1#64 = s0.sp - 4911#64 := sp_sub4912_orr_one hsp_align_eq
    have hsp_orr2 : (s0.sp - 1744#64) ||| 1#64 = s0.sp - 1743#64 := sp_sub1744_orr_one hsp_align_eq
    obtain ⟨ss, hss, hss_len, hfit_ss⟩ := kyberDecaps_some_and_fitBv8_eq hWF hpqSk hkemCt
    have hdecaps_some : (P.kemDecaps inp.pqspkBSk inp.hdr.kemCt).isSome = true := by simp [hss]
    have hss_bv_len : (bytesToBv8 ss).length = 32 := by simp [bytesToBv8, hss_len]
    have hpqSk_drop_len : ((bytesToBv8 inp.pqspkBSk).drop 1).length = 3167 := by
      simp [bytesToBv8, hpqSk]
    have hkemCt_drop_len : ((bytesToBv8 inp.hdr.kemCt).drop 1).length = 1567 := by
      simp [bytesToBv8, hkemCt]
    obtain ⟨s0_w, s1_w, s2_w, s3_w, -, hss_cells⟩ := exists_unpack64_of_length_32 hss_bv_len
    have hro_dbf : infoPqxdh = INFO_PQXDH := by rfl_kernel
    have hinfo_len : BitVec.ofNat 64 INFO_PQXDH.length = 46#64 := by rfl_kernel
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = true := hcanon_b
    simp only [hcanon_ec, ↓reduceIte] at hpost; rw [subStack_to_alloc_ext s0.sp]
    refine SepWPp.of_sepWP_frozen hF1 (mid := entry + 72#64) ?_; wp_steps; wp_call hshim ()
    wp_steps; have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call halloc (192, 1)
    apply SepWP.done (by wp_norm_goal)
      (by wp_norm_goal); intro hF2; try simp only [arm64_norm] at hF2
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs) (fun halloc192 htr192 =>
      ?_) (fun halloc192 halign192 htr192 => ?_)
    · refine SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x23920)) ?_; wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (memRegion_192_init_split _)) (by sep_focus) ?_
      sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (alloc_to_calc_stack_ext s0.sp)) (by sep_focus) ?_
      refine SepWPp.of_sepWP_frozen hF2 (mid := entry + 110016#64) ?_; wp_steps
      refine SepWP.fold (Entails.of_eq (pointsTo64_4_allOnes_eq_F_X25519 _)) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal)
        (by wp_norm_goal); intro hF3; try simp only [arm64_norm] at hF3
      refine SepWPp_call_hag_ext hWF hag' hF3 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
        (s0.readReg64 (.gpr 0#5) + 128#64) inp.hdr.ikAPk (by wp_norm_lhs) (by wp_norm_lhs) hsp_align
        (by wp_norm_lhs) (ret_pc := entry + 120#64) (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hikAPk⟩
        (by sep_focus) (allowPanic_hag_ext (by wp_norm_lhs))
        (fun hdh1 sf1 hi1 u2_1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
        (fun hdh1 sf1 dh1_ptr hpc1 hrun1 hsp1 hcs1 htr1 hF4 => ?_)
      · have hacc_none : acceptKeys P inp = none :=
          acceptKeys_eq_none_of_dh1_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true› hikAPk
          hekAPk hcanon_b hdh1; dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
          hcs29⟩
        simp only [arm64_norm] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29
        refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
          (by sep_focus) ?_; sep_elim_exists'
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack_ext s0.sp)) (by sep_focus) ?_
        refine SepWPp.fold (vec_err_dh1_merge _) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
        wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
        refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
        refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
          0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
        refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (subStack_to_alloc_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top_ext s0.sp).symm)
          (by sep_focus) ?_
        rw [hacc_none]
        clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
          hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done
      · have hdh1_len : (P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 32 := hWF.x25519_len _ _
        have hdh1_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)).length = 32 := by
          simp [bytesToBv8, hdh1_len]
        have hpfx1_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 64 := by
          simp [F_X25519, hdh1_len]
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
          hcs29⟩
        simp only [arm64_norm] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack_ext s0.sp)) (by sep_focus) ?_
        refine SepWPp.of_sepWP_frozen hF4 (mid := entry + 110016#64) ?_; wp_steps
        wp_call hmemcpy ⟨_, dh1_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)⟩
        refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        wp_steps
        refine SepWP.fold (hdh1_bv_len ▸ pointsToBytes_entails_memRegion dh1_ptr _)
          (by sep_focus) ?_; wp_call hdealloc (dh1_ptr, 32, 1); wp_steps
        refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh1_ptr 32#64) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ F_X25519 (P.x25519 inp.spkBSk
          inp.hdr.ikAPk) 32 (by decide))) (by sep_focus) ?_
        refine SepWP.fold (alloc_to_calc_stack_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        apply SepWP.done (by wp_norm_goal)
          (by wp_norm_goal); intro hF5; try simp only [arm64_norm] at hF5
        refine SepWPp_call_hag_ext hWF hag' hF5 (s0.readReg64 (.gpr 0#5) + 32#64) inp.ikBSk
          (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
          (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc :=
          entry + 304#64) (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hikBSk, hekAPk⟩
          (by sep_focus) (allowPanic_hag_ext (by wp_norm_lhs))
          (fun hdh2 sf2 hi2 u2_2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
          (fun hdh2 sf2 dh2_ptr hpc2 hrun2 hsp2 hcs2 htr2 hF6 => ?_)
        · have hacc_none : acceptKeys P inp = none :=
            acceptKeys_eq_none_of_dh2_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
            hikAPk hekAPk hcanon_b hdh1 hdh2; dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
               hcs2_29
          refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
            (by sep_focus) ?_; sep_elim_exists'
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack_ext s0.sp)) (by sep_focus) ?_
          refine SepWPp.fold (vec_err_dh2_merge _ hpfx1_len) (by sep_focus) ?_
          apply SepWPp.of_sepWP_ret; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
          refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
          refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
            0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
          refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (subStack_to_alloc_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top_ext s0.sp).symm)
            (by sep_focus) ?_
          rw [hacc_none]
          clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
            hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done
        · have hdh2_len : (P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
          have hdh2_bv_len : (bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)).length = 32 := by
            simp [bytesToBv8, hdh2_len]
          have hpfx2_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
            P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 96 := by simp [F_X25519, hdh1_len, hdh2_len]
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
               hcs2_29
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack_ext s0.sp)) (by sep_focus) ?_
          refine SepWPp.of_sepWP_frozen hF6 (mid := entry + 110016#64) ?_; wp_steps
          wp_call hmemcpy ⟨_, dh2_ptr, bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)⟩
          refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          wp_steps
          refine SepWP.fold (hdh2_bv_len ▸ pointsToBytes_entails_memRegion dh2_ptr _)
            (by sep_focus) ?_; wp_call hdealloc (dh2_ptr, 32, 1); wp_steps
          refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh2_ptr 32#64)
            (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
            P.x25519 inp.spkBSk inp.hdr.ikAPk) (P.x25519 inp.ikBSk inp.hdr.ekAPk) 64
            (by simp only [bytesToBv8, List.length_map, hpfx1_len]))) (by sep_focus) ?_
          refine SepWP.fold (alloc_to_calc_stack_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          apply SepWP.done (by wp_norm_goal)
            (by wp_norm_goal); intro hF7; try simp only [arm64_norm] at hF7
          refine SepWPp_call_hag_ext hWF hag' hF7 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
            (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
            (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc :=
            entry + 404#64) (by wp_norm_lhs) (by wp_norm_lhs)
            ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hekAPk⟩
            (by sep_focus) (allowPanic_hag_ext (by wp_norm_lhs))
            (fun hdh3 sf3 hi3 u2_3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
            (fun hdh3 sf3 dh3_ptr hpc3 hrun3 hsp3 hcs3 htr3 hF8 => ?_)
          · have hacc_none : acceptKeys P inp = none :=
              acceptKeys_eq_none_of_dh3_zero P inp ‹inp.trustedPeer = true› ‹inp.replayOk = true›
              hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
            dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
                 hcs3_29
            refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
              (by sep_focus) ?_; sep_elim_exists'
            refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack_ext s0.sp)) (by sep_focus) ?_
            refine SepWPp.fold (vec_err_dh3_merge _ hpfx2_len) (by sep_focus) ?_
            apply SepWPp.of_sepWP_ret; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
            refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
            refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
              0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
            refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (subStack_to_alloc_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top_ext s0.sp).symm)
              (by sep_focus) ?_; rw [hacc_none]
            clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
              hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done
          · have hdh3_len : (P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
            have hdh3_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)).length = 32 := by
              simp [bytesToBv8, hdh3_len]
            have hpfx3_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
              P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 128 :=
              by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len]
            dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
                 hcs3_29
            cases hopk_eq : inp.opkBSk? with
            | none =>
              have hikm160_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                ss).length = 160 := by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, hss_len]
              have hikm160_bv : BitVec.ofNat 64 (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                ss).length = 160#64 := by rw [hikm160_len]
              have hacc_some : acceptKeys P inp = some (Model.deriveDRKeys P (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss)) :=
                acceptKeys_eq_some_of_opk_none P inp ss ‹inp.trustedPeer = true›
                ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hss
              have hprk160_len : (bytesToBv8 (hkdfExtractRef P none (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss))).length = 32 := by
                simp [bytesToBv8, hkdfExtractRef_length]
              have hprk160_len32 : (hkdfExtractRef P none (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss)).length = 32 :=
                hkdfExtractRef_length P none _
              obtain ⟨p0, p1, p2, p3, -, hprk160⟩ := exists_unpack64_of_length_32 hprk160_len
              obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm160, hout160⟩ :=
                exists_unpack64_hkdfDerive96 P hWF (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss)
              simp only [Bool.false_eq_true, ↓reduceIte, emp_sepConj]
              refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack_ext s0.sp)) (by sep_focus) ?_
              refine SepWPp.of_sepWP_frozen hF8 (mid := entry + 944#64) ?_; wp_steps
              wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              wp_steps
              refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
                (by sep_focus) ?_; wp_call hdealloc (dh3_ptr, 32, 1)
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk) (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
                (by simp only [bytesToBv8, List.length_map, hpfx2_len]))) (by sep_focus) ?_
              refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp 0#64 dh3_ptr 32#64 0#64)
                (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (pqsk_region_phaseB_split s0.sp)) (by sep_focus) ?_
              sep_elim_exists'
              refine SepWP.fold (Entails.of_eq (kemct_region_phaseB_split s0.sp)) (by sep_focus) ?_
              sep_elim_exists'
              refine SepWP.fold (Entails.of_eq (sub176_split_32_64 s0.sp)) (by sep_focus) ?_
              sep_elim_exists'; wp_steps
              wp_call hmemcpy ⟨s0.sp - 4911#64, pqskPtr + 1#64, (bytesToBv8 inp.pqspkBSk).drop 1⟩
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              wp_steps
              wp_call hmemcpy ⟨s0.sp - 1743#64, ctBufPtr + 2#64, (bytesToBv8 inp.hdr.kemCt).drop 1⟩
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              refine SepWP.fold (pqsk_head_tail_merge s0.sp hpqSk) (by sep_focus) ?_
              refine SepWP.fold (kemct_head_tail_merge s0.sp hkemCt) (by sep_focus) ?_; wp_steps
              refine SepWP.fold (Entails.of_eq (alloc_to_decaps_stack_ext s0.sp)) (by sep_focus) ?_
              wp_call hdecaps ⟨s0.sp - 4912#64, inp.pqspkBSk, s0.sp - 1744#64, inp.hdr.kemCt,
                s0.sp - 176#64⟩
              refine SepWP.fold (decaps_to_alloc_stack_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              wp_steps; wp_call hshim (); wp_steps; wp_call halloc (32, 1)
              apply SepWP.done (by wp_norm_goal)
                (by wp_norm_goal); intro hF9; try simp only [arm64_norm] at hF9
              refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
                (fun halloc32 htr32 => ?_) (fun halloc32 halign32 htr32 => ?_)
              · refine SepWPp.of_sepWP
                  (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - 0x23920)) ?_
                wp_steps
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
                exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
              · (conv => arg 4; rw [hfit_ss, ss_sub176_eq s0.sp hss_cells, hro_dbf])
                refine SepWPp.fold (pqsk_to_extract_region s0.sp hpqSk) (by sep_focus) ?_
                refine SepWPp.fold (kemct_to_hmac18_region s0.sp hkemCt) (by sep_focus) ?_
                sep_elim_exists'
                refine SepWPp.fold (Entails.of_eq (ss_and_vec128_split _ _)) (by sep_focus) ?_
                sep_elim_exists'; apply SepWPp.of_sepWP_ret; apply SepWP.of_sepWP_frozen hF9
                wp_steps
                refine SepWP.fold (cells4_to_memRegion32 _ s0_w s1_w s2_w s3_w) (by sep_focus) ?_
                wp_call hdealloc (_, 32, 1)
                refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (ss_vec_add128_merge _ hss_cells) (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk) ss 128 (by simp only [bytesToBv8,
                  List.length_map, hpfx3_len]))) (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (stack_to_kdf_ext s0.sp)) (by sep_focus) ?_; wp_steps
                apply SepWP.checkpoint_frozen (by wp_norm_lhs)
                  (by wp_norm_lhs); intro hF10; try simp only [arm64_norm] at hF10
                wp_call hext_none (s0.sp - 4912#64, _, F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss, s0.sp - 4944#64)
                refine SepWP.fold (vec_ok_160_merge _ hikm160_len) (by sep_focus) ?_
                refine SepWP.fold (prk_sub4912_eq s0.sp hprk160) (by sep_focus) ?_
                try (conv => arg 4; simp only [bv_sub_add_lit', BitVec.reduceSub])
                refine SepWP.fold (hmacCore_split_sub4880 P s0.sp _) (by sep_focus) ?_
                sep_elim_exists'; refine SepWP.pure_left_elim fun hhmac160 => ?_; wp_steps
                apply SepWP.done_frozen (by wp_norm_lhs)
                  (by wp_norm_lhs); intro hF11; try simp only [arm64_norm] at hF11
                refine SepWP.fold (hmacState_merge_sub1744 P s0.sp _ hhmac160) (by sep_focus) ?_
                (conv => arg 4; simp only [hadrp_dbf_1, hadrp_dbf_2, arm64_norm, ← hinfo_len])
                wp_call hexp' (s0.sp - 1744#64, hkdfExtractRef P none (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ ss), s0.sp - 4912#64,
                  img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"),
                  INFO_PQXDH, s0.sp - 176#64, s0.sp - 4944#64); sep_elim_exists'
                try (conv => arg 4; simp only [bv_sub_add_lit', BitVec.reduceSub])
                refine SepWP.fold (Entails.of_eq (stack_to_kdf_ext s0.sp).symm) (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (outPtr_ok104_cells_split (s0.readReg64 (.gpr
                  8#5)))) (by sep_focus) ?_; sep_elim_exists'
                refine SepWP.fold (okm_sub176_eq s0.sp hokm160) (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (sub1680_split_32_48 s0.sp)) (by sep_focus) ?_
                sep_elim_exists'; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
                refine SepWP.fold (outPtr_ok104_cells_merge (s0.readReg64 (.gpr 8#5)) hout160)
                  (by sep_focus) ?_
                refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (sub4912_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (sub1744_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
                  (by sep_focus) ?_
                refine SepWP.fold (sub176_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
                  (by sep_focus) ?_
                refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (subStack_to_alloc_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top_ext s0.sp).symm)
                  (by sep_focus) ?_; (conv => arg 4; rw [← hro_dbf]); rw [hacc_some]
                clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
                  hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done
            | some opkSk =>
              have hopkSk : opkSk.length = 32 := _hopk_sz opkSk hopk_eq; simp only [↓reduceIte]
              refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack_ext s0.sp)) (by sep_focus) ?_
              refine SepWPp.of_sepWP_frozen hF8 (mid := entry + 110016#64) ?_; wp_steps
              wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              wp_steps
              refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
                (by sep_focus) ?_; wp_call hdealloc (dh3_ptr, 32, 1)
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              wp_steps; refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh3_ptr 32#64)
                (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk) (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
                (by simp only [bytesToBv8, List.length_map, hpfx2_len]))) (by sep_focus) ?_
              refine SepWP.fold (alloc_to_calc_stack_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              apply SepWP.done (by wp_norm_goal)
                (by wp_norm_goal); intro hF8_1; try simp only [arm64_norm] at hF8_1
              refine SepWPp_call_hag_ext hWF hag' hF8_1 (s0.readReg64 (.gpr 0#5) + 265#64) opkSk
                (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
                (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc :=
                entry + 720#64) (by wp_norm_lhs) (by wp_norm_lhs)
                ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hopkSk, hekAPk⟩
                (by sep_focus) (allowPanic_hag_ext (by wp_norm_lhs))
                (fun hdh4 sf4 hi4 u2_4 hpc4 hrun4 hsp4 hcs4 htr4 => ?_)
                (fun hdh4 sf4 dh4_ptr hpc4 hrun4 hsp4 hcs4 htr4 hF8_2 => ?_)
              · have hacc_none : acceptKeys P inp = none :=
                  acceptKeys_eq_none_of_dh4_zero P inp opkSk ‹inp.trustedPeer = true›
                  ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                  ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hdh4
                dsimp only [CalleeSavedPreserved, Reg.fp] at hcs4
                rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25,
                  hcs4_26, hcs4_27, hcs4_28, hcs4_29⟩
                simp only [arm64_norm]
                  at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28
                     hcs4_29
                refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
                  (by sep_focus) ?_; sep_elim_exists'
                refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack_ext s0.sp)) (by sep_focus) ?_
                refine SepWPp.fold (vec_err_dh4_merge _ hpfx3_len) (by sep_focus) ?_
                apply SepWPp.of_sepWP_ret; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
                refine SepWP.fold (emp_entails_anyHeap) (by sep_focus) ?_
                refine SepWP.fold (outPtr_err104_strong2_merge (s0.readReg64 (.gpr 8#5))
                  0x800000000000000a#64 _ _ _ _ (by decide)) (by sep_focus) ?_
                refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (subStack_to_alloc_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top_ext s0.sp).symm)
                  (by sep_focus) ?_; rw [hacc_none]
                clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy hdecaps
                  hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done
              · have hdh4_len : (P.x25519 opkSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
                have hdh4_bv_len : (bytesToBv8 (P.x25519 opkSk inp.hdr.ekAPk)).length = 32 := by
                  simp [bytesToBv8, hdh4_len]
                have hpfx4_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                  P.x25519 opkSk inp.hdr.ekAPk).length = 160 := by
                  simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, hdh4_len]
                have hikm192_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                  P.x25519 opkSk inp.hdr.ekAPk ++ ss).length = 192 := by
                  simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, hdh4_len, hss_len]
                have hikm192_bv : BitVec.ofNat 64 (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                  P.x25519 opkSk inp.hdr.ekAPk ++ ss).length = 192#64 := by rw [hikm192_len]
                have hacc_some : acceptKeys P inp = some (Model.deriveDRKeys P (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss)) :=
                  acceptKeys_eq_some_of_opk_some P inp opkSk ss ‹inp.trustedPeer = true›
                  ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                  ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hdh4 hss
                have hprk192_len : (bytesToBv8 (hkdfExtractRef P none (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++
                  ss))).length = 32 := by simp [bytesToBv8, hkdfExtractRef_length]
                have hprk192_len32 : (hkdfExtractRef P none (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss)).length =
                  32 := hkdfExtractRef_length P none _
                obtain ⟨p0, p1, p2, p3, -, hprk192⟩ := exists_unpack64_of_length_32 hprk192_len
                obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm192, hout192⟩ :=
                  exists_unpack64_hkdfDerive96 P hWF (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss)
                dsimp only [CalleeSavedPreserved, Reg.fp] at hcs4
                rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25,
                  hcs4_26, hcs4_27, hcs4_28, hcs4_29⟩
                simp only [arm64_norm]
                  at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28
                     hcs4_29
                refine SepWPp.fold (Entails.of_eq (calc_to_vecAppend_stack_ext s0.sp))
                  (by sep_focus) ?_
                refine SepWPp.of_sepWP_frozen hF8_2 (mid := entry + 944#64) ?_; wp_steps
                wp_call hvec_append (s0.sp - 4936#64, _, dh4_ptr,
                  bytesToBv8 (P.x25519 opkSk inp.hdr.ekAPk))
                refine SepWP.fold (vecAppend_to_alloc_stack_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                wp_steps
                refine SepWP.fold (hdh4_bv_len ▸ pointsToBytes_entails_memRegion dh4_ptr _)
                  (by sep_focus) ?_; wp_call hdealloc (dh4_ptr, 32, 1)
                refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                  P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk) (P.x25519 opkSk inp.hdr.ekAPk) 128
                  (by simp only [bytesToBv8, List.length_map, hpfx3_len]))) (by sep_focus) ?_
                refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp 0#64 dh4_ptr 32#64 0#64)
                  (by sep_focus) ?_
                refine SepWP.fold (Entails.of_eq (pqsk_region_phaseB_split s0.sp)) (by sep_focus) ?_
                sep_elim_exists'
                refine SepWP.fold (Entails.of_eq (kemct_region_phaseB_split s0.sp))
                  (by sep_focus) ?_; sep_elim_exists'
                refine SepWP.fold (Entails.of_eq (sub176_split_32_64 s0.sp)) (by sep_focus) ?_
                sep_elim_exists'; wp_steps
                wp_call hmemcpy ⟨s0.sp - 4911#64, pqskPtr + 1#64, (bytesToBv8 inp.pqspkBSk).drop 1⟩
                refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                wp_steps; wp_call hmemcpy ⟨s0.sp - 1743#64, ctBufPtr + 2#64,
                  (bytesToBv8 inp.hdr.kemCt).drop 1⟩
                refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (pqsk_head_tail_merge s0.sp hpqSk) (by sep_focus) ?_
                refine SepWP.fold (kemct_head_tail_merge s0.sp hkemCt) (by sep_focus) ?_; wp_steps
                refine SepWP.fold (Entails.of_eq (alloc_to_decaps_stack_ext s0.sp))
                  (by sep_focus) ?_
                wp_call hdecaps ⟨s0.sp - 4912#64, inp.pqspkBSk, s0.sp - 1744#64, inp.hdr.kemCt,
                  s0.sp - 176#64⟩
                refine SepWP.fold (decaps_to_alloc_stack_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                wp_steps; wp_call hshim (); wp_steps; wp_call halloc (32, 1)
                apply SepWP.done (by wp_norm_goal)
                  (by wp_norm_goal); intro hF9; try simp only [arm64_norm] at hF9
                refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
                  (fun halloc32 htr32 => ?_) (fun halloc32 halign32 htr32 => ?_)
                · refine SepWPp.of_sepWP
                    (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - 0x23920)) ?_
                  wp_steps
                  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
                  apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
                  exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
                · (conv => arg 4; rw [hfit_ss, ss_sub176_eq s0.sp hss_cells, hro_dbf])
                  refine SepWPp.fold (pqsk_to_extract_region s0.sp hpqSk) (by sep_focus) ?_
                  refine SepWPp.fold (kemct_to_hmac18_region s0.sp hkemCt) (by sep_focus) ?_
                  sep_elim_exists'
                  refine SepWPp.fold (Entails.of_eq (ss_and_vec160_split _ _)) (by sep_focus) ?_
                  sep_elim_exists'; apply SepWPp.of_sepWP_ret; apply SepWP.of_sepWP_frozen hF9
                  wp_steps
                  refine SepWP.fold (cells4_to_memRegion32 _ s0_w s1_w s2_w s3_w) (by sep_focus) ?_
                  wp_call hdealloc (_, 32, 1)
                  refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                  · simp only [arm64_norm, *]
                  refine SepWP.fold (ss_vec_add160_merge _ hss_cells) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
                    P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                    P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk) ss 160
                    (by simp only [bytesToBv8, List.length_map, hpfx4_len]))) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (stack_to_kdf_ext s0.sp)) (by sep_focus) ?_
                  wp_steps
                  apply SepWP.checkpoint_frozen (by wp_norm_lhs)
                    (by wp_norm_lhs); intro hF10; try simp only [arm64_norm] at hF10
                  wp_call hext_none (s0.sp - 4912#64, _, F_X25519 ++
                    P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                    P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss,
                    s0.sp - 4944#64)
                  refine SepWP.fold (vec_ok_192_merge _ hikm192_len) (by sep_focus) ?_
                  refine SepWP.fold (prk_sub4912_eq s0.sp hprk192) (by sep_focus) ?_
                  try (conv => arg 4; simp only [bv_sub_add_lit', BitVec.reduceSub])
                  refine SepWP.fold (hmacCore_split_sub4880 P s0.sp _) (by sep_focus) ?_
                  sep_elim_exists'; refine SepWP.pure_left_elim fun hhmac192 => ?_; wp_steps
                  apply SepWP.done_frozen (by wp_norm_lhs)
                    (by wp_norm_lhs); intro hF11; try simp only [arm64_norm] at hF11
                  refine SepWP.fold (hmacState_merge_sub1744 P s0.sp _ hhmac192) (by sep_focus) ?_
                  (conv => arg 4; simp only [hadrp_dbf_1, hadrp_dbf_2, arm64_norm, ← hinfo_len])
                  wp_call hexp' (s0.sp - 1744#64, hkdfExtractRef P none (F_X25519 ++
                    P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                    P.x25519 inp.spkBSk inp.hdr.ekAPk ++ P.x25519 opkSk inp.hdr.ekAPk ++ ss),
                    s0.sp - 4912#64,
                    img.base + bv% (ls_str% "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"),
                    INFO_PQXDH, s0.sp - 176#64, s0.sp - 4944#64); sep_elim_exists'
                  try (conv => arg 4; simp only [bv_sub_add_lit', BitVec.reduceSub])
                  refine SepWP.fold (Entails.of_eq (stack_to_kdf_ext s0.sp).symm) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (outPtr_ok104_cells_split (s0.readReg64 (.gpr
                    8#5)))) (by sep_focus) ?_; sep_elim_exists'
                  refine SepWP.fold (okm_sub176_eq s0.sp hokm192) (by sep_focus) ?_
                  refine SepWP.fold (Entails.of_eq (sub1680_split_32_48 s0.sp)) (by sep_focus) ?_
                  sep_elim_exists'; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
                  refine SepWP.fold (outPtr_ok104_cells_merge (s0.readReg64 (.gpr 8#5)) hout192)
                    (by sep_focus) ?_
                  refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
                  refine SepWP.fold (sub4912_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    _ _ _ _ _) (by sep_focus) ?_
                  refine SepWP.fold (sub1744_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
                    (by sep_focus) ?_
                  refine SepWP.fold (sub176_post_kdf_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
                    (by sep_focus) ?_
                  refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
                    (by sep_focus) ?_
                  refine SepWP.fold (subStack_to_alloc_of_eq_ext s0.sp _ ?_) (by sep_focus) ?_
                  · simp only [arm64_norm, *]
                  refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top_ext s0.sp).symm)
                    (by sep_focus) ?_; (conv => arg 4; rw [← hro_dbf]); rw [hacc_some]
                  clear hcanon hag' hvec_append hext_none hexp' hshim halloc hdealloc hmemcpy
                    hdecaps hpan_rawvec hpan_alloc; simp only [sepConj_assoc, *]; wp_done

private theorem pqxdhAcceptFieldsAt_eq_optFieldsAt_frame (basePtr pqskPtr ctSlicePtr ctBufPtr :
    BitVec 64) (inp : AcceptKeysInput) :
    pqxdhAcceptFieldsAt basePtr pqskPtr ctSlicePtr ctBufPtr inp =
      pqxdhAcceptOptFieldsAt basePtr pqskPtr ctSlicePtr ctBufPtr inp ∗
        (match inp.opkBSk? with
         | some _ => .emp
         | none => (basePtr + 265#64) ↦ₛ bytesToBv8 (List.replicate 32 0)) := by
  unfold pqxdhAcceptFieldsAt pqxdhAcceptOptFieldsAt
  cases inp.opkBSk? <;> (simp only [Option.getD, emp_sepConj, sepConj_emp]; try ac_rfl)

theorem pqxdhAccept_fields_base_ok_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : PqxdhHookContractsExt P A img ext)
    (hext : PqxdhHkdfExtractOk_ext P img ext) (hexp : PqxdhHkdfExpandMultiInfoOk_ext P img ext)
    (hag : PqxdhCalculateAgreementOkExt P A img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptFieldsSpecExt P A img) := by
  have hopt := pqxdhAccept_opt_fields_base_ok_ext himg hWF hH hext hexp hag
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp => ?_
  let F_opk : SepProp :=
    match g.inp.opkBSk? with
    | some _ => .emp
    | none => ((g.argPtr + 265#64) ↦ₛ bytesToBv8 (List.replicate 32 0))
  have hpre' : s0.mem ⊨ (pqxdhAcceptOptFieldsSpecExt P A img).pre g s0 ∗ (F_opk ∗ R) := by
    dsimp only [pqxdhAcceptFieldsSpecExt, pqxdhAcceptOptFieldsSpecExt, Spec.inImage, F_opk] at hpre ⊢
    rw [pqxdhAcceptFieldsAt_eq_optFieldsAt_frame] at hpre
    ac_nf at hpre ⊢
  refine hopt.mono_outcome g (F_opk ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hexit, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [pqxdhAcceptFieldsSpecExt, pqxdhAcceptOptFieldsSpecExt, Spec.inImage, F_opk] at hq ⊢
    rw [pqxdhAcceptFieldsAt_eq_optFieldsAt_frame]
    ac_nf at hq ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [pqxdhAcceptFieldsSpecExt, pqxdhAcceptOptFieldsSpecExt, Spec.inImage,
      rustPanicOnOom] at hq ⊢
    exact allowPanic_frame (fun h => h) (by simpa only [sepConj_assoc] using hq)
  · simp only [pqxdhAcceptOptFieldsSpecExt, Spec.inImage, sepConj_assoc,
      satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · simp only [pqxdhAcceptOptFieldsSpecExt, Spec.inImage, sepConj_assoc,
      satisfies_pure_sepConj] at hq
    exact hq.1.elim

end Ext

end CryptoVerification.E2E.Pqxdh.ResponderCore
