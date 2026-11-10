/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.Defs
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem alloc_fnOff : libsignalSessionCode.fnOff allocName = num% (ls_off% "__rustc::__rust_alloc") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "__rustc::__rust_alloc")

theorem decodeErrorFrom_fnOff : libsignalSessionCode.fnOff decodeErrorFromName = num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")

theorem varintSlow_fnOff : libsignalSessionCode.fnOff varintSlowName = num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")

private theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

private theorem hookSat_tripleRatchetExterns_trap (C : Crypto)
    (abs : String → Option (State → State)) {sym : String} {spec : Spec α}
    (heq : trTrapExterns C abs sym = abs sym)
    (h : HookSat abs sym spec) :
    HookSat (trTrapExterns C abs) sym spec := by
  unfold HookSat at *; rwa [heq]

private theorem hookSat_tripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) {sym : String} {spec : Spec α}
    (heq : tripleRatchetExterns C ctl abs sym = abs sym)
    (h : HookSat abs sym spec) :
    HookSat (tripleRatchetExterns C ctl abs) sym spec := by
  unfold HookSat at *; rwa [heq]

private theorem panic_at_handle_alloc_error_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by simp only [arm64_norm]) :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol (hname := "alloc::alloc::handle_alloc_error") rfl hk
    (by rw [(ls_stub% "alloc::alloc::handle_alloc_error")]; decide)
    (fun H => by rw [(ls_stub% "alloc::alloc::handle_alloc_error")]; exact (ls_hook% "alloc::alloc::handle_alloc_error") H)
    (by decide +kernel)

private theorem panic_at_handle_alloc_error {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by simp only [arm64_norm]) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked := by
  have h := panic_at_handle_alloc_error_trap (b := b) (C := C) (abs := abs) hk
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  rcases (trapsOnly_trTrap_kit b C ctl abs).hook ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) with
    heq | ⟨f, hf, ht⟩
  · exact heq.symm.trans h
  · cases h.symm.trans hf
    exact False.elim (ht default (ProofLib.Variant.OutcomeStatus.of_panicked rfl))

private theorem shim_ok_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl hk
    (by rw [(ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]; decide)
    (fun H => by rw [(ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]; exact (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2") H)
    (by decide +kernel)
    ⟨hookNoop, rfl, sessionShim_hookOk⟩

private theorem shim_ok_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (shim_ok_at_trap hk)

private theorem alloc_ok_at_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff allocName := by simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  hook_ok_at (hname := allocName) rfl hk
    (by rw [alloc_fnOff]; decide)
    (fun H => by rw [alloc_fnOff]; exact (ls_hook% "__rustc::__rust_alloc") H)
    (by decide +kernel)
    (hookSat_tripleRatchetExterns_trap C abs rfl hA.alloc)

private theorem alloc_ok_at {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff allocName := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (alloc_ok_at_trap hA hk)

theorem memRegion_split (a : BitVec 64) (n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion a (n + k) = memRegion a n ∗ memRegion (a + BitVec.ofNat 64 n) k :=
  IsBlock.eq (IsBlock.memRegion a (n + k))
    ((IsBlock.memRegion a n).sepConj (IsBlock.memRegion _ k) rfl h)
    fun _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩

theorem memRegion_eight (a : BitVec 64) : memRegion a 8 = ∃∗ v, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem pointsTo64_entails_memRegion8 (a v : BitVec 64) : (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [memRegion_eight]
  exact Entails.sepExists_intro v

theorem memRegion_cells (a : BitVec 64) (k : Nat) (h : 8 * k ≤ 2 ^ 64) :
    memRegion a (8 * k) = cells a k := by
  induction k generalizing a with
  | zero => exact memRegion_zero a
  | succ k ih =>
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, memRegion_split a 8 (8 * k) (by omega),
      memRegion_eight, ih _ (by omega), cells_succ, sepExists_sepConj_left]

theorem stackAt_split_cells (sp : BitVec 64) (n k : Nat) (h : n + 8 * k ≤ 2 ^ 64) :
    stackAt sp (n + 8 * k) =
      stackAt (sp - BitVec.ofNat 64 (8 * k)) n ∗ cells (sp - BitVec.ofNat 64 (8 * k)) k := by
  simp only [stackAt]
  rw [memRegion_split _ n (8 * k) h, memRegion_cells _ k (by omega)]
  generalize hj : 8 * k = j at *
  have e1 : sp - BitVec.ofNat 64 (n + j) = sp - BitVec.ofNat 64 j - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + j) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 j := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

theorem allocFailedIn_of_eq {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem stackAt_decodeErrorFrom (sp : BitVec 64) :
    stackAt sp decodeErrorHookStack =
      stackAt (sp - 4128#64) 4064 ∗
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 := by
  have h1 : stackAt sp decodeErrorHookStack =
      stackAt (sp - 32#64) (4064 + allocHookStack) ∗ cells (sp - 32#64) 4 :=
    stackAt_split_cells sp (4064 + allocHookStack) 4 (by decide)
  have h2 : stackAt (sp - 32#64) (4064 + allocHookStack) =
      stackAt (sp - 4128#64) 4064 ∗ stackAt (sp - 32#64) allocHookStack := by
    simp only [stackAt, allocHookStack]
    rw [memRegion_split _ 4064 4096 (by decide)]
    have e1 : sp - 32#64 - BitVec.ofNat 64 (4064 + 4096) = sp - 4128#64 - 4064#64 := by
      bv_lin
    have e2 : sp - 32#64 - BitVec.ofNat 64 (4064 + 4096) + 4064#64 = sp - 32#64 - 4096#64 := by
      bv_lin
    rw [e2, e1]
  rw [h1, h2, sepConj_assoc]

theorem memRegion_40_cells (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
       ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64,
        (a ↦₆₄ u4) ∗ ((a + 8#64) ↦₆₄ u3) ∗ ((a + 16#64) ↦₆₄ u2) ∗
        ((a + 24#64) ↦₆₄ u1) ∗ ((a + 32#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 32 (by decide),
    memRegion_split (a + 8#64) 8 24 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_48_cells (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
       ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ w : BitVec 64,
        (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ u4) ∗ ((a + 16#64) ↦₆₄ u3) ∗
        ((a + 24#64) ↦₆₄ u2) ∗ ((a + 32#64) ↦₆₄ u1) ∗ ((a + 40#64) ↦₆₄ u0)) := by
  rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide),
    memRegion_eight a, memRegion_40_cells (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_72_cells (a : BitVec 64) :
    memRegion a 72 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
       ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
       ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗ u8 : BitVec 64,
        (a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u7) ∗ ((a + 16#64) ↦₆₄ u6) ∗
        ((a + 24#64) ↦₆₄ u5) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u3) ∗
        ((a + 48#64) ↦₆₄ u2) ∗ ((a + 56#64) ↦₆₄ u1) ∗ ((a + 64#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 64 (by decide),
    memRegion_split (a + 8#64) 8 56 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_40_cells (a + 8#64 + 8#64 + 8#64 + 8#64),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private def decodeErrorFromSpec0 (A : RustAlloc) : Spec (BitVec 64 × BitVec 64) where
  pre := (decodeErrorFromSpec A).pre
  post := fun (k, w) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.trace = s0.trace ∧ KindNoHeap w⌝ ∗
      A.live (sf.readReg64 .x0) 72 8 ∗
      ((sf.readReg64 .x0) ↦₆₄ 0#64) ∗
      ((sf.readReg64 .x0 + 8#64) ↦₆₄ 8#64) ∗
      ((sf.readReg64 .x0 + 16#64) ↦₆₄ 0#64) ∗
      ((sf.readReg64 .x0 + 24#64) ↦₆₄ w) ∗
      memRegion (sf.readReg64 .x0 + 32#64) 40 ∗
      memRegion k 48 ∗
      A.pool ∗ stackAt s0.sp decodeErrorHookStack
  onPanic := (decodeErrorFromSpec A).onPanic

private theorem decodeErrorFromSpec0_post_satisfies (A : RustAlloc)
    (x : BitVec 64 × BitVec 64) (R : SepProp) (s0 sf : State)
    (hm : sf.mem ⊨ (decodeErrorFromSpec0 A).post x s0 sf ∗ R) :
    sf.mem ⊨ (decodeErrorFromSpec A).post x s0 sf ∗ R := by
  rcases x with ⟨k, w⟩
  simp only [decodeErrorFromSpec0, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hne, htr, hkind⟩, hm⟩
  simp only [decodeErrorFromSpec, decodeErrorAtStackLen, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hne, htr⟩, ?_⟩
  have hm' : sf.mem ⊨
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        vecAt A 32 8 stackEntryAt (sf.readReg64 .x0) cap ptr (List.replicate 0 ())) ∗
      (∃∗ w' : BitVec 64, ⌜KindNoHeap w'⌝ ∗ ((sf.readReg64 .x0 + 24#64) ↦₆₄ w')) ∗
      (A.live (sf.readReg64 .x0) 72 8 ∗ memRegion (sf.readReg64 .x0 + 32#64) 40 ∗
        memRegion k 48 ∗ A.pool ∗ stackAt s0.sp decodeErrorHookStack ∗ R) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨w, 0#64, 8#64, ?_⟩
    simp only [vecAt, vecHeader, vecBuf, List.replicate, List.length_nil, BitVec.ofNat_eq_ofNat,
      ite_true, (by decide : (0#64 : BitVec 64).toNat = 0),
      (by decide : 0 ≤ 0 ∧ 0 * 32 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0),
      sepConj_emp, sepConj_assoc, true_and]
    have hm_pure : sf.mem ⊨ ⌜(8#64 : BitVec 64) ≠ 0#64⌝ ∗ ⌜KindNoHeap w⌝ ∗
        (((sf.readReg64 .x0) ↦₆₄ 0#64) ∗ ((sf.readReg64 .x0 + 8#64) ↦₆₄ 8#64) ∗
          ((sf.readReg64 .x0 + 16#64) ↦₆₄ 0#64) ∗ ((sf.readReg64 .x0 + 24#64) ↦₆₄ w) ∗
          A.live (sf.readReg64 .x0) 72 8 ∗ memRegion (sf.readReg64 .x0 + 32#64) 40 ∗
          memRegion k 48 ∗ A.pool ∗ stackAt s0.sp decodeErrorHookStack ∗ R) :=
      (satisfies_pure_sepConj _ _ _).mpr
        ⟨by decide, (satisfies_pure_sepConj _ _ _).mpr ⟨hkind, Satisfies.of_eq hm⟩⟩
    exact Satisfies.of_eq hm_pure
  exact Satisfies.of_eq hm' (by unfold vecOf; ac_rfl)

attribute [local irreducible] Program.fnOff

theorem decodeErrorFrom_ok_aux_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A) := by
  refine subroutine_ok_mono (spec := decodeErrorFromSpec0 A) ?_
    (fun _ _ _ h => h)
    (fun x R s0 sf h => decodeErrorFromSpec0_post_satisfies A x R s0 sf h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)
  simp only [decodeErrorFromSpec0, decodeErrorFromSpec,
    memRegion_40_cells, memRegion_48_cells, stackAt_decodeErrorFrom,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff decodeErrorFromName = num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") :=
    decodeErrorFrom_fnOff
  have hshim := shim_ok_at_trap (b := b) (C := C) (abs := abs)
    (name := decodeErrorFromName) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_trap (b := b) (C := C)
    (name := decodeErrorFromName) (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")) hA
    (by rw [hfn, alloc_fnOff])
  have hpanic := panic_at_handle_alloc_error_trap (b := b) (C := C) (abs := abs)
    (name := decodeErrorFromName) (k := num% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
    (by rw [hfn, (ls_stub% "alloc::alloc::handle_alloc_error")])
  code_fetches CryptoVerification.libsignalSessionCode
    varintSlowBin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")) 92
  dsimp only [trTrapProgAt] at hshim halloc hpanic ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr decodeErrorFromName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨k, w⟩ := x
  dsimp only at *
  obtain ⟨hk1, hk2⟩ := h
  have hpow2 : ∃ j, 8 = 2 ^ j := ⟨3, rfl⟩
  have hlay : LayoutOk 72 8 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (32))
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_72_cells,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
      SepWPp.exists_elim fun u4 => SepWPp.exists_elim fun u5 =>
      SepWPp.exists_elim fun u6 => SepWPp.exists_elim fun u7 =>
      SepWPp.exists_elim fun u8 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem decodeErrorFrom_ok_aux (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr decodeErrorFromName]
  exact subroutine_ok_kit_of_trTrap (decodeErrorFrom_ok_aux_trap b C A abs hA)

theorem decodeErrorFrom_ok_at_varintSlow_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr varintSlowName - 11672#64)
      (decodeErrorFromSpec A) := by
  have heq : (trTrapProgAt b C abs).fnAddr varintSlowName - 11672#64 =
      (trTrapProgAt b C abs).fnAddr decodeErrorFromName := by
    simp only [trTrapProgAt, Program.fnAddr_rebase, varintSlow_fnOff, decodeErrorFrom_fnOff]
    bv_lin
  rw [heq]
  exact decodeErrorFrom_ok_aux_trap b C A abs hA

theorem decodeErrorFrom_ok_at_varintSlow (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr varintSlowName - 11672#64)
      (decodeErrorFromSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr varintSlowName]
  exact subroutine_ok_kit_of_trTrap (decodeErrorFrom_ok_at_varintSlow_trap b C A abs hA)

end CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow
