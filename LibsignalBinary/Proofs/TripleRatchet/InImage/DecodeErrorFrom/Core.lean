/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalTripleRatchetProofDefs

/-!
# Verification of In-Image `<DecodeError as From<DecodeErrorKind>>::from`

Proves that the compiled `DecodeError::from` implementation allocates a 72-byte `Box<Inner>`
with an empty context stack and satisfies `decodeErrorFromSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorFrom

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "alloc::alloc::handle_alloc_error")

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") → (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" + 88)]

/-! ## Local hook & memory helpers -/

theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

theorem noAllocShim_ok_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl hk
    (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    ⟨hookNoop, rfl, sessionShim_hookOk⟩

theorem noAllocShim_ok_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (noAllocShim_ok_at_trap hk)

theorem allocHooks_alloc_tripleRatchetExterns_trap (C : Crypto)
    (A : RustAlloc) (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    HookSat (Rust.withPanics (trTrapExterns C abs)) allocName (rustAllocSpec A) := by
  have habs := tripleRatchetExterns_abs C 0#64 abs
  have h4 : Rust.withPanics (trTrapExterns C abs) allocName = abs allocName :=
    (withPanics_trTrap_ne C abs (n := allocName) (by decide)).trans
      (Option.some.inj (congrArg (·[4]?) habs))
  simpa [HookSat, h4] using hA.alloc

theorem allocHooks_alloc_tripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (A : RustAlloc) (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    HookSat (Rust.withPanics (tripleRatchetExterns C ctl abs)) allocName (rustAllocSpec A) := by
  have ht := allocHooks_alloc_tripleRatchetExterns_trap C A abs hA
  have heq : Rust.withPanics (trTrapExterns C abs) allocName =
      Rust.withPanics (tripleRatchetExterns C ctl abs) allocName := by
    rw [withPanics_trTrap_ne C abs (n := allocName) (by decide)]
    unfold Rust.withPanics
    rw [tripleRatchetExterns_ctl C 0#64 ctl abs (n := allocName) (by decide)]
  unfold HookSat at ht ⊢
  rwa [← heq]

theorem alloc_ok_at_norm_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  hook_ok_at_raw (hname := "__rustc::__rust_alloc") rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm])
    (allocHooks_alloc_tripleRatchetExterns_trap C A abs hA)

theorem alloc_ok_at_norm {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (alloc_ok_at_norm_trap hA hk)

theorem panic_at_handle_alloc_error2_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by
        simp only [arm64_norm]) :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol (hname := "alloc::alloc::handle_alloc_error") rfl hk
    (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])

theorem panic_at_handle_alloc_error2 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by
        simp only [arm64_norm]) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked := by
  have h := panic_at_handle_alloc_error2_trap (b := b) (C := C) (abs := abs) hk
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  rcases (trapsOnly_trTrap_kit b C ctl abs).hook ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) with
    heq | ⟨f, hf, ht⟩
  · exact heq.symm.trans h
  · cases h.symm.trans hf
    exact False.elim (ht default (ProofLib.Variant.OutcomeStatus.of_panicked rfl))

theorem memRegion_zero (a : BitVec 64) : memRegion a 0 = emp := by
  have hb := IsBlock.pointsToBytes a []
  rw [pointsToBytes_nil] at hb
  exact IsBlock.eq (IsBlock.memRegion a 0) hb
    fun _ => ⟨fun _ => ⟨by simp, by simp⟩, fun _ => trivial⟩

theorem memRegion_eight (a : BitVec 64) : memRegion a 8 = ∃∗ v, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

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

theorem stackAt_decodeErrorFrom (sp : BitVec 64) :
    stackAt sp decodeErrorHookStack =
      memRegion (sp - 8192#64) 4064 ∗
        stackAt (sp - 32#64) allocHookStack ∗
        cells (sp - 32#64) 4 := by
  have h1 : stackAt sp decodeErrorHookStack =
      memRegion (sp - 8192#64) 4064 ∗ stackAt sp (allocHookStack + 32) :=
    ProofLib.stackAt_split_bottom sp (allocHookStack + 32) 4064 (by decide)
  have h2 : stackAt sp (allocHookStack + 32) =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 :=
    stackAt_split_cells sp 4096 4 (by decide)
  rw [h1, h2]

theorem allocFailedIn_of_eq {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

theorem memRegion_40_cells (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64,
        (a ↦₆₄ u4) ∗ ((a + 8#64) ↦₆₄ u3) ∗ ((a + 16#64) ↦₆₄ u2) ∗
        ((a + 24#64) ↦₆₄ u1) ∗ ((a + 32#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 32 (by decide),
    memRegion_split (a + 8#64) 8 24 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_72_cells (a : BitVec 64) :
    memRegion a 72 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
       ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗ u8 : BitVec 64,
        (a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u7) ∗ ((a + 16#64) ↦₆₄ u6) ∗
        ((a + 24#64) ↦₆₄ u5) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u3) ∗
        ((a + 48#64) ↦₆₄ u2) ∗ ((a + 56#64) ↦₆₄ u1) ∗ ((a + 64#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 64 (by decide),
    memRegion_split (a + 8#64) 8 56 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight,
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem cells5_entails_memRegion40 (a u4 u3 u2 u1 u0 : BitVec 64) :
    (a ↦₆₄ u4) ∗ ((a + 8#64) ↦₆₄ u3) ∗ ((a + 16#64) ↦₆₄ u2) ∗
      ((a + 24#64) ↦₆₄ u1) ∗ ((a + 32#64) ↦₆₄ u0) ⊢
      memRegion a 40 := by
  rw [memRegion_split a 8 32 (by decide),
    memRegion_split (a + 8#64) 8 24 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ u4)
    (sepConj_mono (pointsTo64_entails_memRegion _ u3)
      (sepConj_mono (pointsTo64_entails_memRegion _ u2)
        (sepConj_mono (pointsTo64_entails_memRegion _ u1)
          (pointsTo64_entails_memRegion _ u0))))

theorem cells6_entails_memRegion48 (a w u4 u3 u2 u1 u0 : BitVec 64) :
    (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ u4) ∗ ((a + 16#64) ↦₆₄ u3) ∗
      ((a + 24#64) ↦₆₄ u2) ∗ ((a + 32#64) ↦₆₄ u1) ∗ ((a + 40#64) ↦₆₄ u0) ⊢
      memRegion a 48 := by
  rw [memRegion_split a 8 40 (by decide)]
  refine sepConj_mono (pointsTo64_entails_memRegion a w) ?_
  have h40 := cells5_entails_memRegion40 (a + 8#64) u4 u3 u2 u1 u0
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h40

theorem vecOf_nil_entails (A : RustAlloc) (e : BitVec 64) :
    (e ↦₆₄ 0#64) ∗ ((e + 8#64) ↦₆₄ 8#64) ∗ ((e + 16#64) ↦₆₄ 0#64) ⊢
      vecOf A 32 8 stackEntryAt e [] := by
  unfold vecOf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
  unfold vecAt vecHeader vecBuf
  have hpure : ([] : List Unit).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 32 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0 := by decide
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  have hlen : BitVec.ofNat 64 ([] : List Unit).length = 0#64 := rfl
  simp only [hlen, h0, ↓reduceIte, sepConj_emp]
  rw [sepConj_comm _ ⌜_⌝]
  exact Entails.pure_right hpure (Entails.refl _)

theorem decodeErrorWith_zero_entails (A : RustAlloc) (e w u4 u3 u2 u1 u0 : BitVec 64)
    (hw : KindNoHeap w) :
    A.live e 72 8 ∗
      (e ↦₆₄ 0#64) ∗ ((e + 8#64) ↦₆₄ 8#64) ∗ ((e + 16#64) ↦₆₄ 0#64) ∗
      ((e + 24#64) ↦₆₄ w) ∗ ((e + 32#64) ↦₆₄ u4) ∗ ((e + 40#64) ↦₆₄ u3) ∗
      ((e + 48#64) ↦₆₄ u2) ∗ ((e + 56#64) ↦₆₄ u1) ∗ ((e + 64#64) ↦₆₄ u0) ⊢
      decodeErrorAtStackLen A e 0 := by
  unfold decodeErrorAtStackLen
  dsimp only [List.replicate]
  have hvec := vecOf_nil_entails A e
  have hkind : ((e + 24#64) ↦₆₄ w) ⊢ ∃∗ w' : BitVec 64, ⌜KindNoHeap w'⌝ ∗ ((e + 24#64) ↦₆₄ w') :=
    Entails.sepExists_right w (Entails.pure_right hw (Entails.refl _))
  have h40 : ((e + 32#64) ↦₆₄ u4) ∗ ((e + 40#64) ↦₆₄ u3) ∗
      ((e + 48#64) ↦₆₄ u2) ∗ ((e + 56#64) ↦₆₄ u1) ∗ ((e + 64#64) ↦₆₄ u0) ⊢
      memRegion (e + 32#64) 40 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      cells5_entails_memRegion40 (e + 32#64) u4 u3 u2 u1 u0
  rw [show A.live e 72 8 ∗ (e ↦₆₄ 0#64) ∗ ((e + 8#64) ↦₆₄ 8#64) ∗ ((e + 16#64) ↦₆₄ 0#64) ∗
      ((e + 24#64) ↦₆₄ w) ∗ ((e + 32#64) ↦₆₄ u4) ∗ ((e + 40#64) ↦₆₄ u3) ∗
      ((e + 48#64) ↦₆₄ u2) ∗ ((e + 56#64) ↦₆₄ u1) ∗ ((e + 64#64) ↦₆₄ u0) =
    A.live e 72 8 ∗ ((e ↦₆₄ 0#64) ∗ ((e + 8#64) ↦₆₄ 8#64) ∗ ((e + 16#64) ↦₆₄ 0#64)) ∗
      ((e + 24#64) ↦₆₄ w) ∗ (((e + 32#64) ↦₆₄ u4) ∗ ((e + 40#64) ↦₆₄ u3) ∗
      ((e + 48#64) ↦₆₄ u2) ∗ ((e + 56#64) ↦₆₄ u1) ∗ ((e + 64#64) ↦₆₄ u0)) by ac_rfl]
  exact sepConj_mono_right (sepConj_mono hvec (sepConj_mono hkind h40))

/-! ## Main proof of `<DecodeError as From<DecodeErrorKind>>::from` -/

theorem decodeErrorFrom_ok_aux_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A) := by
  simp only [decodeErrorFromSpec, stackAt_decodeErrorFrom]
  cells_unfold
  have hshim := noAllocShim_ok_at_trap (b := b) (C := C) (abs := abs)
    (name := decodeErrorFromName) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
  have halloc := alloc_ok_at_norm_trap (b := b) (C := C)
    (name := decodeErrorFromName) (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")) hA
  have hpanic := panic_at_handle_alloc_error2_trap (b := b) (C := C) (abs := abs)
    (name := decodeErrorFromName) (k := num% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
  clear hA
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff decodeErrorFromName = num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") :=
    (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")
  code_fetches CryptoVerification.libsignalSessionCode
    libsignalSessionBin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")) 92
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase b
        (Rust.withPanics (trTrapExterns C abs))).fnAddr decodeErrorFromName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [trTrapProgAt] at hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr decodeErrorFromName = entry
  examples_hide_fetches
  obtain ⟨k, w⟩ := x
  dsimp only at *
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
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_40_cells (k + 8#64), memRegion_72_cells,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun k0 => SepWPp.exists_elim fun k1 =>
      SepWPp.exists_elim fun k2 => SepWPp.exists_elim fun k3 =>
      SepWPp.exists_elim fun k4 =>
      SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
      SepWPp.exists_elim fun u4 => SepWPp.exists_elim fun u5 =>
      SepWPp.exists_elim fun u6 => SepWPp.exists_elim fun u7 =>
      SepWPp.exists_elim fun u8 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    apply SepWP.fold (decodeErrorWith_zero_entails A _ w _ _ _ _ _ ‹KindNoHeap w›) (by sep_focus)
    apply SepWP.fold (cells6_entails_memRegion48 k w _ _ _ _ _) (by sep_focus)
    wp_done

theorem decodeErrorFrom_ok_aux (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr decodeErrorFromName]
  exact subroutine_ok_kit_of_trTrap (decodeErrorFrom_ok_aux_trap b C A abs hA)

end CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorFrom
