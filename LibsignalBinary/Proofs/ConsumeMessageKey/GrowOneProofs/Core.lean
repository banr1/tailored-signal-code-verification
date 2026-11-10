/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.Fetch
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalSession.RawVecGrowOne

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace GrowOneStateSimp

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

end GrowOneStateSimp

open GrowOneStateSimp

macro "grow_cc_close" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, applyWriteback,
    State.advancePC_eq_setPC, State.setPC_setPC, State.writeReg64_setPC, State.setPState_setPC,
    State.setPState_setPState, State.writeReg64_setPState, State.setMem_setPC, State.setMem_setMem,
    State.writeReg64_setMem, State.setPState_setMem, State.writeReg64_writeReg64_same,
    arm64_norm, *]
  done))

noncomputable abbrev SP (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics (sessionExterns F alloc))

/-- Introduce instruction-fetch hypotheses for a function in `libsignalSessionCode`. -/
elab "session_fetches " b:term:max H:term:max hfn:term:max off:term:max len:term:max : tactic => open Lean Meta Elab Tactic in do
  let offLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat off "session_fetches "))
  let k0Lit := Syntax.mkNumLit "0"
  let lenLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat len "session_fetches "))
  let hfnId : Ident ← if hfn.raw.isIdent then pure ⟨hfn.raw⟩ else do
    let g ← getMainGoal
    let c? ← g.withContext do
      tryCatchRuntimeEx (do
        let e := (← instantiateMVars (← Term.elabTermAndSynthesize hfn none)).consumeMData
        return if e.isConst then some e.constName! else none) (fun _ => pure none)
    match c? with
    | some c => pure (mkCIdentFrom hfn c)
    | none =>
      let id := mkIdent `_hfn_layout
      evalTactic (← `(tactic| have $id := $hfn))
      pure id
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalSessionBin $b $H $hfnId:ident $offLit:num $k0Lit:num $lenLit:num))

def sessionShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

/-- `alloc::raw_vec::handle_error` (`0x47f6c`) transitions to panic. -/
theorem panic_at_handle_error {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "alloc::raw_vec::handle_error")) :
    (SP b F alloc).externAt? ((SP b F alloc).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol hfn hk (by decide) (ls_hook% "alloc::raw_vec::handle_error")
    (by simp [Rust.isPanicSymbol])

theorem shim_ok_at {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2")) :
    subroutine_ok (SP b F alloc) ((SP b F alloc).fnAddr name + BitVec.ofNat 64 k)
      sessionShimSpec :=
  hook_ok_at hfn hk (by decide) (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by simp [Rust.isPanicSymbol])
    ⟨hookNoop, rfl, sessionShim_hookOk⟩

theorem alloc_ok_at {A : RustAlloc} {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} (hA : AllocHooks A alloc)
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "__rustc::__rust_alloc")) :
    subroutine_ok (SP b F alloc) ((SP b F alloc).fnAddr name + BitVec.ofNat 64 k)
      (rustAllocSpec A) :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "__rustc::__rust_alloc")
    (allocHooks_sessionExterns F A alloc hA).alloc

theorem realloc_ok_at {A : RustAlloc} {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} (hA : AllocHooks A alloc)
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "__rustc::__rust_realloc")) :
    subroutine_ok (SP b F alloc) ((SP b F alloc).fnAddr name + BitVec.ofNat 64 k)
      (rustReallocSpec A) :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "__rustc::__rust_realloc")
    (allocHooks_sessionExterns F A alloc hA).realloc

/-! ## Arithmetic Helpers for `finish_grow` and `grow_one` -/

theorem umulh_104_eq_zero {new : BitVec 64} (h : new.toNat * 104 ≤ 9223372036854775800) :
    BitVec.truncate 64 ((104#128 * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth]
  have h1 : (104#128 : BitVec 128).toNat = 104 := rfl
  have h2 : new.toNat < 2 ^ 128 := by omega
  have h3 : 104 * new.toNat < 2 ^ 128 := by omega
  rw [h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : 104 * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  rfl

theorem mul_104_toNat {new : BitVec 64} (h : new.toNat * 104 < 2 ^ 64) :
    (104#64 * new).toNat = new.toNat * 104 := by
  rw [BitVec.toNat_mul]
  have : (104#64 : BitVec 64).toNat = 104 := rfl
  rw [this, Nat.mul_comm, Nat.mod_eq_of_lt h]

theorem mul_104_ne_zero {new : BitVec 64} (h0 : 0 < new.toNat) (h : new.toNat * 104 < 2 ^ 64) :
    104#64 * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_104_toNat h] at ht
  change new.toNat * 104 = 0 at ht
  omega

theorem hi_104_eq_false {new : BitVec 64} (h : new.toNat * 104 ≤ 9223372036854775800) :
    (9223372036854775800#64).ult (104#64 * new) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, mul_104_toNat (by omega)]
  change ¬ (9223372036854775800 < new.toNat * 104)
  omega

theorem beq_mul_104_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat)
    (h : new.toNat * 104 ≤ 9223372036854775800) :
    (104#64 * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_104_ne_zero h0 (by omega)

def rustReallocFullSpec (A : RustAlloc) : Spec (BitVec 64 × Nat × Nat × List (BitVec 8)) where
  pre := fun (p, align, new, bs) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ LayoutOk new align ∧ bs.length ≤ bs.length ∧ bs.length ≤ new⌝ ∗
      A.pool ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗ stackAt s.sp allocHookStack
  post := fun (p, align, new, bs) s0 sf =>
    A.pool ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live p bs.length align ∗ (p ↦ₛ bs)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) new align ∗ (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))

theorem realloc_full_ok_at {A : RustAlloc} {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} (hA : AllocHooks A alloc)
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "__rustc::__rust_realloc")) :
    subroutine_ok (SP b F alloc) ((SP b F alloc).fnAddr name + BitVec.ofNat 64 k)
      (rustReallocFullSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨p, align, new, bs⟩ R s0 hpc hrun hpre hsp => ?_
  have hraw := (realloc_ok_at (b := b) (F := F) hA hfn hk).to_outcome (p, bs.length, align, new, bs) R s0 hpc hrun
    (by simpa only [rustReallocSpec, rustReallocFullSpec, Nat.sub_self, memRegion_zero,
      emp_sepConj, sepConj_emp] using hpre) hsp
  refine hraw.mono_outcome (fun sf hout => ?_)
  unfold SubroutineOutcome at hout ⊢
  simpa only [rustReallocSpec, rustReallocFullSpec, Nat.sub_self,
    memRegion_zero, emp_sepConj, sepConj_emp] using hout

theorem SepWP.instantiate_post_exists {α : Type _} {prog : Program} {target_pc : BitVec 64}
    {s : State} {P R : SepProp} {Q : State → α → SepProp} {rest : State → Prop} (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf w ∗ R) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (∃∗ a, Q sf a) ∗ R) ∧ rest sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro w)) (h1 hm), h2⟩

/-! ## `RawVecInner::finish_grow` (`0x15de4`) -/

abbrev FinishGrowGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def finishGrowZeroSpec (A : RustAlloc) : Spec FinishGrowGhost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs.length = cap.toNat * 104 ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ cells (fsp - 48#64) 6 ∗ stackAt (fsp - 48#64) allocHookStack
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
        A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104)) ∗
      A.pool ∗ cells (fsp - 48#64) 6 ∗ stackAt (fsp - 48#64) allocHookStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

theorem finish_grow_zero_ok {A : RustAlloc} {b : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} (hA : AllocHooks A alloc) :
    subroutine_ok (SP b F alloc)
      ((SP b F alloc).fnAddr "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")
      (finishGrowZeroSpec A) := by
  unfold finishGrowZeroSpec
  cells_unfold
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")
  have hshim := shim_ok_at (b := b) (F := F) (alloc := alloc) hfn (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) (by decide)
  have halloc := alloc_ok_at (b := b) (F := F) hA hfn (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) (by decide)
  session_fetches b (Rust.withPanics (sessionExterns F alloc)) hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) 180
  dsimp only [SP] at hshim halloc ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (sessionExterns F alloc))).fnAddr
    "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (sessionExterns F alloc))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ := x
  dsimp only at *
  subst fsp
  subst cap
  have humulh := umulh_104_eq_zero h
  have hhi := hi_104_eq_false h
  have hcbz := beq_mul_104_zero_eq_false h_11 h
  have hmul : (104#64 * new).toNat = new.toNat * 104 := mul_104_toNat (by omega)
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true]
    wp_done

def finishGrowNeSpec (A : RustAlloc) : Spec FinishGrowGhost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length = cap.toNat * 104 ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗
    A.pool ∗ cells (fsp - 48#64) 6 ∗ stackAt (fsp - 48#64) allocHookStack
  post := fun (out, _cap, ptr, new, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
        A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length)) ∗
      A.pool ∗ cells (fsp - 48#64) 6 ∗ stackAt (fsp - 48#64) allocHookStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

theorem finish_grow_ne_ok {A : RustAlloc} {b : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} (hA : AllocHooks A alloc) :
    subroutine_ok (SP b F alloc)
      ((SP b F alloc).fnAddr "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")
      (finishGrowNeSpec A) := by
  unfold finishGrowNeSpec
  cells_unfold
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")
  have hrealloc := realloc_full_ok_at (b := b) (F := F) hA hfn (k := num% (ls_off% "__rustc::__rust_realloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) (by decide)
  session_fetches b (Rust.withPanics (sessionExterns F alloc)) hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) 180
  dsimp only [SP] at hrealloc ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (sessionExterns F alloc))).fnAddr
    "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (sessionExterns F alloc))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ := x
  dsimp only at *
  subst fsp
  have humulh := umulh_104_eq_zero h
  have hhi := hi_104_eq_false h
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr h_8
  have hmul : (104#64 * new).toNat = new.toNat * 104 := mul_104_toNat (by omega)
  have hcap_le : cap.toNat * 104 ≤ new.toNat * 104 := Nat.mul_le_mul_right 104 h_10
  have hmul_cap : (104#64 * cap).toNat = bs.length := by
    rw [mul_104_toNat (by omega), h_9]
  have hle_new : bs.length ≤ new.toNat * 104 := by omega
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  wp_steps
  wp_apply
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
    simp only [ite_true]
    wp_done

/-! ## `RawVec<MessageKey>::grow_one` (`0x15cac`) -/

theorem stackAt_grow_one (sp : BitVec 64) :
    stackAt sp 4608 =
      memRegion (sp - 4608#64) 400 ∗
        stackAt (sp - 112#64) allocHookStack ∗
        cells (sp - 112#64) 6 ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := stackAt_split_bottom sp 4208 400 (by decide)
  have h2 := stackAt_split_cells sp 4144 8 (by decide)
  have h3 := stackAt_split_cells (sp - 64#64) 4096 6 (by decide)
  change stackAt sp 4608 = memRegion (sp - 4608#64) 400 ∗ stackAt sp 4208 at h1
  change stackAt sp 4208 = stackAt (sp - 64#64) 4144 ∗ cells (sp - 64#64) 8 at h2
  have hsub : (sp - 64#64) - BitVec.ofNat 64 (8 * 6) = sp - 112#64 := by
    rw [BitVec.sub_sub]; rfl
  rw [hsub] at h3
  change stackAt (sp - 64#64) 4144 =
    stackAt (sp - 112#64) allocHookStack ∗ cells (sp - 112#64) 6 at h3
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, h3, hc8]
  ac_rfl

theorem grow_new_cap_eq {cap : BitVec 64} (h : max (2 * cap.toNat) 4 * 104 ≤ 9223372036854775800) :
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

theorem allocFailedIn_of_eq {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem grow_one_base_ok {A : RustAlloc} {b : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} (hA : AllocHooks A alloc) :
    subroutine_ok (SP b F alloc)
      ((SP b F alloc).fnAddr "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
      (growOneSpec A) := by
  simp only [growOneSpec, stackAt_grow_one, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
  have hpanic := panic_at_handle_error (b := b) (F := F) (alloc := alloc) hfn (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")) (by decide)
  have hfg0 := finish_grow_zero_ok (b := b) (F := F) hA
  have hfg1 := finish_grow_ne_ok (b := b) (F := F) hA
  rw [Program.fnAddr_rel (name := "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]") (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")) (by decide)] at hfg0 hfg1
  session_fetches b (Rust.withPanics (sessionExterns F alloc)) hfn (num% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")) 104
  dsimp only [SP] at hpanic hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (sessionExterns F alloc))).fnAddr
    "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (sessionExterns F alloc))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hnew_eq := grow_new_cap_eq h
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * 104 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero h_2
    subst hbs
    simp only [BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_zero, Nat.mul_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := entry + bv% (60))
    wp_steps
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0', ite_false, sepConj_assoc]
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = new.toNat * 104 - bs.length := by
      rw [Nat.sub_mul, hnew_toNat, h_2]
    rw [hsub_mul]
    apply SepWPp.of_sepWP (mid := entry + bv% (60))
    wp_steps
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_ok' (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) (A : RustAlloc)
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocHooks A alloc) :
    GrowOneOk img F alloc A := by
  unfold GrowOneOk
  rw [show sessionProg img F alloc = SP img.base F alloc from libsignalSessionCode_ofImage himg]
  have haddr : ((SP img.base F alloc).fnAddr
      "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one") =
      img.base + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")]
  rw [← haddr]
  exact subroutine_ok_inImage img (grow_one_base_ok hA)

/-! ## Relocatable `[LibsignalPlacement]` Contracts (Blocks 43 and 45) -/

theorem ls_externAt?_of_mem [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (k := k) (by simp [hk, hget]) hi hunmut

theorem ls_hook_ok_of_mem [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((ls_externAt?_of_mem hmem hi hunmut).trans hf) hok

theorem realloc_full_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustReallocSym) (rustReallocFullSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨p, align, new, bs⟩ R s0 hpc hrun hpre hsp => ?_
  have hraw := (ls_hook_ok_of_mem (prog := prog) h_realloc (by decide) hi hunmut).to_outcome
    (p, bs.length, align, new, bs) R s0 hpc hrun
    (by simpa only [rustReallocSpec, rustReallocFullSpec, Nat.sub_self, memRegion_zero,
      emp_sepConj, sepConj_emp] using hpre) hsp
  refine hraw.mono_outcome (fun sf hout => ?_)
  unfold SubroutineOutcome at hout ⊢
  simpa only [rustReallocSpec, rustReallocFullSpec, Nat.sub_self,
    memRegion_zero, emp_sepConj, sepConj_emp] using hout

theorem finish_grow_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrowZeroSpec A) := by
  unfold finishGrowZeroSpec
  cells_unfold
  have hshim : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsNoAllocShimSym) sessionShimSpec :=
    ls_hook_ok_of_mem ⟨hookNoop, h_shim, sessionShim_hookOk⟩
  have halloc : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) :=
    ls_hook_ok_of_mem h_alloc
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ := x
  dsimp only at *
  subst fsp
  subst cap
  have humulh := umulh_104_eq_zero h
  have hhi := hi_104_eq_false h
  have hcbz := beq_mul_104_zero_eq_false h_11 h
  have hmul : (104#64 * new).toNat = new.toNat * 104 := mul_104_toNat (by omega)
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true]
    wp_done

theorem finish_grow_ne_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrowNeSpec A) := by
  unfold finishGrowNeSpec
  cells_unfold
  have hrealloc : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustReallocSym) (rustReallocFullSpec A) :=
    realloc_full_placed_ok h_realloc
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ := x
  dsimp only at *
  subst fsp
  have humulh := umulh_104_eq_zero h
  have hhi := hi_104_eq_false h
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr h_8
  have hmul : (104#64 * new).toNat = new.toNat * 104 := mul_104_toNat (by omega)
  have hcap_le : cap.toNat * 104 ≤ new.toNat * 104 := Nat.mul_le_mul_right 104 h_10
  have hmul_cap : (104#64 * cap).toNat = bs.length := by
    rw [mul_104_toNat (by omega), h_9]
  have hle_new : bs.length ≤ new.toNat * 104 := by omega
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  wp_steps
  wp_apply
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
    simp only [ite_true]
    wp_done

def finishGrowSpec (A : RustAlloc) : Spec FinishGrowGhost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ bs.length = cap.toNat * 104 ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool ∗ cells (fsp - 48#64) 6 ∗ stackAt (fsp - 48#64) allocHookStack
  post := fun (out, cap, ptr, new, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs))
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
        A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length)) ∗
      A.pool ∗ cells (fsp - 48#64) 6 ∗ stackAt (fsp - 48#64) allocHookStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

theorem finish_grow_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrowSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  dsimp only [finishGrowSpec] at hpre'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hbs_len, hle, hpos, hbnd⟩, hrest⟩ := hpre'
  by_cases hcap : cap = 0#64
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero hbs_len
    subst hbs
    have h0 := (finish_grow_zero_placed_ok h_shim h_alloc).to_outcome
      (out, 0#64, ptr, new, [], o0, o1, o2, fsp) R s0 hpc hrun
      (by
        dsimp only [finishGrowZeroSpec]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, rfl, hbs_len, hle, hpos, hbnd⟩, ?_⟩
        simpa only [ite_true, emp_sepConj, sepConj_assoc] using hrest)
      hsp
    refine h0.mono_outcome (fun sf hout => ?_)
    unfold SubroutineOutcome at hout ⊢
    simpa only [finishGrowZeroSpec, finishGrowSpec, ite_true, emp_sepConj, sepConj_emp,
      pointsToBytes_nil, List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      Nat.sub_zero, sepConj_assoc] using hout
  · have h1 := (finish_grow_ne_placed_ok h_realloc).to_outcome
      (out, cap, ptr, new, bs, o0, o1, o2, fsp) R s0 hpc hrun
      (by
        dsimp only [finishGrowNeSpec]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs_len, hle, hpos, hbnd⟩, ?_⟩
        simpa only [hcap, ite_false, sepConj_assoc] using hrest)
      hsp
    refine h1.mono_outcome (fun sf hout => ?_)
    unfold SubroutineOutcome at hout ⊢
    simpa only [finishGrowNeSpec, finishGrowSpec, hcap, ite_false, sepConj_assoc] using hout

theorem grow_one_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneSpec A)) := by
  simp only [withLsCodeLoaded, growOneSpec, stackAt_grow_one,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hpanic : ((blkPC_43).rebase (blkPl_43).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked :=
    (ls_externAt?_of_mem).trans h_panic
  have hfg0 := finish_grow_zero_placed_ok h_shim h_alloc
  have hfg1 := finish_grow_ne_placed_ok h_realloc
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hnew_eq : (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := grow_new_cap_eq (by omega)
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * 104 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero ‹bs.length = (0#64 : BitVec 64).toNat * 104›
    subst hbs
    simp only [BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_zero, Nat.mul_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := (blkPl_43).base + 60#64)
    wp_steps_lscl (lsmpl.base 45)
    have hfg0_call := lscall_blk (callerProg := (blkPC_43).rebase (blkPl_43).base H) hfg0 ‹_›
    wp_call hfg0_call (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0', ite_false, sepConj_assoc]
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = new.toNat * 104 - bs.length := by
      rw [Nat.sub_mul, hnew_toNat, ‹bs.length = cap.toNat * 104›]
    rw [hsub_mul]
    apply SepWPp.of_sepWP (mid := (blkPl_43).base + 60#64)
    wp_steps_lscl (lsmpl.base 45)
    have hfg1_call := lscall_blk (callerProg := (blkPC_43).rebase (blkPl_43).base H) hfg1 ‹_›
    wp_call hfg1_call (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

end CryptoVerification.LibsignalSession.RawVecGrowOne
