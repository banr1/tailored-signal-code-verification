/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpers
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Panic Branch of `next_key_internal` and Front-Pop Loop of `Chain::send_key`

Proves the panic branch of `<ChainEpochDirection>::next_key_internal` (`0x5fd94`, Block `362`)
when `next.length ≠ 32 ∨ ctr = 0xffffffff#32`, and the front-epoch pop loop (`+148..+344`) and
front-clear block (`+344..+380`) of `<spqr::chain::Chain>::send_key` (`0x60db0`, Block `367`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open ChainAddEpochFacts ChainNewFacts NextKeyInternalFacts AgreeStateSimp

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x5b9b8 → 0x5bc08]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! ## Panic Branch of `<ChainEpochDirection>::next_key_internal` (`0x5fd94`) -/

theorem chainSendKey_fnOff : libsignalSessionCode.fnOff chainSendKeyName = 0x5b9b8 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x5b9b8

abbrev assertFailedUsizeName : String :=
  "core::panicking::assert_failed::<usize, usize>"

theorem assertFailedUsize_fnOff :
    libsignalSessionCode.fnOff assertFailedUsizeName =
      num% (ls_off% "core::panicking::assert_failed::<usize, usize>") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_stub% "core::panicking::assert_failed::<usize, usize>")

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  nextKeyInternal_fnOff chainSendKey_fnOff
  shim_fnOff alloc_fnOff dealloc_fnOff handleError_fnOff
  panicAddOverflow_fnOff corePanic_fnOff assertFailedUsize_fnOff
  libsignalSessionCode_fnOff_0x5a99c
  libsignalSessionCode_fnOff_0x5b9b8
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_stub% "core::panicking::assert_failed::<usize, usize>")
  (ls_hook% "core::panicking::assert_failed::<usize, usize>")
  (ls_stub% "core::panicking::panic")
  (ls_hook% "core::panicking::panic")

theorem stackAt_nextKeyInternalPanic_split (sp : BitVec 64) :
    stackAt sp nextKeyInternalStackX =
      memRegion (sp - BitVec.ofNat 64 16560) 16384 ∗ (∃∗ l0 : BitVec 64, (sp - 176#64) ↦₆₄ l0) ∗
      memRegion (sp - 168#64) 120 ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
       ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ c0) ∗ ((sp - 40#64) ↦₆₄ c1) ∗ ((sp - 32#64) ↦₆₄ c2) ∗
        ((sp - 24#64) ↦₆₄ c3) ∗ ((sp - 16#64) ↦₆₄ c4) ∗ ((sp - 8#64) ↦₆₄ c5)) := by
  change memRegion (sp - BitVec.ofNat 64 16560) 16560 = _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16560) (n := 16384) (k := 176) (b' := sp - 176#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 176#64) (n := 8) (k := 168) (b' := sp - 168#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 168#64) (n := 120) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (sp - 176#64)]
  change memRegion (sp - BitVec.ofNat 64 16560) 16384 ∗ ((∃∗ l0 : BitVec 64, (sp - 176#64) ↦₆₄ l0) ∗
    (memRegion (sp - 168#64) 120 ∗ memRegion (sp - 48#64) (8 * 6))) = _
  rw [ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]
  have hc6 : cells (sp - 48#64) 6 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
       ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ c0) ∗ ((sp - 40#64) ↦₆₄ c1) ∗ ((sp - 32#64) ↦₆₄ c2) ∗
        ((sp - 24#64) ↦₆₄ c3) ∗ ((sp - 16#64) ↦₆₄ c4) ∗ ((sp - 8#64) ↦₆₄ c5)) := by cells_unfold
  rw [hc6]

theorem panic_at_ovf_nextKeyInternal (base : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt base ext).externAt?
      ((tripleRatchetProgAtExt base ext).fnAddr nextKeyInternalName +
        bv% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - 0x5a99c)) =
      some Rust.panicked := by
  exact panic_at_sym_ext base ext nextKeyInternalName panicAddOverflowName
    (num% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - 0x5a99c))
    (by rw [nextKeyInternal_fnOff, panicAddOverflow_fnOff])
    (hp := by simp [Rust.isPanicSymbol, panicAddOverflowName])

theorem panic_at_assert_nextKeyInternal (base : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt base ext).externAt?
      ((tripleRatchetProgAtExt base ext).fnAddr nextKeyInternalName +
        bv% (ls_off% "core::panicking::assert_failed::<usize, usize>" - 0x5a99c)) =
      some Rust.panicked := by
  exact panic_at_sym_ext base ext nextKeyInternalName assertFailedUsizeName
    (num% (ls_off% "core::panicking::assert_failed::<usize, usize>" - 0x5a99c))
    (by rw [nextKeyInternal_fnOff, assertFailedUsize_fnOff])
    (hp := by simp [Rust.isPanicSymbol, assertFailedUsizeName])

local macro "sep_elim_exists" : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _))))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem nextKeyInternal_panic_ok_ext_x {img : Obj.Image}
    {ext : String → Option (State → State)}
    (_himg : Obj.Loads libsignalSessionImage img) :
    NextKeyInternalPanicOkX img ext := by
  unfold NextKeyInternalPanicOkX tripleRatchetProgAtExt
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff nextKeyInternalName = 0x5a99c :=
    nextKeyInternal_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5a99c 272
  have h_panic_ovf := panic_at_ovf_nextKeyInternal img.base ext
  have h_panic_assert := panic_at_assert_nextKeyInternal img.base ext
  dsimp only [tripleRatchetProgAtExt] at h_panic_ovf h_panic_assert
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear _himg hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      nextKeyInternalName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  rcases x with ⟨out, nextA, next, ctrA, ctr⟩
  dsimp only [Spec.inImage, nextKeyInternalPanicSpecX] at *
  refine SepWPp.rw_pre (by rw [stackAt_nextKeyInternalPanic_split s0.sp]) ?_
  sep_elim_exists
  subst h_4
  by_cases hlen32 : next.length = 32
  · have hctr : ctr = 0xffffffff#32 := h.resolve_left (not_not.mpr hlen32)
    subst hctr
    have hx2_32 : s0.readReg64 (.gpr 2#5) = 32#64 := by rw [h_3, hlen32]
    wp_norm_hyp hx2_32
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - 0x5a99c))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_ovf) fun hm => ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨by simp [Rust.panicked, arm64_norm], Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm⟩
  · have hne_bv : BitVec.ofNat 64 next.length ≠ 32#64 := by
      intro heq
      have htn := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_5] at htn
      exact hlen32 htn
    have hne : (s0.readReg64 (.gpr 2#5) + 18446744073709551584#64 == 0#64) = false := by
      rw [h_3]; revert hne_bv; bv_kernel
    have hne2 : (s0.readReg64 (.gpr 2#5) == 32#64) = false := by
      rw [h_3]; exact beq_false_of_ne hne_bv
    have hne3 : (s0.readReg64 (.gpr 2#5) != 32#64) = true := by
      rw [h_3]; simp [hne_bv]
    wp_norm_hyp hne
    wp_norm_hyp hne2
    wp_norm_hyp hne3
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "core::panicking::assert_failed::<usize, usize>" - 0x5a99c))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_assert) fun hm => ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨by simp [Rust.panicked, arm64_norm], Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm⟩

/-! ## Front-Pop Loop of `<spqr::chain::Chain>::send_key` (`0x60e44 .. 0x60f08`) -/

open ChainSendKeyFacts

theorem SepWP.seq_entails_inImage {prog : Program} {img : Obj.Image}
    {mid target : BitVec 64} {s : State} {P P_mid : SepProp}
    {φ : State → Prop} {post : State → SepProp → Prop}
    (hF : ImgCallInv img s)
    (h1 : SepWP prog mid s P (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → ImgCallInv img sm → φ sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post := by
  unfold SepWP
  intro R hm hL
  rcases h1.elim hm hL with ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hφ, hent⟩ | ⟨hoom, hfalse⟩⟩
  · have hmm' : sm.mem ⊨ P_mid ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    rcases (h2 sm hpcm hrunm (hF.of_steps hsteps1) hφ).elim hmm' (hsteps1.codeLoaded hL) with
      ⟨sf, hsteps2, hout⟩
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hoom, hfalse⟩⟩

theorem SepWP.frame_entails {prog : Program} {mid : BitVec 64} {s : State}
    {P P_mid F : SepProp} {φ : State → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid))) :
    SepWP prog mid s (P ∗ F) (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid ∗ F)) := by
  unfold SepWP
  intro R hm hL
  rw [sepConj_assoc] at hm
  rcases h1.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hφ, hent⟩ | ⟨_, hfalse⟩⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inl ⟨hpcm, hrunm, Pm ∗ F, hmm, hφ, sepConj_mono_left hent⟩⟩
  · rw [satisfies_pure_sepConj] at hfalse; exact False.elim hfalse.1

theorem SepWP.join_inImage {prog : Program} {img : Obj.Image}
    {join_pc target : BitVec 64} {s : State}
    {P P_join : SepProp} {post : State → SepProp → Prop}
    (hF : ImgCallInv img s)
    (h1 : SepWP prog join_pc s P (fun sm Pm =>
      sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ sm.trace = s.trace ∧ (Pm ⊢ P_join)))
    (h2 : ∀ sm, sm.pc = join_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → sm.trace = s.trace → ImgCallInv img sm →
      SepWP prog target sm P_join post) :
    SepWP prog target s P post := by
  unfold SepWP
  intro R hm hL
  rcases h1.elim hm hL with ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hsp, hcs, htr, hent⟩ | ⟨hoom, hfalse⟩⟩
  · have hmm' : sm.mem ⊨ P_join ∗ R :=
      Satisfies.mono (sepConj_mono_left hent) hmm
    rcases (h2 sm hpcm hrunm hsp hcs htr (hF.of_steps hsteps1)).elim hmm' (hsteps1.codeLoaded hL) with
      ⟨sf, hsteps2, hout⟩
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hoom, hfalse⟩⟩

theorem SepWP.conseq {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {post1 post2 : State → SepProp → Prop}
    (h1 : SepWP prog target s P post1)
    (h2 : ∀ sf Pf, post1 sf Pf → post2 sf Pf) :
    SepWP prog target s P post2 := by
  unfold SepWP
  intro R hm hL
  rcases h1.elim hm hL with ⟨sf, hsteps, ⟨hpcf, hrunf, Pf, hmf, hp1⟩ | ⟨hoom, hfalse⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, Pf, hmf, h2 sf Pf hp1⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hoom, hfalse⟩⟩

theorem vecDequeRingBuf_get_front (A : RustAlloc) (cap ptr head : BitVec 64)
    (x0 : ChainEpochGhost × ChainEpoch) (xs : List (ChainEpochGhost × ChainEpoch))
    (hlen : (x0 :: xs).length ≤ cap.toNat) :
    vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head (x0 :: xs) ⊢
      ⌜head.toNat < cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      A.live ptr (cap.toNat * 112) 8 ∗
      chainEpochAt A x0 (ptr + head * 112#64) ∗
      vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr (x0 :: xs) head.toNat := by
  have hi : 0 < (x0 :: xs).length := Nat.zero_lt_succ _
  refine Entails.trans (vecDequeRingBuf_get_physIdx A cap ptr head (x0 :: xs) hlen hi) ?_
  refine Entails.pure_left fun ⟨hhead, hcap_lt, hptr⟩ => ?_
  have hphys0 : vecDequePhysIdx head.toNat cap.toNat 0 = head.toNat := by
    unfold vecDequePhysIdx; simp [hhead]
  have hmadd := (head_mul_112_eq (ptr := ptr) hhead hcap_lt).symm
  rw [hmadd, hphys0]
  exact Entails.pure_right ⟨hhead, hcap_lt, hptr⟩ (Entails.refl _)

theorem vecDequeRingBuf_pop_front_mul (A : RustAlloc) (cap ptr head : BitVec 64)
    (x0 : ChainEpochGhost × ChainEpoch) (xs : List (ChainEpochGhost × ChainEpoch))
    (hhead : head.toNat < cap.toNat) (hcap_lt : cap.toNat * 112 < 2 ^ 63)
    (hptr : ptr ≠ 0#64) (hlen : (x0 :: xs).length ≤ cap.toNat) :
    A.live ptr (cap.toNat * 112) 8 ∗
      memRegion (ptr + head * 112#64) 112 ∗
      vecDequeSlotsExcept (chainEpochAt A) 112 cap.toNat head.toNat ptr (x0 :: xs) head.toNat ⊢
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr
        (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)) xs := by
  have hphys0 : vecDequePhysIdx head.toNat cap.toNat 0 = head.toNat := by
    unfold vecDequePhysIdx; simp [hhead]
  have hmadd := head_mul_112_eq (ptr := ptr) hhead hcap_lt
  rw [hphys0] at hmadd
  rw [hmadd]
  exact vecDequeRingBuf_pop_front A cap ptr head x0 xs hhead hcap_lt hptr hlen

theorem ofNat_cons_len_props {α : Type} (x : α) (xs : List α) {cap : BitVec 64}
    (hlen : (x :: xs).length ≤ cap.toNat) (hcap : cap.toNat * 112 < 2 ^ 63) :
    (BitVec.ofNat 64 (x :: xs).length == 0#64) = false ∧
    BitVec.ofNat 64 (x :: xs).length + 18446744073709551615#64 = BitVec.ofNat 64 xs.length ∧
    BitVec.ofNat 64 (x :: xs).length - 1#64 = BitVec.ofNat 64 xs.length := by
  simp only [List.length_cons] at hlen ⊢
  have hlt1 : xs.length + 1 < 18446744073709551616 := by omega
  have hlt0 : xs.length < 18446744073709551616 := by omega
  have hne : BitVec.ofNat 64 (xs.length + 1) ≠ 0#64 := by
    intro h0
    have htn := congrArg BitVec.toNat h0
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt1] at htn
  have hsub : BitVec.ofNat 64 (xs.length + 1) - 1#64 = BitVec.ofNat 64 xs.length := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt0]
    omega
  have hadd : BitVec.ofNat 64 (xs.length + 1) + 18446744073709551615#64 =
      BitVec.ofNat 64 (xs.length + 1) - 1#64 := by bv_kernel
  exact ⟨beq_false_of_ne hne, hadd.trans hsub, hsub⟩

theorem cap_ne_neg_one {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  have hne : cap ≠ 0xffffffffffffffff#64 := by
    intro heq; subst heq; simp at h
  rw [beq_eq_false_iff_ne]; intro heq; apply hne; revert heq; bv_kernel

/-- Minimal heap footprint of the front-pop loop in `Chain::send_key`. -/
def popLoopPre (A : RustAlloc) (sp selfPtr cap ptr head l2 : BitVec 64)
    (epochs : List ChainEpochGhost) (links : List ChainEpoch) : SepProp :=
  ((sp + 8#64) ↦₆₄ ptr) ∗ ((sp + 16#64) ↦₆₄ cap) ∗ ((sp + 24#64) ↦₆₄ l2) ∗
  ((selfPtr + 16#64) ↦₆₄ head) ∗ ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links.length) ∗
  vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
    cap ptr head (epochs.zip links) ∗
  A.pool ∗ stackAt sp extHookStack

set_option maxHeartbeats 1600000 in
theorem sendKey_pop_step {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (selfPtr cap ptr head l2 : BitVec 64)
    (gce : ChainEpochGhost) (epochs' : List ChainEpochGhost)
    (ce : ChainEpoch) (links' : List ChainEpoch)
    (hlen_le : (ce :: links').length ≤ cap.toNat) (hlen_eq : epochs'.length = links'.length)
    (s : State) (hF : ImgCallInv img s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainSendKeyName + 164#64)
    (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (ce :: links').length)
    (hx20 : s.readReg64 (.gpr 20#5) = selfPtr) (hx22 : s.readReg64 (.gpr 22#5) = head) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    let entry := prog.fnAddr chainSendKeyName
    let head1 := BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)
    SepWP prog (entry + 148#64) s
      (popLoopPre A s.sp selfPtr cap ptr head l2 (gce :: epochs') (ce :: links'))
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.spAligned = true ∧
         sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sf.readReg64 (.gpr 20#5) = selfPtr ∧
         sf.readReg64 (.gpr 22#5) = head1 ∧ sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 links'.length ∧
         sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧ sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
         sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (P' ⊢ popLoopPre A s.sp selfPtr cap ptr head1 gce.recv.prev.ptr epochs' links')) := by
  intro prog entry head1
  have hfn : libsignalSessionCode.fnOff chainSendKeyName = 0x5b9b8 := chainSendKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b9b8 596
  have h_dealloc := sub_ok_at_rebase (name := chainSendKeyName) (callee := deallocName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x5b9b8))
    (by rw [chainSendKey_fnOff, dealloc_fnOff]) hdealloc
  clear hdealloc hfn
  dsimp only [prog, entry, head1] at *
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainSendKeyName = entry_addr
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  unfold popLoopPre; simp only [List.zip_cons_cons]
  have hzip_le : ((gce, ce) :: epochs'.zip links').length ≤ cap.toNat := by
    simp only [List.length_cons, List.length_zip, hlen_eq, Nat.min_self] at hlen_le ⊢; exact hlen_le
  refine SepWP.fold (vecDequeRingBuf_get_front A cap ptr head (gce, ce) (epochs'.zip links') hzip_le) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hhead, hcap_lt, hptr⟩
  refine SepWP.fold (chainEpochAt_unpack_pop A gce ce (ptr + head * 112#64)) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hs_n_le, hs_n_lt, hs_n_ptr, hs_p_le, hs_p_lt, hs_p_ptr,
    hr_n_le, hr_n_lt, hr_n_ptr, hr_p_le, hr_p_lt, hr_p_ptr⟩
  have ⟨hx8_ne0, hx8_add, hx8_sub⟩ := ofNat_cons_len_props ce links' hlen_le hcap_lt
  have hhead1_eq := physIdx_one_eq hhead hcap_lt
  have hcmn := cap_ne_neg_one hs_n_lt
  wp_norm_hyp hsp_align; wp_norm_hyp hx8; wp_norm_hyp hx20; wp_norm_hyp hx22
  wp_norm_hyp hx8_ne0; wp_norm_hyp hx8_add; wp_norm_hyp hx8_sub; wp_norm_hyp hhead1_eq; wp_norm_hyp hcmn
  apply SepWP.seq_inImage (mid := entry_addr + 232#64) hF
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  refine SepWP.join_inImage (join_pc := entry_addr + 248#64)
    (P_join :=
      ((s.sp + 8#64) ↦₆₄ ptr) ∗ ((s.sp + 16#64) ↦₆₄ cap) ∗ ((s.sp + 24#64) ↦₆₄ gce.recv.prev.ptr) ∗
      ((selfPtr + 16#64) ↦₆₄ head1) ∗ ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links'.length) ∗
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head1 (epochs'.zip links') ∗
      (gce.send.prev.ptr ↦ₛ ce.send.prev.data) ∗ vecU8Rest A gce.send.prev.cap gce.send.prev.ptr ce.send.prev.data.length ∗
      (gce.recv.next.ptr ↦ₛ ce.recv.next) ∗ vecU8Rest A gce.recv.next.cap gce.recv.next.ptr ce.recv.next.length ∗
      (gce.recv.prev.ptr ↦ₛ ce.recv.prev.data) ∗ vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data.length ∗
      A.pool ∗ stackAt s.sp extHookStack) hinv1 ?_ ?_
  · by_cases hcap1 : gce.send.next.cap = 0#64
    · have hcap1_beq : (gce.send.next.cap == 0#64) = true := by simp [hcap1]
      wp_norm_hyp hcap1_beq
      refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A gce.send.next.ptr hcap1 hs_n_le)) (by sep_focus) ?_
      wp_steps
      refine SepWP.fold (chainEpochSlot_entails_memRegion_112 (ptr + head * 112#64)
        gce.send.next.cap gce.send.next.ptr (BitVec.ofNat 64 ce.send.next.length)
        gce.send.prev.cap gce.send.prev.ptr (BitVec.ofNat 64 ce.send.prev.data.length)
        gce.recv.next.cap gce.recv.next.ptr (BitVec.ofNat 64 ce.recv.next.length)
        gce.recv.prev.cap gce.recv.prev.ptr (BitVec.ofNat 64 ce.recv.prev.data.length)
        ce.send.ctr ce.recv.ctr) (by sep_focus) ?_
      refine SepWP.fold (vecDequeRingBuf_pop_front_mul A cap ptr head (gce, ce) (epochs'.zip links')
        hhead hcap_lt hptr hzip_le) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩; sep_frame
    · have hcap1_beq : (gce.send.next.cap == 0#64) = false := beq_false_of_ne hcap1
      wp_norm_hyp hcap1_beq
      refine SepWP.fold (vecU8Rest_nonzero_entails A gce.send.next.ptr hcap1 hs_n_le hs_n_lt) (by sep_focus) ?_
      refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hpos1, _, hisize1⟩
      have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      apply SepWP.seq_inImage (mid := entry_addr + bv% (ls_off% "__rustc::__rust_dealloc" - 0x5b9b8)) hinv1
      wp_steps
      refine SepWP.fold (chainEpochSlot_entails_memRegion_112 (ptr + head * 112#64)
        gce.send.next.cap gce.send.next.ptr (BitVec.ofNat 64 ce.send.next.length)
        gce.send.prev.cap gce.send.prev.ptr (BitVec.ofNat 64 ce.send.prev.data.length)
        gce.recv.next.cap gce.recv.next.ptr (BitVec.ofNat 64 ce.recv.next.length)
        gce.recv.prev.cap gce.recv.prev.ptr (BitVec.ofNat 64 ce.recv.prev.data.length)
        ce.send.ctr ce.recv.ctr) (by sep_focus) ?_
      refine SepWP.fold (vecDequeRingBuf_pop_front_mul A cap ptr head (gce, ce) (epochs'.zip links')
        hhead hcap_lt hptr hzip_le) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      rintro ⟨hF_d1, hsym_d1⟩
      wp_call h_dealloc (gce.send.next.ptr, gce.send.next.cap.toNat, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩; sep_frame
  · intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv2
    have hsp1_eq : sf1.sp = s.sp := hsp1
    wp_split_join hsp1 hcs1; wp_norm_hyp htr1
    refine SepWP.join_inImage (join_pc := entry_addr + 268#64)
      (P_join :=
        ((s.sp + 8#64) ↦₆₄ ptr) ∗ ((s.sp + 16#64) ↦₆₄ cap) ∗ ((s.sp + 24#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((selfPtr + 16#64) ↦₆₄ head1) ∗ ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links'.length) ∗
        vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head1 (epochs'.zip links') ∗
        (gce.recv.next.ptr ↦ₛ ce.recv.next) ∗ vecU8Rest A gce.recv.next.cap gce.recv.next.ptr ce.recv.next.length ∗
        (gce.recv.prev.ptr ↦ₛ ce.recv.prev.data) ∗ vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data.length ∗
        A.pool ∗ stackAt s.sp extHookStack) hinv2 ?_ ?_
    · by_cases hcap2 : gce.send.prev.cap = 0#64
      · have hcap2_beq : (gce.send.prev.cap == 0#64) = true := by simp [hcap2]
        wp_norm_hyp hcap2_beq
        refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A gce.send.prev.ptr hcap2 hs_p_le)) (by sep_focus) ?_
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩; sep_frame
      · have hcap2_beq : (gce.send.prev.cap == 0#64) = false := beq_false_of_ne hcap2
        wp_norm_hyp hcap2_beq
        refine SepWP.fold (vecU8Rest_nonzero_entails A gce.send.prev.ptr hcap2 hs_p_le hs_p_lt) (by sep_focus) ?_
        refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hpos2, _, hisize2⟩
        have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        apply SepWP.seq_inImage (mid := entry_addr + bv% (ls_off% "__rustc::__rust_dealloc" - 0x5b9b8)) hinv2
        wp_steps
        refine SepWP.fold (Entails.of_eq (show stackAt s.sp extHookStack = stackAt sf1.sp extHookStack by rw [hsp1_eq])) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        rintro ⟨hF_d2, hsym_d2⟩
        wp_call h_dealloc (gce.send.prev.ptr, gce.send.prev.cap.toNat, 1)
        refine SepWP.fold (Entails.of_eq (show stackAt sf1.sp extHookStack = stackAt s.sp extHookStack by rw [hsp1_eq])) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩; sep_frame
    · intro sf2 hpc2 hrun2 hsp2 hcs2 htr2 hinv3
      have hsp2_eq : sf2.sp = s.sp := hsp2.trans hsp1_eq
      wp_split_join hsp2 hcs2; wp_norm_hyp htr2
      refine SepWP.join_inImage (join_pc := entry_addr + 288#64)
        (P_join :=
          ((s.sp + 8#64) ↦₆₄ ptr) ∗ ((s.sp + 16#64) ↦₆₄ cap) ∗ ((s.sp + 24#64) ↦₆₄ gce.recv.prev.ptr) ∗
          ((selfPtr + 16#64) ↦₆₄ head1) ∗ ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links'.length) ∗
          vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head1 (epochs'.zip links') ∗
          (gce.recv.prev.ptr ↦ₛ ce.recv.prev.data) ∗ vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data.length ∗
          A.pool ∗ stackAt s.sp extHookStack) hinv3 ?_ ?_
      · by_cases hcap3 : gce.recv.next.cap = 0#64
        · have hcap3_beq : (gce.recv.next.cap == 0#64) = true := by simp [hcap3]
          wp_norm_hyp hcap3_beq
          refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A gce.recv.next.ptr hcap3 hr_n_le)) (by sep_focus) ?_
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩; sep_frame
        · have hcap3_beq : (gce.recv.next.cap == 0#64) = false := beq_false_of_ne hcap3
          wp_norm_hyp hcap3_beq
          refine SepWP.fold (vecU8Rest_nonzero_entails A gce.recv.next.ptr hcap3 hr_n_le hr_n_lt) (by sep_focus) ?_
          refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hpos3, _, hisize3⟩
          have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          apply SepWP.seq_inImage (mid := entry_addr + bv% (ls_off% "__rustc::__rust_dealloc" - 0x5b9b8)) hinv3
          wp_steps
          refine SepWP.fold (Entails.of_eq (show stackAt s.sp extHookStack = stackAt sf2.sp extHookStack by rw [hsp2_eq])) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          rintro ⟨hF_d3, hsym_d3⟩
          wp_call h_dealloc (gce.recv.next.ptr, gce.recv.next.cap.toNat, 1)
          refine SepWP.fold (Entails.of_eq (show stackAt sf2.sp extHookStack = stackAt s.sp extHookStack by rw [hsp2_eq])) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩; sep_frame
      · intro sf3 hpc3 hrun3 hsp3 hcs3 htr3 hinv4
        have hsp3_eq : sf3.sp = s.sp := hsp3.trans hsp2_eq
        wp_split_join hsp3 hcs3; wp_norm_hyp htr3
        by_cases hcap4 : gce.recv.prev.cap = 0#64
        · have hcap4_beq : (gce.recv.prev.cap == 0#64) = true := by simp [hcap4]
          wp_norm_hyp hcap4_beq
          refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A gce.recv.prev.ptr hcap4 hr_p_le)) (by sep_focus) ?_
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩, ?_⟩; sep_frame
        · have hcap4_beq : (gce.recv.prev.cap == 0#64) = false := beq_false_of_ne hcap4
          wp_norm_hyp hcap4_beq
          refine SepWP.fold (vecU8Rest_nonzero_entails A gce.recv.prev.ptr hcap4 hr_p_le hr_p_lt) (by sep_focus) ?_
          refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hpos4, _, hisize4⟩
          have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          apply SepWP.seq_inImage (mid := entry_addr + bv% (ls_off% "__rustc::__rust_dealloc" - 0x5b9b8)) hinv4
          wp_steps
          refine SepWP.fold (Entails.of_eq (show stackAt s.sp extHookStack = stackAt sf3.sp extHookStack by rw [hsp3_eq])) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          rintro ⟨hF_d4, hsym_d4⟩
          wp_call h_dealloc (gce.recv.prev.ptr, gce.recv.prev.cap.toNat, 1)
          wp_steps
          refine SepWP.fold (Entails.of_eq (show stackAt sf3.sp extHookStack = stackAt s.sp extHookStack by rw [hsp3_eq])) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩, ?_⟩; sep_frame

/-- Iterated ring-buffer head pointer after popping `k` elements from the front. -/
def iterHead (cap : Nat) (head : BitVec 64) : Nat → BitVec 64
  | 0 => head
  | k + 1 => iterHead cap (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap 1)) k

/-- Iterated `[sp + 24]` scratch slot value after popping `k` elements from the front. -/
def iterL2 (l2 : BitVec 64) : List ChainEpochGhost → Nat → BitVec 64
  | _, 0 => l2
  | [], _ + 1 => l2
  | gce :: epochs', k + 1 => iterL2 gce.recv.prev.ptr epochs' k

theorem k_plus_3_props (k : Nat) {cap : BitVec 64}
    (hk : k + 2 < cap.toNat) (hcap : cap.toNat * 112 < 2 ^ 63) :
    BitVec.ofNat 64 (k + 3) + 18446744073709551615#64 = BitVec.ofNat 64 (k + 2) ∧
    BitVec.ofNat 64 (k + 3) - 1#64 = BitVec.ofNat 64 (k + 2) ∧
    BitVec.ule (BitVec.ofNat 64 (k + 2)) 1#64 = false ∧
    BitVec.ult 1#64 (BitVec.ofNat 64 (k + 2)) = true ∧
    (BitVec.ofNat 64 (k + 2) == 1#64) = false ∧
    BitVec.ult (BitVec.ofNat 64 (k + 2)) 1#64 = false := by
  have hlt3 : k + 3 < 18446744073709551616 := by omega
  have hlt2 : k + 2 < 18446744073709551616 := by omega
  have hsub : BitVec.ofNat 64 (k + 3) - 1#64 = BitVec.ofNat 64 (k + 2) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt3, Nat.mod_eq_of_lt hlt2]
    omega
  have hadd : BitVec.ofNat 64 (k + 3) + 18446744073709551615#64 =
      BitVec.ofNat 64 (k + 3) - 1#64 := by bv_kernel
  have hule : BitVec.ule (BitVec.ofNat 64 (k + 2)) 1#64 = false := by
    simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt2]
  have hult1 : BitVec.ult 1#64 (BitVec.ofNat 64 (k + 2)) = true := by
    simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt2]
  have hne1 : (BitVec.ofNat 64 (k + 2) == 1#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h
    have htn := congrArg BitVec.toNat h
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt2] at htn
  have hult2 : BitVec.ult (BitVec.ofNat 64 (k + 2)) 1#64 = false := by
    simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt2]
  exact ⟨hadd.trans hsub, hsub, hule, hult1, hne1, hult2⟩

theorem sendKey_pop_check_zero {img : Obj.Image}
    {ext : String → Option (State → State)}
    (s sm : State) (selfPtr cap : BitVec 64)
    (ce2 : ChainEpoch) (links'' : List ChainEpoch) (P : SepProp)
    (hlen'_le : (ce2 :: links'').length ≤ cap.toNat) (hcap_lt : cap.toNat * 112 < 2 ^ 63)
    (hpcm : sm.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainSendKeyName + 148#64)
    (hrunm : sm.status = .Running) (hsp_m : sm.sp = s.sp) (hsp_align_m : sm.spAligned = true)
    (hx19_m : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hx20_m : sm.readReg64 (.gpr 20#5) = selfPtr)
    (hx22_m : sm.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (vecDequePhysIdx (s.readReg64 (.gpr 22#5)).toNat cap.toNat 1))
    (hx27_m : sm.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (ce2 :: links'').length)
    (hx28_m : sm.readReg64 (.gpr 28#5) = 2#64)
    (hx29_m : sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5))
    (htr_m : sm.trace = s.trace) (hv_m : calleeSavedVRegs sm = calleeSavedVRegs s) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    let entry := prog.fnAddr chainSendKeyName
    SepWP prog (entry + 344#64) sm P
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.spAligned = true ∧
         sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sf.readReg64 (.gpr 20#5) = selfPtr ∧
         sf.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (vecDequePhysIdx (s.readReg64 (.gpr 22#5)).toNat cap.toNat 1) ∧
         sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (ce2 :: links'').length ∧
         sf.readReg64 (.gpr 28#5) = 1#64 ∧ sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
         sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (P' ⊢ P)) := by
  intro prog entry
  have hfn : libsignalSessionCode.fnOff chainSendKeyName = 0x5b9b8 := chainSendKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b9b8 596
  clear hfn
  dsimp only [prog, entry] at *
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainSendKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  have ⟨hx27_ne0, _, _⟩ := ofNat_cons_len_props ce2 links'' hlen'_le hcap_lt
  wp_norm_hyp hx19_m; wp_norm_hyp hx20_m; wp_norm_hyp hx22_m; wp_norm_hyp hx27_m
  wp_norm_hyp hx28_m; wp_norm_hyp hx29_m; wp_norm_hyp htr_m; wp_norm_hyp hv_m; wp_norm_hyp hx27_ne0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨⟨hsp_m, hsp_align_m, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩, Entails.refl _⟩

theorem sendKey_pop_check_succ {img : Obj.Image}
    {ext : String → Option (State → State)}
    (s sm : State) (selfPtr cap head1 : BitVec 64) (k : Nat)
    (links' : List ChainEpoch) (P : SepProp)
    (hk_lt_cap : k + 2 < cap.toNat) (hcap_lt : cap.toNat * 112 < 2 ^ 63)
    (hpcm : sm.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainSendKeyName + 148#64)
    (hrunm : sm.status = .Running) (hsp_align_m : sm.spAligned = true)
    (hx19_m : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hx20_m : sm.readReg64 (.gpr 20#5) = selfPtr)
    (hx22_m : sm.readReg64 (.gpr 22#5) = head1)
    (hx27_m : sm.readReg64 (.gpr 27#5) = BitVec.ofNat 64 links'.length)
    (hx28_m : sm.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (k + 3))
    (hx29_m : sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5))
    (htr_m : sm.trace = s.trace) (hv_m : calleeSavedVRegs sm = calleeSavedVRegs s) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    let entry := prog.fnAddr chainSendKeyName
    SepWP prog (entry + 164#64) sm P
      (fun sm2 P2 =>
        (sm2.sp = sm.sp ∧ sm2.spAligned = true ∧
         sm2.readReg64 (.gpr 8#5) = BitVec.ofNat 64 links'.length ∧
         sm2.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sm2.readReg64 (.gpr 20#5) = selfPtr ∧
         sm2.readReg64 (.gpr 22#5) = head1 ∧ sm2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (k + 2) ∧
         sm2.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
         sm2.trace = s.trace ∧ calleeSavedVRegs sm2 = calleeSavedVRegs s) ∧
        (P2 ⊢ P)) := by
  intro prog entry
  have hfn : libsignalSessionCode.fnOff chainSendKeyName = 0x5b9b8 := chainSendKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b9b8 596
  clear hfn
  dsimp only [prog, entry] at *
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainSendKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  have ⟨hk_add, hk_sub, hk_ule, hk_ult1, hk_ne1, hk_ult2⟩ := k_plus_3_props k hk_lt_cap hcap_lt
  wp_norm_hyp hx19_m; wp_norm_hyp hx20_m; wp_norm_hyp hx22_m; wp_norm_hyp hx27_m
  wp_norm_hyp hx28_m; wp_norm_hyp hx29_m; wp_norm_hyp htr_m; wp_norm_hyp hv_m
  wp_norm_hyp hk_add; wp_norm_hyp hk_sub; wp_norm_hyp hk_ule; wp_norm_hyp hk_ult1
  wp_norm_hyp hk_ne1; wp_norm_hyp hk_ult2
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨⟨by wp_norm_goal, hsp_align_m, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩, Entails.refl _⟩

theorem zip_set_snd {α β : Type} :
    ∀ (xs : List α) (ys : List β) (i : Nat) (x : α) (y' : β),
      xs[i]? = some x → (xs.zip ys).set i (x, y') = xs.zip (ys.set i y')
  | _ :: _, _ :: _, 0, _, _, h => by cases h; rfl
  | _ :: xs, _ :: ys, i + 1, x, y', h => by
      simp only [List.zip_cons_cons, List.set_cons_succ]; exact congrArg (_ :: ·) (zip_set_snd xs ys i x y' h)
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], 0, _, _, _ => rfl
  | _ :: _, [], _ + 1, _, _, _ => rfl

theorem onPanic_sendKey_of_trace_eq {s0 s sf : State} {P : Prop} {hpan : SepProp}
    (hP : P) (hs : s.trace = s0.trace)
    (hp : s.mem ⊨ (⌜sf.trace = s.trace⌝ ∗ anyHeap) ∗ hpan) :
    s.mem ⊨ ⌜(P ∧ sf.trace = s0.trace) ∨ (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rw [satisfies_pure_sepConj]
  exact ⟨Or.inl ⟨hP, hp.1.trans hs⟩, Satisfies.mono (entails_anyHeap _) hp.2⟩

theorem sendKey_pop_loop {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (selfPtr cap ptr : BitVec 64) (hcap_lt : cap.toNat * 112 < 2 ^ 63) (k : Nat) :
    ∀ (head l2 : BitVec 64) (epochs : List ChainEpochGhost) (links : List ChainEpoch)
      (_ : k + 1 < links.length) (_ : links.length ≤ cap.toNat) (_ : epochs.length = links.length)
      (s : State) (_ : ImgCallInv img s)
      (_ : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainSendKeyName + 164#64)
      (_ : s.status = .Running) (_ : s.spAligned = true)
      (_ : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 links.length)
      (_ : s.readReg64 (.gpr 20#5) = selfPtr) (_ : s.readReg64 (.gpr 22#5) = head)
      (_ : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (k + 2)),
      let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
      let entry := prog.fnAddr chainSendKeyName
      SepWP prog (entry + 344#64) s
        (popLoopPre A s.sp selfPtr cap ptr head l2 epochs links)
        (fun sf P' =>
          (sf.sp = s.sp ∧ sf.spAligned = true ∧
           sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sf.readReg64 (.gpr 20#5) = selfPtr ∧
           sf.readReg64 (.gpr 22#5) = iterHead cap.toNat head (k + 1) ∧
           sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (links.drop (k + 1)).length ∧
           sf.readReg64 (.gpr 28#5) = 1#64 ∧ sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
           sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
          (P' ⊢ popLoopPre A s.sp selfPtr cap ptr
            (iterHead cap.toNat head (k + 1)) (iterL2 l2 epochs (k + 1))
            (epochs.drop (k + 1)) (links.drop (k + 1)))) := by
  induction k with
  | zero =>
    intro head l2 epochs links hk hlen_le hlen_eq s hF hpc hrun hsp_align hx8 hx20 hx22 hx28 prog entry
    rcases links with _ | ⟨ce, links'⟩; · simp at hk
    rcases epochs with _ | ⟨gce, epochs'⟩; · simp at hlen_eq
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen_eq
    have hstep := sendKey_pop_step hdealloc selfPtr cap ptr head l2 gce epochs' ce links'
      hlen_le hlen_eq s hF hpc hrun hsp_align hx8 hx20 hx22
    dsimp only at hstep
    refine SepWP.seq_entails_inImage hF hstep ?_
    rintro sm hpcm hrunm hFm ⟨hsp_m, hsp_align_m, hx19_m, hx20_m, hx22_m, hx27_m, hx28_m, hx29_m, htr_m, hv_m⟩
    rcases links' with _ | ⟨ce2, links''⟩; · simp at hk
    have hlen'_le : (ce2 :: links'').length ≤ cap.toNat := by simp only [List.length_cons] at hlen_le ⊢; omega
    have hx22_m' : sm.readReg64 (.gpr 22#5) =
        BitVec.ofNat 64 (vecDequePhysIdx (s.readReg64 (.gpr 22#5)).toNat cap.toNat 1) := by
      rw [hx22]; exact hx22_m
    have hchk := sendKey_pop_check_zero s sm selfPtr cap ce2 links''
      (popLoopPre A s.sp selfPtr cap ptr
        (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)) gce.recv.prev.ptr epochs' (ce2 :: links''))
      hlen'_le hcap_lt hpcm hrunm hsp_m hsp_align_m hx19_m hx20_m hx22_m' hx27_m (hx28_m.trans hx28) hx29_m htr_m hv_m
    dsimp only at hchk; rw [hx22] at hchk
    simp only [iterHead, iterL2, List.drop_succ_cons, List.drop_zero]; exact hchk
  | succ k ih =>
    intro head l2 epochs links hk hlen_le hlen_eq s hF hpc hrun hsp_align hx8 hx20 hx22 hx28 prog entry
    rcases links with _ | ⟨ce, links'⟩; · simp at hk
    rcases epochs with _ | ⟨gce, epochs'⟩; · simp at hlen_eq
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen_eq
    have hstep := sendKey_pop_step hdealloc selfPtr cap ptr head l2 gce epochs' ce links'
      hlen_le hlen_eq s hF hpc hrun hsp_align hx8 hx20 hx22
    dsimp only at hstep
    refine SepWP.seq_entails_inImage hF hstep ?_
    rintro sm hpcm hrunm hFm ⟨hsp_m, hsp_align_m, hx19_m, hx20_m, hx22_m, hx27_m, hx28_m, hx29_m, htr_m, hv_m⟩
    have hk_lt_cap : k + 2 < cap.toNat := by simp only [List.length_cons] at hk hlen_le; omega
    have hchk := sendKey_pop_check_succ s sm selfPtr cap
      (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)) k links'
      (popLoopPre A s.sp selfPtr cap ptr
        (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)) gce.recv.prev.ptr epochs' links')
      hk_lt_cap hcap_lt hpcm hrunm hsp_align_m hx19_m hx20_m hx22_m hx27_m (hx28_m.trans hx28) hx29_m htr_m hv_m
    dsimp only at hchk
    refine SepWP.seq_entails_inImage hFm hchk ?_
    rintro sm2 hpcm2 hrunm2 hFm2 ⟨hsp_m2, hsp_align_m2, hx8_m2, hx19_m2, hx20_m2, hx22_m2, hx28_m2, hx29_m2, htr_m2, hv_m2⟩
    have hsp_eq : s.sp = sm2.sp := (hsp_m2.trans hsp_m).symm
    rw [hsp_eq]
    have hk' : k + 1 < links'.length := by simp only [List.length_cons] at hk; omega
    have hlen'_le : links'.length ≤ cap.toNat := by simp only [List.length_cons] at hlen_le; omega
    have hih := ih (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)) gce.recv.prev.ptr
      epochs' links' hk' hlen'_le hlen_eq sm2 hFm2 hpcm2 hrunm2 hsp_align_m2 hx8_m2 hx20_m2 hx22_m2 hx28_m2
    dsimp only at hih; simp only [iterHead, iterL2, List.drop_succ_cons]
    refine SepWP.conseq hih ?_
    rintro sf P' ⟨⟨hsp_f, hsp_align_f, hx19_f, hx20_f, hx22_f, hx27_f, hx28_f, hx29_f, htr_f, hv_f⟩, hent_f⟩
    exact ⟨⟨hsp_f, hsp_align_f, hx19_f.trans hx19_m2, hx20_f, hx22_f, hx27_f, hx28_f,
      hx29_f.trans hx29_m2, htr_f.trans htr_m2, hv_f.trans hv_m2⟩, hent_f⟩

/-- Minimal heap footprint of the `+344..+376` block that clears `links1[0].send.next`. -/
def clearFrontPre (A : RustAlloc) (selfPtr cap ptr head1 : BitVec 64)
    (epochs1 : List ChainEpochGhost) (links1 : List ChainEpoch) : SepProp :=
  (selfPtr ↦₆₄ cap) ∗ ((selfPtr + 8#64) ↦₆₄ ptr) ∗ ((selfPtr + 16#64) ↦₆₄ head1) ∗
  vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A)
    cap ptr head1 (epochs1.zip links1)

theorem chainEpochAt_unpack_send_next (A : RustAlloc) (gce : ChainEpochGhost) (ce : ChainEpoch)
    (a : BitVec 64) :
    chainEpochAt A (gce, ce) a ⊢
      ⌜ce.send.next.length ≤ gce.send.next.cap.toNat ∧ gce.send.next.cap.toNat < 2 ^ 63 ∧ gce.send.next.ptr ≠ 0⌝ ∗
      (a ↦₆₄ gce.send.next.cap) ∗ ((a + 8#64) ↦₆₄ gce.send.next.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ce.send.next.length) ∗
      (gce.send.next.ptr ↦ₛ ce.send.next) ∗ vecU8Rest A gce.send.next.cap gce.send.next.ptr ce.send.next.length ∗
      keyHistoryAt A (a + 24#64) gce.send.prev ce.send.prev ∗
      ((a + 48#64) ↦₃₂ ce.send.ctr) ∗ memRegion (a + 52#64) 4 ∗
      chainEpochDirectionAt A (a + 56#64) gce.recv ce.recv := by
  unfold chainEpochAt; dsimp only
  refine Entails.trans (sepConj_mono_left (chainEpochDirectionAt_unpack_next A a gce.send ce.send)) ?_
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem chainEpochAt_pack_clearNext (A : RustAlloc) (gce : ChainEpochGhost) (ce : ChainEpoch)
    (a : BitVec 64) (hle : ce.send.next.length ≤ gce.send.next.cap.toNat)
    (hcap : gce.send.next.cap.toNat < 2 ^ 63) (hptr : gce.send.next.ptr ≠ 0) :
    (a ↦₆₄ gce.send.next.cap) ∗ ((a + 8#64) ↦₆₄ gce.send.next.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      (gce.send.next.ptr ↦ₛ ce.send.next) ∗ vecU8Rest A gce.send.next.cap gce.send.next.ptr ce.send.next.length ∗
      keyHistoryAt A (a + 24#64) gce.send.prev ce.send.prev ∗ ((a + 48#64) ↦₃₂ ce.send.ctr) ∗ memRegion (a + 52#64) 4 ∗
      chainEpochDirectionAt A (a + 56#64) gce.recv ce.recv ⊢
      chainEpochAt A (gce, { ce with send := ce.send.clearNext }) a := by
  unfold chainEpochAt; dsimp only
  have h1 := chainEpochDirectionAt_pack_clearNext A a gce.send ce.send hle hcap hptr
  rw [show (a ↦₆₄ gce.send.next.cap) ∗ ((a + 8#64) ↦₆₄ gce.send.next.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      (gce.send.next.ptr ↦ₛ ce.send.next) ∗ vecU8Rest A gce.send.next.cap gce.send.next.ptr ce.send.next.length ∗
      keyHistoryAt A (a + 24#64) gce.send.prev ce.send.prev ∗ ((a + 48#64) ↦₃₂ ce.send.ctr) ∗ memRegion (a + 52#64) 4 ∗
      chainEpochDirectionAt A (a + 56#64) gce.recv ce.recv =
    ((a ↦₆₄ gce.send.next.cap) ∗ ((a + 8#64) ↦₆₄ gce.send.next.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      (gce.send.next.ptr ↦ₛ ce.send.next) ∗ vecU8Rest A gce.send.next.cap gce.send.next.ptr ce.send.next.length ∗
      keyHistoryAt A (a + 24#64) gce.send.prev ce.send.prev ∗ ((a + 48#64) ↦₃₂ ce.send.ctr) ∗ memRegion (a + 52#64) 4) ∗
    chainEpochDirectionAt A (a + 56#64) gce.recv ce.recv by ac_rfl]
  exact sepConj_mono_left h1

theorem sendKey_from_344 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (selfPtr cap ptr head1 : BitVec 64)
    (epochs1 : List ChainEpochGhost) (links1 : List ChainEpoch)
    (h0 : 0 < links1.length) (hlen_le : links1.length ≤ cap.toNat) (hlen_eq : epochs1.length = links1.length)
    (s : State)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainSendKeyName + 344#64)
    (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hx20 : s.readReg64 (.gpr 20#5) = selfPtr) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    let entry := prog.fnAddr chainSendKeyName
    let links2 := links1.set 0 { links1[0] with send := links1[0].send.clearNext }
    SepWP prog (entry + 380#64) s
      (clearFrontPre A selfPtr cap ptr head1 epochs1 links1)
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.spAligned = true ∧
         sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sf.readReg64 (.gpr 20#5) = selfPtr ∧
         sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧ sf.readReg64 (.gpr 28#5) = 1#64 ∧
         sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧ sf.trace = s.trace ∧
         calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (P' ⊢ clearFrontPre A selfPtr cap ptr head1 epochs1 links2)) := by
  intro prog entry links2
  have hfn : libsignalSessionCode.fnOff chainSendKeyName = 0x5b9b8 := chainSendKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b9b8 596
  clear hfn
  dsimp only [prog, entry, links2] at *
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainSendKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches; unfold clearFrontPre
  have hzip_len : (epochs1.zip links1).length = links1.length := by simp [hlen_eq]
  have hzip_le : (epochs1.zip links1).length ≤ cap.toNat := by omega
  have hzip_0 : 0 < (epochs1.zip links1).length := by omega
  refine SepWP.fold (vecDequeRingBuf_get_physIdx A cap ptr head1 (epochs1.zip links1) hzip_le hzip_0) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hhead, hcap_lt, hptr⟩
  have hzip_get0 : (epochs1.zip links1)[0] = (epochs1[0]'(by omega), links1[0]'h0) := by simp [List.getElem_zip]
  rw [hzip_get0]
  refine SepWP.fold (chainEpochAt_unpack_send_next A (epochs1[0]'(by omega)) (links1[0]'h0)
    (ptr + BitVec.ofNat 64 (vecDequePhysIdx head1.toNat cap.toNat 0 * 112))) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hle0, hcap0, hptr0⟩
  have hmadd0 := physIdx_zero_madd_eq (ptr := ptr) hhead hcap_lt
  have hpack_ce := chainEpochAt_pack_clearNext A (epochs1[0]'(by omega)) (links1[0]'h0)
    (ptr + BitVec.ofNat 64 (vecDequePhysIdx head1.toNat cap.toNat 0 * 112)) hle0 hcap0 hptr0
  have hset := vecDequeRingBuf_set_physIdx A cap ptr head1 (epochs1.zip links1)
    (epochs1[0]'(by omega), { links1[0] with send := links1[0].send.clearNext })
    hhead hcap_lt hptr hzip_le hzip_0
  dsimp only at hset
  have hzip_set : (epochs1.zip links1).set 0
      (epochs1[0]'(by omega), { links1[0] with send := links1[0].send.clearNext }) =
      epochs1.zip (links1.set 0 { links1[0] with send := links1[0].send.clearNext }) :=
    zip_set_snd epochs1 links1 0 (epochs1[0]'(by omega)) _ (List.getElem?_eq_getElem (by omega))
  rw [hzip_set] at hset
  wp_norm_hyp hx20; wp_norm_hyp hmadd0; wp_steps
  refine SepWP.fold hpack_ce (by sep_focus) ?_
  refine SepWP.fold hset (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨⟨by wp_norm_goal, hsp_align, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩, ?_⟩; sep_frame

/-! ## Relocatable `[LibsignalPlacement]` Pop Loop and `next_key_internal` Panic (`blkPC_362`, `blkPC_367`) -/

theorem nextKeyInternal_panic_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (hovf : ((blkPC_362).rebase (blkPl_362).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") = some Rust.panicked)
    (hassert : ((blkPC_362).rebase (blkPl_362).base H).externAt?
      (lsρ "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_") = some Rust.panicked) :
    NextKeyInternalPanicPlacedOkX H := by
  unfold NextKeyInternalPanicPlacedOkX; wpp_init x s0
  rcases x with ⟨out, nextA, next, ctrA, ctr⟩; dsimp only [nextKeyInternalPanicSpecX] at *
  refine SepWPp.rw_pre (by rw [stackAt_nextKeyInternalPanic_split s0.sp]) ?_; sep_elim_exists; subst h_4
  by_cases hlen32 : next.length = 32
  · have hctr : ctr = 0xffffffff#32 := h.resolve_left (not_not.mpr hlen32); subst hctr
    have hx2_32 : s0.readReg64 (.gpr 2#5) = 32#64 := by rw [h_3, hlen32]
    wp_norm_hyp hx2_32
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow")
    wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hovf) fun hm => ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨by simp [Rust.panicked, arm64_norm], Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm⟩
  · have hne_bv : BitVec.ofNat 64 next.length ≠ 32#64 := fun heq => by
      have htn := congrArg BitVec.toNat heq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_5] at htn; exact hlen32 htn
    have hne : (s0.readReg64 (.gpr 2#5) + 18446744073709551584#64 == 0#64) = false := by rw [h_3]; revert hne_bv; bv_kernel
    have hne2 : (s0.readReg64 (.gpr 2#5) == 32#64) = false := by rw [h_3]; exact beq_false_of_ne hne_bv
    have hne3 : (s0.readReg64 (.gpr 2#5) != 32#64) = true := by rw [h_3]; simp [hne_bv]
    wp_norm_hyp hne; wp_norm_hyp hne2; wp_norm_hyp hne3
    apply SepWPp.of_sepWP (mid := lsρ "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_")
    wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hassert) fun hm => ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨by simp [Rust.panicked, arm64_norm], Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm⟩

theorem SepWP.seq_cps {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  SepWP.seq h (fun _ _ _ _ h2 => h2)

theorem SepWP.seq_entails_plain {prog : Program}
    {mid target : BitVec 64} {s : State} {P P_mid : SepProp} {φ : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post := by
  unfold SepWP; intro R hm hL
  rcases h1.elim hm hL with ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hφ, hent⟩ | ⟨hoom, hfalse⟩⟩
  · rcases (h2 sm hpcm hrunm hφ).elim (Satisfies.mono (sepConj_mono_left hent) hmm) (hsteps1.codeLoaded hL) with ⟨sf, hsteps2, hout⟩
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hoom, hfalse⟩⟩

theorem SepWP.join_plain {prog : Program}
    {join_pc target : BitVec 64} {s : State} {P P_join : SepProp} {post : State → SepProp → Prop}
    (h1 : SepWP prog join_pc s P (fun sm Pm =>
      sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ sm.trace = s.trace ∧ (Pm ⊢ P_join)))
    (h2 : ∀ sm, sm.pc = join_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → sm.trace = s.trace → SepWP prog target sm P_join post) :
    SepWP prog target s P post := by
  unfold SepWP; intro R hm hL
  rcases h1.elim hm hL with ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hsp, hcs, htr, hent⟩ | ⟨hoom, hfalse⟩⟩
  · rcases (h2 sm hpcm hrunm hsp hcs htr).elim (Satisfies.mono (sepConj_mono_left hent) hmm) (hsteps1.codeLoaded hL) with ⟨sf, hsteps2, hout⟩
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hoom, hfalse⟩⟩

set_option maxHeartbeats 1600000 in
theorem sendKey_pop_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocExternSpecWithStack A extHookStack))
    (selfPtr cap ptr head l2 : BitVec 64) (gce : ChainEpochGhost) (epochs' : List ChainEpochGhost)
    (ce : ChainEpoch) (links' : List ChainEpoch)
    (hlen_le : (ce :: links').length ≤ cap.toNat) (hlen_eq : epochs'.length = links'.length)
    (s : State) (hpc : s.pc = (blkPl_367).base + 164#64) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (ce :: links').length)
    (hx20 : s.readReg64 (.gpr 20#5) = selfPtr) (hx22 : s.readReg64 (.gpr 22#5) = head) :
    let head1 := BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)
    SepWP ((blkPC_367).rebase (blkPl_367).base H) ((blkPl_367).base + 148#64) s
      (popLoopPre A s.sp selfPtr cap ptr head l2 (gce :: epochs') (ce :: links'))
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.spAligned = true ∧
         sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sf.readReg64 (.gpr 20#5) = selfPtr ∧
         sf.readReg64 (.gpr 22#5) = head1 ∧ sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 links'.length ∧
         sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧ sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
         sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (P' ⊢ popLoopPre A s.sp selfPtr cap ptr head1 gce.recv.prev.ptr epochs' links')) := by
  intro head1; dsimp only [head1] at *; unfold popLoopPre; simp only [List.zip_cons_cons]
  have hzip_le : ((gce, ce) :: epochs'.zip links').length ≤ cap.toNat := by
    simp only [List.length_cons, List.length_zip, hlen_eq, Nat.min_self] at hlen_le ⊢; exact hlen_le
  refine SepWP.fold (vecDequeRingBuf_get_front A cap ptr head (gce, ce) (epochs'.zip links') hzip_le) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hhead, hcap_lt, hptr⟩
  refine SepWP.fold (chainEpochAt_unpack_pop A gce ce (ptr + head * 112#64)) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hs_n_le, hs_n_lt, hs_n_ptr, hs_p_le, hs_p_lt, hs_p_ptr, hr_n_le, hr_n_lt, hr_n_ptr, hr_p_le, hr_p_lt, hr_p_ptr⟩
  have ⟨hx8_ne0, hx8_add, hx8_sub⟩ := ofNat_cons_len_props ce links' hlen_le hcap_lt
  have hhead1_eq := physIdx_one_eq hhead hcap_lt; have hcmn := cap_ne_neg_one hs_n_lt
  wp_norm_hyp hsp_align; wp_norm_hyp hx8; wp_norm_hyp hx20; wp_norm_hyp hx22
  wp_norm_hyp hx8_ne0; wp_norm_hyp hx8_add; wp_norm_hyp hx8_sub; wp_norm_hyp hhead1_eq; wp_norm_hyp hcmn
  apply SepWP.seq_cps (mid := (blkPl_367).base + 232#64); wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine SepWP.join_plain (join_pc := (blkPl_367).base + 248#64)
    (P_join :=
      ((s.sp + 8#64) ↦₆₄ ptr) ∗ ((s.sp + 16#64) ↦₆₄ cap) ∗ ((s.sp + 24#64) ↦₆₄ gce.recv.prev.ptr) ∗
      ((selfPtr + 16#64) ↦₆₄ head1) ∗ ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links'.length) ∗
      vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head1 (epochs'.zip links') ∗
      (gce.send.prev.ptr ↦ₛ ce.send.prev.data) ∗ vecU8Rest A gce.send.prev.cap gce.send.prev.ptr ce.send.prev.data.length ∗
      (gce.recv.next.ptr ↦ₛ ce.recv.next) ∗ vecU8Rest A gce.recv.next.cap gce.recv.next.ptr ce.recv.next.length ∗
      (gce.recv.prev.ptr ↦ₛ ce.recv.prev.data) ∗ vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data.length ∗
      A.pool ∗ stackAt s.sp extHookStack) ?_ ?_
  · by_cases hcap1 : gce.send.next.cap = 0#64
    · have hcap1_beq : (gce.send.next.cap == 0#64) = true := by simp [hcap1]
      wp_norm_hyp hcap1_beq
      refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A gce.send.next.ptr hcap1 hs_n_le)) (by sep_focus) ?_
      wp_steps
      refine SepWP.fold (chainEpochSlot_entails_memRegion_112 (ptr + head * 112#64)
        gce.send.next.cap gce.send.next.ptr (BitVec.ofNat 64 ce.send.next.length)
        gce.send.prev.cap gce.send.prev.ptr (BitVec.ofNat 64 ce.send.prev.data.length)
        gce.recv.next.cap gce.recv.next.ptr (BitVec.ofNat 64 ce.recv.next.length)
        gce.recv.prev.cap gce.recv.prev.ptr (BitVec.ofNat 64 ce.recv.prev.data.length)
        ce.send.ctr ce.recv.ctr) (by sep_focus) ?_
      refine SepWP.fold (vecDequeRingBuf_pop_front_mul A cap ptr head (gce, ce) (epochs'.zip links')
        hhead hcap_lt hptr hzip_le) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩; sep_frame
    · have hcap1_beq : (gce.send.next.cap == 0#64) = false := beq_false_of_ne hcap1
      wp_norm_hyp hcap1_beq
      refine SepWP.fold (vecU8Rest_nonzero_entails A gce.send.next.ptr hcap1 hs_n_le hs_n_lt) (by sep_focus) ?_
      refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hpos1, _, hisize1⟩
      have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      wp_steps
      refine SepWP.fold (chainEpochSlot_entails_memRegion_112 (ptr + head * 112#64)
        gce.send.next.cap gce.send.next.ptr (BitVec.ofNat 64 ce.send.next.length)
        gce.send.prev.cap gce.send.prev.ptr (BitVec.ofNat 64 ce.send.prev.data.length)
        gce.recv.next.cap gce.recv.next.ptr (BitVec.ofNat 64 ce.recv.next.length)
        gce.recv.prev.cap gce.recv.prev.ptr (BitVec.ofNat 64 ce.recv.prev.data.length)
        ce.send.ctr ce.recv.ctr) (by sep_focus) ?_
      refine SepWP.fold (vecDequeRingBuf_pop_front_mul A cap ptr head (gce, ce) (epochs'.zip links')
        hhead hcap_lt hptr hzip_le) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      wp_call hdealloc (gce.send.next.ptr, gce.send.next.cap.toNat, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩; sep_frame
  · intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
    have hsp1_eq : sf1.sp = s.sp := hsp1; wp_split_join hsp1 hcs1; wp_norm_hyp htr1
    refine SepWP.join_plain (join_pc := (blkPl_367).base + 268#64)
      (P_join :=
        ((s.sp + 8#64) ↦₆₄ ptr) ∗ ((s.sp + 16#64) ↦₆₄ cap) ∗ ((s.sp + 24#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((selfPtr + 16#64) ↦₆₄ head1) ∗ ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links'.length) ∗
        vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head1 (epochs'.zip links') ∗
        (gce.recv.next.ptr ↦ₛ ce.recv.next) ∗ vecU8Rest A gce.recv.next.cap gce.recv.next.ptr ce.recv.next.length ∗
        (gce.recv.prev.ptr ↦ₛ ce.recv.prev.data) ∗ vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data.length ∗
        A.pool ∗ stackAt s.sp extHookStack) ?_ ?_
    · by_cases hcap2 : gce.send.prev.cap = 0#64
      · have hcap2_beq : (gce.send.prev.cap == 0#64) = true := by simp [hcap2]
        wp_norm_hyp hcap2_beq
        refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A gce.send.prev.ptr hcap2 hs_p_le)) (by sep_focus) ?_
        wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩; sep_frame
      · have hcap2_beq : (gce.send.prev.cap == 0#64) = false := beq_false_of_ne hcap2
        wp_norm_hyp hcap2_beq
        refine SepWP.fold (vecU8Rest_nonzero_entails A gce.send.prev.ptr hcap2 hs_p_le hs_p_lt) (by sep_focus) ?_
        refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hpos2, _, hisize2⟩
        have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
        wp_steps
        refine SepWP.fold (Entails.of_eq (show stackAt s.sp extHookStack = stackAt sf1.sp extHookStack by rw [hsp1_eq])) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        wp_call hdealloc (gce.send.prev.ptr, gce.send.prev.cap.toNat, 1)
        refine SepWP.fold (Entails.of_eq (show stackAt sf1.sp extHookStack = stackAt s.sp extHookStack by rw [hsp1_eq])) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩; sep_frame
    · intro sf2 hpc2 hrun2 hsp2 hcs2 htr2
      have hsp2_eq : sf2.sp = s.sp := hsp2.trans hsp1_eq; wp_split_join hsp2 hcs2; wp_norm_hyp htr2
      refine SepWP.join_plain (join_pc := (blkPl_367).base + 288#64)
        (P_join :=
          ((s.sp + 8#64) ↦₆₄ ptr) ∗ ((s.sp + 16#64) ↦₆₄ cap) ∗ ((s.sp + 24#64) ↦₆₄ gce.recv.prev.ptr) ∗
          ((selfPtr + 16#64) ↦₆₄ head1) ∗ ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links'.length) ∗
          vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) cap ptr head1 (epochs'.zip links') ∗
          (gce.recv.prev.ptr ↦ₛ ce.recv.prev.data) ∗ vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr ce.recv.prev.data.length ∗
          A.pool ∗ stackAt s.sp extHookStack) ?_ ?_
      · by_cases hcap3 : gce.recv.next.cap = 0#64
        · have hcap3_beq : (gce.recv.next.cap == 0#64) = true := by simp [hcap3]
          wp_norm_hyp hcap3_beq
          refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A gce.recv.next.ptr hcap3 hr_n_le)) (by sep_focus) ?_
          wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩; sep_frame
        · have hcap3_beq : (gce.recv.next.cap == 0#64) = false := beq_false_of_ne hcap3
          wp_norm_hyp hcap3_beq
          refine SepWP.fold (vecU8Rest_nonzero_entails A gce.recv.next.ptr hcap3 hr_n_le hr_n_lt) (by sep_focus) ?_
          refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hpos3, _, hisize3⟩
          have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          wp_steps
          refine SepWP.fold (Entails.of_eq (show stackAt s.sp extHookStack = stackAt sf2.sp extHookStack by rw [hsp2_eq])) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          wp_call hdealloc (gce.recv.next.ptr, gce.recv.next.cap.toNat, 1)
          refine SepWP.fold (Entails.of_eq (show stackAt sf2.sp extHookStack = stackAt s.sp extHookStack by rw [hsp2_eq])) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, by wp_norm_goal, ?_⟩; sep_frame
      · intro sf3 hpc3 hrun3 hsp3 hcs3 htr3
        have hsp3_eq : sf3.sp = s.sp := hsp3.trans hsp2_eq; wp_split_join hsp3 hcs3; wp_norm_hyp htr3
        by_cases hcap4 : gce.recv.prev.cap = 0#64
        · have hcap4_beq : (gce.recv.prev.cap == 0#64) = true := by simp [hcap4]
          wp_norm_hyp hcap4_beq
          refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A gce.recv.prev.ptr hcap4 hr_p_le)) (by sep_focus) ?_
          wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩, ?_⟩; sep_frame
        · have hcap4_beq : (gce.recv.prev.cap == 0#64) = false := beq_false_of_ne hcap4
          wp_norm_hyp hcap4_beq
          refine SepWP.fold (vecU8Rest_nonzero_entails A gce.recv.prev.ptr hcap4 hr_p_le hr_p_lt) (by sep_focus) ?_
          refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hpos4, _, hisize4⟩
          have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          wp_steps
          refine SepWP.fold (Entails.of_eq (show stackAt s.sp extHookStack = stackAt sf3.sp extHookStack by rw [hsp3_eq])) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          wp_call hdealloc (gce.recv.prev.ptr, gce.recv.prev.cap.toNat, 1)
          wp_steps
          refine SepWP.fold (Entails.of_eq (show stackAt sf3.sp extHookStack = stackAt s.sp extHookStack by rw [hsp3_eq])) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩, ?_⟩; sep_frame

theorem sendKey_pop_check_zero_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (s sm : State) (selfPtr cap : BitVec 64) (ce2 : ChainEpoch) (links'' : List ChainEpoch) (P : SepProp)
    (hlen'_le : (ce2 :: links'').length ≤ cap.toNat) (hcap_lt : cap.toNat * 112 < 2 ^ 63)
    (hpcm : sm.pc = (blkPl_367).base + 148#64) (hrunm : sm.status = .Running)
    (hsp_m : sm.sp = s.sp) (hsp_align_m : sm.spAligned = true)
    (hx19_m : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5)) (hx20_m : sm.readReg64 (.gpr 20#5) = selfPtr)
    (hx22_m : sm.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (vecDequePhysIdx (s.readReg64 (.gpr 22#5)).toNat cap.toNat 1))
    (hx27_m : sm.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (ce2 :: links'').length)
    (hx28_m : sm.readReg64 (.gpr 28#5) = 2#64) (hx29_m : sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5))
    (htr_m : sm.trace = s.trace) (hv_m : calleeSavedVRegs sm = calleeSavedVRegs s) :
    SepWP ((blkPC_367).rebase (blkPl_367).base H) ((blkPl_367).base + 344#64) sm P
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.spAligned = true ∧
         sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sf.readReg64 (.gpr 20#5) = selfPtr ∧
         sf.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (vecDequePhysIdx (s.readReg64 (.gpr 22#5)).toNat cap.toNat 1) ∧
         sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (ce2 :: links'').length ∧
         sf.readReg64 (.gpr 28#5) = 1#64 ∧ sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
         sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (P' ⊢ P)) := by
  have ⟨hx27_ne0, _, _⟩ := ofNat_cons_len_props ce2 links'' hlen'_le hcap_lt
  wp_norm_hyp hx19_m; wp_norm_hyp hx20_m; wp_norm_hyp hx22_m; wp_norm_hyp hx27_m
  wp_norm_hyp hx28_m; wp_norm_hyp hx29_m; wp_norm_hyp htr_m; wp_norm_hyp hv_m; wp_norm_hyp hx27_ne0
  wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨⟨hsp_m, hsp_align_m, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩, Entails.refl _⟩

theorem sendKey_pop_check_succ_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (s sm : State) (selfPtr cap head1 : BitVec 64) (k : Nat) (links' : List ChainEpoch) (P : SepProp)
    (hk_lt_cap : k + 2 < cap.toNat) (hcap_lt : cap.toNat * 112 < 2 ^ 63)
    (hpcm : sm.pc = (blkPl_367).base + 148#64) (hrunm : sm.status = .Running) (hsp_align_m : sm.spAligned = true)
    (hx19_m : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5)) (hx20_m : sm.readReg64 (.gpr 20#5) = selfPtr)
    (hx22_m : sm.readReg64 (.gpr 22#5) = head1) (hx27_m : sm.readReg64 (.gpr 27#5) = BitVec.ofNat 64 links'.length)
    (hx28_m : sm.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (k + 3)) (hx29_m : sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5))
    (htr_m : sm.trace = s.trace) (hv_m : calleeSavedVRegs sm = calleeSavedVRegs s) :
    SepWP ((blkPC_367).rebase (blkPl_367).base H) ((blkPl_367).base + 164#64) sm P
      (fun sm2 P2 =>
        (sm2.sp = sm.sp ∧ sm2.spAligned = true ∧
         sm2.readReg64 (.gpr 8#5) = BitVec.ofNat 64 links'.length ∧
         sm2.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sm2.readReg64 (.gpr 20#5) = selfPtr ∧
         sm2.readReg64 (.gpr 22#5) = head1 ∧ sm2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (k + 2) ∧
         sm2.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
         sm2.trace = s.trace ∧ calleeSavedVRegs sm2 = calleeSavedVRegs s) ∧
        (P2 ⊢ P)) := by
  have ⟨hk_add, hk_sub, hk_ule, hk_ult1, hk_ne1, hk_ult2⟩ := k_plus_3_props k hk_lt_cap hcap_lt
  wp_norm_hyp hx19_m; wp_norm_hyp hx20_m; wp_norm_hyp hx22_m; wp_norm_hyp hx27_m
  wp_norm_hyp hx28_m; wp_norm_hyp hx29_m; wp_norm_hyp htr_m; wp_norm_hyp hv_m
  wp_norm_hyp hk_add; wp_norm_hyp hk_sub; wp_norm_hyp hk_ule; wp_norm_hyp hk_ult1
  wp_norm_hyp hk_ne1; wp_norm_hyp hk_ult2
  wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨⟨by wp_norm_goal, hsp_align_m, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩, Entails.refl _⟩

theorem sendKey_pop_loop_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocExternSpecWithStack A extHookStack))
    (selfPtr cap ptr : BitVec 64) (hcap_lt : cap.toNat * 112 < 2 ^ 63) (k : Nat) :
    ∀ (head l2 : BitVec 64) (epochs : List ChainEpochGhost) (links : List ChainEpoch)
      (_ : k + 1 < links.length) (_ : links.length ≤ cap.toNat) (_ : epochs.length = links.length)
      (s : State) (_ : s.pc = (blkPl_367).base + 164#64) (_ : s.status = .Running)
      (_ : s.spAligned = true) (_ : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 links.length)
      (_ : s.readReg64 (.gpr 20#5) = selfPtr) (_ : s.readReg64 (.gpr 22#5) = head)
      (_ : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (k + 2)),
      SepWP ((blkPC_367).rebase (blkPl_367).base H) ((blkPl_367).base + 344#64) s
        (popLoopPre A s.sp selfPtr cap ptr head l2 epochs links)
        (fun sf P' =>
          (sf.sp = s.sp ∧ sf.spAligned = true ∧
           sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sf.readReg64 (.gpr 20#5) = selfPtr ∧
           sf.readReg64 (.gpr 22#5) = iterHead cap.toNat head (k + 1) ∧
           sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (links.drop (k + 1)).length ∧
           sf.readReg64 (.gpr 28#5) = 1#64 ∧ sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
           sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
          (P' ⊢ popLoopPre A s.sp selfPtr cap ptr
            (iterHead cap.toNat head (k + 1)) (iterL2 l2 epochs (k + 1))
            (epochs.drop (k + 1)) (links.drop (k + 1)))) := by
  induction k with
  | zero =>
    intro head l2 epochs links hk hlen_le hlen_eq s hpc hrun hsp_align hx8 hx20 hx22 hx28
    rcases links with _ | ⟨ce, links'⟩; · simp at hk
    rcases epochs with _ | ⟨gce, epochs'⟩; · simp at hlen_eq
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen_eq
    have hstep := sendKey_pop_step_placed hdealloc selfPtr cap ptr head l2 gce epochs' ce links'
      hlen_le hlen_eq s hpc hrun hsp_align hx8 hx20 hx22
    dsimp only at hstep; refine SepWP.seq_entails_plain hstep ?_
    rintro sm hpcm hrunm ⟨hsp_m, hsp_align_m, hx19_m, hx20_m, hx22_m, hx27_m, hx28_m, hx29_m, htr_m, hv_m⟩
    rcases links' with _ | ⟨ce2, links''⟩; · simp at hk
    have hlen'_le : (ce2 :: links'').length ≤ cap.toNat := by simp only [List.length_cons] at hlen_le ⊢; omega
    have hx22_m' : sm.readReg64 (.gpr 22#5) =
        BitVec.ofNat 64 (vecDequePhysIdx (s.readReg64 (.gpr 22#5)).toNat cap.toNat 1) := by rw [hx22]; exact hx22_m
    have hchk := sendKey_pop_check_zero_placed (H := H) s sm selfPtr cap ce2 links''
      (popLoopPre A s.sp selfPtr cap ptr
        (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)) gce.recv.prev.ptr epochs' (ce2 :: links''))
      hlen'_le hcap_lt hpcm hrunm hsp_m hsp_align_m hx19_m hx20_m hx22_m' hx27_m (hx28_m.trans hx28) hx29_m htr_m hv_m
    rw [hx22] at hchk; simp only [iterHead, iterL2, List.drop_succ_cons, List.drop_zero]; exact hchk
  | succ k ih =>
    intro head l2 epochs links hk hlen_le hlen_eq s hpc hrun hsp_align hx8 hx20 hx22 hx28
    rcases links with _ | ⟨ce, links'⟩; · simp at hk
    rcases epochs with _ | ⟨gce, epochs'⟩; · simp at hlen_eq
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen_eq
    have hstep := sendKey_pop_step_placed hdealloc selfPtr cap ptr head l2 gce epochs' ce links'
      hlen_le hlen_eq s hpc hrun hsp_align hx8 hx20 hx22
    dsimp only at hstep; refine SepWP.seq_entails_plain hstep ?_
    rintro sm hpcm hrunm ⟨hsp_m, hsp_align_m, hx19_m, hx20_m, hx22_m, hx27_m, hx28_m, hx29_m, htr_m, hv_m⟩
    have hk_lt_cap : k + 2 < cap.toNat := by simp only [List.length_cons] at hk hlen_le; omega
    have hchk := sendKey_pop_check_succ_placed (H := H) s sm selfPtr cap
      (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)) k links'
      (popLoopPre A s.sp selfPtr cap ptr
        (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)) gce.recv.prev.ptr epochs' links')
      hk_lt_cap hcap_lt hpcm hrunm hsp_align_m hx19_m hx20_m hx22_m hx27_m (hx28_m.trans hx28) hx29_m htr_m hv_m
    refine SepWP.seq_entails_plain hchk ?_
    rintro sm2 hpcm2 hrunm2 ⟨hsp_m2, hsp_align_m2, hx8_m2, hx19_m2, hx20_m2, hx22_m2, hx28_m2, hx29_m2, htr_m2, hv_m2⟩
    have hsp_eq : s.sp = sm2.sp := (hsp_m2.trans hsp_m).symm; rw [hsp_eq]
    have hk' : k + 1 < links'.length := by simp only [List.length_cons] at hk; omega
    have hlen'_le : links'.length ≤ cap.toNat := by simp only [List.length_cons] at hlen_le; omega
    have hih := ih (BitVec.ofNat 64 (vecDequePhysIdx head.toNat cap.toNat 1)) gce.recv.prev.ptr
      epochs' links' hk' hlen'_le hlen_eq sm2 hpcm2 hrunm2 hsp_align_m2 hx8_m2 hx20_m2 hx22_m2 hx28_m2
    simp only [iterHead, iterL2, List.drop_succ_cons]
    refine SepWP.conseq hih ?_
    rintro sf P' ⟨⟨hsp_f, hsp_align_f, hx19_f, hx20_f, hx22_f, hx27_f, hx28_f, hx29_f, htr_f, hv_f⟩, hent_f⟩
    exact ⟨⟨hsp_f, hsp_align_f, hx19_f.trans hx19_m2, hx20_f, hx22_f, hx27_f, hx28_f,
      hx29_f.trans hx29_m2, htr_f.trans htr_m2, hv_f.trans hv_m2⟩, hent_f⟩

theorem sendKey_from_344_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (selfPtr cap ptr head1 : BitVec 64) (epochs1 : List ChainEpochGhost) (links1 : List ChainEpoch)
    (h0 : 0 < links1.length) (hlen_le : links1.length ≤ cap.toNat) (hlen_eq : epochs1.length = links1.length)
    (s : State) (hpc : s.pc = (blkPl_367).base + 344#64) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hx20 : s.readReg64 (.gpr 20#5) = selfPtr) :
    let links2 := links1.set 0 { links1[0] with send := links1[0].send.clearNext }
    SepWP ((blkPC_367).rebase (blkPl_367).base H) ((blkPl_367).base + 380#64) s
      (clearFrontPre A selfPtr cap ptr head1 epochs1 links1)
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.spAligned = true ∧
         sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sf.readReg64 (.gpr 20#5) = selfPtr ∧
         sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧ sf.readReg64 (.gpr 28#5) = 1#64 ∧
         sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧ sf.trace = s.trace ∧
         calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (P' ⊢ clearFrontPre A selfPtr cap ptr head1 epochs1 links2)) := by
  intro links2; dsimp only [links2] at *; unfold clearFrontPre
  have hzip_len : (epochs1.zip links1).length = links1.length := by simp [hlen_eq]
  have hzip_le : (epochs1.zip links1).length ≤ cap.toNat := by omega
  have hzip_0 : 0 < (epochs1.zip links1).length := by omega
  refine SepWP.fold (vecDequeRingBuf_get_physIdx A cap ptr head1 (epochs1.zip links1) hzip_le hzip_0) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hhead, hcap_lt, hptr⟩
  have hzip_get0 : (epochs1.zip links1)[0] = (epochs1[0]'(by omega), links1[0]'h0) := by simp [List.getElem_zip]
  rw [hzip_get0]
  refine SepWP.fold (chainEpochAt_unpack_send_next A (epochs1[0]'(by omega)) (links1[0]'h0)
    (ptr + BitVec.ofNat 64 (vecDequePhysIdx head1.toNat cap.toNat 0 * 112))) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hle0, hcap0, hptr0⟩
  have hmadd0 := physIdx_zero_madd_eq (ptr := ptr) hhead hcap_lt
  have hpack_ce := chainEpochAt_pack_clearNext A (epochs1[0]'(by omega)) (links1[0]'h0)
    (ptr + BitVec.ofNat 64 (vecDequePhysIdx head1.toNat cap.toNat 0 * 112)) hle0 hcap0 hptr0
  have hset := vecDequeRingBuf_set_physIdx A cap ptr head1 (epochs1.zip links1)
    (epochs1[0]'(by omega), { links1[0] with send := links1[0].send.clearNext })
    hhead hcap_lt hptr hzip_le hzip_0
  dsimp only at hset
  have hzip_set : (epochs1.zip links1).set 0
      (epochs1[0]'(by omega), { links1[0] with send := links1[0].send.clearNext }) =
      epochs1.zip (links1.set 0 { links1[0] with send := links1[0].send.clearNext }) :=
    zip_set_snd epochs1 links1 0 (epochs1[0]'(by omega)) _ (List.getElem?_eq_getElem (by omega))
  rw [hzip_set] at hset
  wp_norm_hyp hx20; wp_norm_hyp hmadd0; wp_steps
  refine SepWP.fold hpack_ce (by sep_focus) ?_
  refine SepWP.fold hset (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨⟨by wp_norm_goal, hsp_align, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩, ?_⟩; sep_frame

namespace SendKeyTailHelpers
open ChainSendKeyFacts

theorem nextKeyOutAt_dup_len (out : BitVec 64) (ctr : BitVec 32) (key : List (BitVec 8)) :
    nextKeyOutAt out ctr key ⊢ ⌜key.length = 32⌝ ∗ nextKeyOutAt out ctr key := by
  unfold nextKeyOutAt
  refine Entails.pure_left fun hlen => Entails.pure_right hlen (Entails.pure_right hlen (Entails.refl _))

theorem nextKeyNext_length_of_nextKeyOut_length {hkdf : HkdfFn} {next : Bytes} {ctr : BitVec 32}
    (h : (nextKeyOut hkdf next ctr).length = 32) :
    (nextKeyNext hkdf next ctr).length = 32 := by
  unfold nextKeyOut at h; unfold nextKeyNext
  rw [List.length_take, List.length_drop] at h; rw [List.length_take]; omega

theorem ofNat_lt_props {i len : Nat} (hi : i < len) (hlen : len < 2 ^ 63) :
    BitVec.ule (BitVec.ofNat 64 len) (BitVec.ofNat 64 i) = false ∧
    BitVec.ult (BitVec.ofNat 64 i) (BitVec.ofNat 64 len) = true := by
  have hi64 : i < 18446744073709551616 := by omega
  have hlen64 : len < 18446744073709551616 := by omega
  refine ⟨?_, ?_⟩ <;>
    simp [BitVec.ule, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hlen64] <;> omega

def calleeSavedSendKeyAt (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

theorem calleeSavedSendKeyAt_def (s0 : State) :
    calleeSavedSendKeyAt s0 =
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) := rfl

def sendKeyScratchAt (sp0 l0 l1 l2 : BitVec 64) : SepProp :=
  memRegion (sp0 - 208#64) 8 ∗ ((sp0 - 200#64) ↦₆₄ l0) ∗
  ((sp0 - 192#64) ↦₆₄ l1) ∗ ((sp0 - 184#64) ↦₆₄ l2) ∗ memRegion (sp0 - 144#64) 12

theorem sendKeyScratchAt_def (sp0 l0 l1 l2 : BitVec 64) :
    sendKeyScratchAt sp0 l0 l1 l2 =
      memRegion (sp0 - 208#64) 8 ∗ ((sp0 - 200#64) ↦₆₄ l0) ∗
      ((sp0 - 192#64) ↦₆₄ l1) ∗ ((sp0 - 184#64) ↦₆₄ l2) ∗ memRegion (sp0 - 144#64) 12 := rfl

theorem sp_sub_208_aligned {s s0 : State} (h0 : s0.spAligned = true) (h : s.sp = s0.sp - 208#64) :
    s.spAligned = true := by
  simp only [State.spAligned, h] at h0 ⊢; revert h0; bv_kernel

theorem stackAt_nextKeyInternalX_to_extHook {sp sp0 : BitVec 64} (hsp : sp = sp0 - 208#64) :
    stackAt (sp0 - 208#64) nextKeyInternalStackX =
      memRegion (sp0 - 208#64 - BitVec.ofNat 64 nextKeyInternalStackX) 176 ∗
      stackAt sp extHookStack := by
  subst hsp; exact stackAt_nextKeyInternalX_top_split (sp0 - 208#64)

theorem from436_q_reframe {sp sp0 : BitVec 64} (hsp : sp = sp0 - 208#64) (q0 q1 q2 q3 : BitVec 64) :
    ((sp0 - 176#64) ↦₆₄ q0) ∗ ((sp0 - 168#64) ↦₆₄ q1) ∗
    ((sp0 - 160#64) ↦₆₄ q2) ∗ ((sp0 - 152#64) ↦₆₄ q3) =
    ((sp + 32#64) ↦₆₄ q0) ∗ ((sp + 40#64) ↦₆₄ q1) ∗
    ((sp + 48#64) ↦₆₄ q2) ∗ ((sp + 56#64) ↦₆₄ q3) := by
  subst hsp; simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]

theorem from436_sp_unframe {sp sp0 : BitVec 64} (hsp : sp = sp0 - 208#64) (k0 k1 k2 k3 : BitVec 64) :
    ((sp + 32#64) ↦₆₄ k0) ∗ ((sp + 40#64) ↦₆₄ k1) ∗
    ((sp + 48#64) ↦₆₄ k2) ∗ ((sp + 56#64) ↦₆₄ k3) =
    ((sp0 - 176#64) ↦₆₄ k0) ∗ ((sp0 - 168#64) ↦₆₄ k1) ∗
    ((sp0 - 160#64) ↦₆₄ k2) ∗ ((sp0 - 152#64) ↦₆₄ k3) := by
  subst hsp; simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]

theorem allowPanic_sendKey_oom {s0 sf : State} {P_pan : Prop} {P R : SepProp}
    (hoom : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ ⌜(P_pan ∧ sf.trace = s0.trace) ∨ (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)⌝ ∗ anyHeap ∗ R := by
  rw [satisfies_pure_sepConj]
  exact ⟨Or.inr hoom, Satisfies.mono (sepConj_mono_left (entails_anyHeap P)) hm⟩

theorem SepWPp.post_of_entails {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp} {R : SepProp} {Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P' ⊢ Q sf)) Qp) :
    SepWPp prog ret s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) Qp := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R' hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hret, hrun, P', hm', hsp, hcs, hent⟩ | hpan
  · exact Or.inl ⟨hret, hrun, P', hm', ⟨fun hmR => Satisfies.mono (sepConj_mono_left hent) hmR, hsp, hcs⟩⟩
  · exact Or.inr hpan

theorem SepWP.conseq_entails {prog : Program} {mid : BitVec 64} {s : State}
    {P P0 F P_mid P_mid' : SepProp} {φ : State → Prop}
    (h1 : SepWP prog mid s P0 (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid)))
    (hpre : P ⊢ P0 ∗ F) (hpost : P_mid ∗ F ⊢ P_mid') :
    SepWP prog mid s P (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid')) := by
  unfold SepWP; intro R hm hL
  have hm0 : s.mem ⊨ P0 ∗ (F ∗ R) := by
    rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hpre) hm
  rcases h1.elim hm0 hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hφ, hent⟩ | ⟨_, hfalse⟩⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inl ⟨hpcm, hrunm, Pm ∗ F, hmm, hφ, Entails.trans (sepConj_mono_left hent) hpost⟩⟩
  · rw [satisfies_pure_sepConj] at hfalse; exact False.elim hfalse.1

theorem SepWPp.seq_entails_inImage {prog : Program} {img : Obj.Image}
    {mid target : BitVec 64} {s : State} {P P_mid : SepProp}
    {φ : State → Prop} {post panic_post : State → SepProp → Prop}
    (hF : ImgCallInv img s)
    (h1 : SepWP prog mid s P (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → ImgCallInv img sm → φ sm →
      SepWPp prog target sm P_mid post panic_post) :
    SepWPp prog target s P post panic_post := by
  intro R hm hL
  rcases h1.elim hm hL with ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hφ, hent⟩ | ⟨_, hfalse⟩⟩
  · have hmm' : sm.mem ⊨ P_mid ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps2, hout⟩ :=
      h2 sm hpcm hrunm (hF.of_steps hsteps1) hφ R hmm' (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · rw [satisfies_pure_sepConj] at hfalse; exact False.elim hfalse.1

theorem lt_props {a b : BitVec 64} (h : a < b) :
    BitVec.ult a b = true ∧ BitVec.ule b a = false := by
  have hlt : a.toNat < b.toNat := BitVec.lt_def.mp h
  refine ⟨?_, ?_⟩ <;> simp [BitVec.ult, BitVec.ule] <;> omega

theorem ge_props {a b : BitVec 64} (h : ¬ a < b) :
    BitVec.ult a b = false ∧ BitVec.ule b a = true := by
  have hge : b.toNat ≤ a.toNat := by by_contra hlt; exact h (BitVec.lt_def.mpr (by omega))
  refine ⟨?_, ?_⟩ <;> simp [BitVec.ult, BitVec.ule] <;> omega

theorem back_ge_props {d : BitVec 64} {len : Nat}
    (hge : d.toNat ≥ len) (hlen : len < 2 ^ 63) :
    BitVec.ult d (BitVec.ofNat 64 len) = false ∧ BitVec.ule (BitVec.ofNat 64 len) d = true := by
  have hlen64 : len < 18446744073709551616 := by omega
  refine ⟨?_, ?_⟩ <;> simp [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64] <;> omega

theorem back_lt_props {d : BitVec 64} {len : Nat}
    (hlt : d.toNat < len) (hlen : len < 2 ^ 63) :
    BitVec.ult d (BitVec.ofNat 64 len) = true ∧ BitVec.ule (BitVec.ofNat 64 len) d = false := by
  have hlen64 : len < 18446744073709551616 := by omega
  refine ⟨?_, ?_⟩ <;> simp [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64] <;> omega

theorem ne_branch_props {a b : BitVec 64} (hne : a ≠ b) :
    (a == b) = false ∧ (a - b == 0#64) = false ∧ (a + (~~~b + 1#64) == 0#64) = false := by
  refine ⟨beq_false_of_ne hne, ?_, ?_⟩ <;>
    (rw [beq_eq_false_iff_ne]; intro heq; apply hne; revert heq; bv_kernel)

theorem k_plus_2_ge_2_props (k : Nat) (hk : k + 2 < 2 ^ 63) :
    BitVec.ult (BitVec.ofNat 64 (k + 2)) 2#64 = false ∧
    BitVec.ule 2#64 (BitVec.ofNat 64 (k + 2)) = true := by
  have hk64 : k + 2 < 18446744073709551616 := by omega
  refine ⟨?_, ?_⟩ <;> simp [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]

end SendKeyTailHelpers

theorem SepWP.conseq_entails {prog : Program} {mid : BitVec 64} {s : State}
    {P P0 F P_mid P_mid' : SepProp} {φ : State → Prop}
    (h1 : SepWP prog mid s P0 (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid)))
    (hpre : P ⊢ P0 ∗ F) (hpost : P_mid ∗ F ⊢ P_mid') :
    SepWP prog mid s P (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid')) := by
  unfold SepWP; intro R hm hL
  have hm0 : s.mem ⊨ P0 ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hpre) hm
  rcases h1.elim hm0 hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hφ, hent⟩ | ⟨_, hfalse⟩⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inl ⟨hpcm, hrunm, Pm ∗ F, hmm, hφ, Entails.trans (sepConj_mono_left hent) hpost⟩⟩
  · rw [satisfies_pure_sepConj] at hfalse; exact False.elim hfalse.1

end CryptoVerification.SpqrV1.ChainProofs
