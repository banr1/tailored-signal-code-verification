/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEpilogue
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `message_keys` vector clone loop for `<Chain as Clone>::clone` (`0x24848`)
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainCloneStateSimp.sp_setPC_pre ChainCloneStateSimp.sp_setMem_setPC_pre
  ChainCloneStateSimp.readReg64_setPC_pre ChainCloneStateSimp.readReg64_setMem_setPC_pre
  ChainCloneStateSimp.readReg32_setPC_pre ChainCloneStateSimp.readReg32_setMem_setPC_pre
  ChainCloneStateSimp.readReg_setPC_pre ChainCloneStateSimp.readReg_setMem_setPC_pre
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## Per-element `MessageKey` clone loop -/

theorem mul104_ne_of_lt {doneLen total : Nat}
    (hlt : doneLen < total) (htot : total ≤ maxMessageKeys) :
    BitVec.ofNat 64 (104 * total) ≠ BitVec.ofNat 64 (104 * doneLen) := by
  intro heq
  have h1 : 104 * total < 2 ^ 64 := by unfold maxMessageKeys at htot; omega
  have h2 : 104 * doneLen < 2 ^ 64 := by unfold maxMessageKeys at htot; omega
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at ht
  omega

theorem mul104_beq_eq_false {doneLen total : Nat}
    (hlt : doneLen < total) (htot : total ≤ maxMessageKeys) :
    (BitVec.ofNat 64 (104 * total) == BitVec.ofNat 64 (104 * doneLen)) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul104_ne_of_lt hlt htot

theorem off_add_104 (doneLen : Nat) :
    BitVec.ofNat 64 (104 * doneLen) + 104#64 = BitVec.ofNat 64 (104 * (doneLen + 1)) := by
  simp [Nat.mul_add, BitVec.ofNat_add]

theorem ptr_off_add_104 (mkPtr' : BitVec 64) (doneLen : Nat) :
    mkPtr' + BitVec.ofNat 64 (104 * doneLen) + 104#64 =
      mkPtr' + BitVec.ofNat 64 (104 * (doneLen + 1)) := by
  rw [BitVec.add_assoc, off_add_104]

theorem memRegion_mk_cons (mkPtr' : BitVec 64) (doneLen n : Nat)
    (hn : n + 1 ≤ maxMessageKeys) :
    memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * (n + 1)) =
      memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) 104 ∗
      memRegion (mkPtr' + BitVec.ofNat 64 (104 * (doneLen + 1))) (104 * n) := by
  have hmul : 104 * (n + 1) = 104 + 104 * n := by omega
  have hle : 104 + 104 * n ≤ 2 ^ 64 := by unfold maxMessageKeys at hn; omega
  rw [hmul,
      ProofLib.memRegion_split (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) 104 (104 * n) hle,
      ptr_off_add_104]

theorem ofNat_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add]
  bv_omega

theorem fold_iter_messageKeys (A : RustAlloc)
    (gk : MessageKeyGhost) (mkg : MessageKeyGenerator)
    (srcCur dstCur seedPtr' : BitVec 64)
    (R0 R0b R1 R2 : SepProp)
    (hpos : 0 < mkg.seed.length)
    (hle : mkg.seed.length ≤ gk.seed.cap.toNat)
    (hlt : gk.seed.cap.toNat < 2 ^ 63)
    (hptr : gk.seed.ptr ≠ 0)
    (hptr' : seedPtr' ≠ 0#64) :
    ((seedPtr' ↦ₛ mkg.seed) ∗
      (gk.seed.ptr ↦ₛ mkg.seed) ∗
      R0 ∗
      R0b ∗
      A.live seedPtr' mkg.seed.length 1 ∗
      ((srcCur + 16#64) ↦₆₄ 0#64) ∗
      ((srcCur + 40#64) ↦₆₄ 0#64) ∗
      ((srcCur + 64#64) ↦₆₄ 0#64) ∗
      ((srcCur + 80#64) ↦₆₄ gk.seed.ptr) ∗
      ((srcCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((srcCur + 96#64) ↦₃₂ mkg.counter) ∗
      messageKeySourceFrame A gk mkg srcCur ∗
      R1 ∗
      (dstCur ↦₆₄ 0#64) ∗
      ((dstCur + 8#64) ↦₆₄ 1#64) ∗
      ((dstCur + 16#64) ↦₆₄ 0#64) ∗
      ((dstCur + 24#64) ↦₆₄ 0#64) ∗
      ((dstCur + 32#64) ↦₆₄ 1#64) ∗
      ((dstCur + 40#64) ↦₆₄ 0#64) ∗
      ((dstCur + 48#64) ↦₆₄ 0#64) ∗
      ((dstCur + 56#64) ↦₆₄ 1#64) ∗
      ((dstCur + 64#64) ↦₆₄ 0#64) ∗
      ((dstCur + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dstCur + 80#64) ↦₆₄ seedPtr') ∗
      ((dstCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dstCur + 96#64) ↦₃₂ mkg.counter) ∗
      memRegion (dstCur + 100#64) 4 ∗
      R2) ⊢
    (messageKeyAt A (gk, mkg) srcCur ∗
      messageKeyAt A (clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length) seedPtr', mkg) dstCur ∗
      R1 ∗ R0 ∗ R0b ∗ R2) := by
  have hlt_seed : mkg.seed.length < 2 ^ 63 := by omega
  rw [← fold_cloned_messageKeyAt A mkg seedPtr' dstCur hpos hlt_seed hptr',
      messageKeyAt_eq_source A gk mkg srcCur]
  have hgroup :
      ((seedPtr' ↦ₛ mkg.seed) ∗
        (gk.seed.ptr ↦ₛ mkg.seed) ∗
        R0 ∗
        R0b ∗
        A.live seedPtr' mkg.seed.length 1 ∗
        ((srcCur + 16#64) ↦₆₄ 0#64) ∗
        ((srcCur + 40#64) ↦₆₄ 0#64) ∗
        ((srcCur + 64#64) ↦₆₄ 0#64) ∗
        ((srcCur + 80#64) ↦₆₄ gk.seed.ptr) ∗
        ((srcCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((srcCur + 96#64) ↦₃₂ mkg.counter) ∗
        messageKeySourceFrame A gk mkg srcCur ∗
        R1 ∗
        (dstCur ↦₆₄ 0#64) ∗
        ((dstCur + 8#64) ↦₆₄ 1#64) ∗
        ((dstCur + 16#64) ↦₆₄ 0#64) ∗
        ((dstCur + 24#64) ↦₆₄ 0#64) ∗
        ((dstCur + 32#64) ↦₆₄ 1#64) ∗
        ((dstCur + 40#64) ↦₆₄ 0#64) ∗
        ((dstCur + 48#64) ↦₆₄ 0#64) ∗
        ((dstCur + 56#64) ↦₆₄ 1#64) ∗
        ((dstCur + 64#64) ↦₆₄ 0#64) ∗
        ((dstCur + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((dstCur + 80#64) ↦₆₄ seedPtr') ∗
        ((dstCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((dstCur + 96#64) ↦₃₂ mkg.counter) ∗
        memRegion (dstCur + 100#64) 4 ∗
        R2) =
      ((((srcCur + 16#64) ↦₆₄ 0#64) ∗
          ((srcCur + 40#64) ↦₆₄ 0#64) ∗
          ((srcCur + 64#64) ↦₆₄ 0#64) ∗
          ((srcCur + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((srcCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗
          ((srcCur + 96#64) ↦₃₂ mkg.counter) ∗
          messageKeySourceFrame A gk mkg srcCur) ∗
        ((dstCur ↦₆₄ 0#64) ∗
          ((dstCur + 8#64) ↦₆₄ 1#64) ∗
          ((dstCur + 16#64) ↦₆₄ 0#64) ∗
          ((dstCur + 24#64) ↦₆₄ 0#64) ∗
          ((dstCur + 32#64) ↦₆₄ 1#64) ∗
          ((dstCur + 40#64) ↦₆₄ 0#64) ∗
          ((dstCur + 48#64) ↦₆₄ 0#64) ∗
          ((dstCur + 56#64) ↦₆₄ 1#64) ∗
          ((dstCur + 64#64) ↦₆₄ 0#64) ∗
          ((dstCur + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dstCur + 80#64) ↦₆₄ seedPtr') ∗
          ((dstCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dstCur + 96#64) ↦₃₂ mkg.counter) ∗
          memRegion (dstCur + 100#64) 4 ∗
          A.live seedPtr' mkg.seed.length 1 ∗
          (seedPtr' ↦ₛ mkg.seed)) ∗
        R1 ∗ R0 ∗ R0b ∗ R2) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono_left (Entails.pure_right ⟨hpos, hle, hlt, hptr⟩ (Entails.refl _))

set_option maxHeartbeats 1200000 in
private theorem chain_clone_mk_loop_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hshim : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr chainCloneLocal1Name +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
      sessionShimSpec)
    (halloc : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr chainCloneLocal1Name +
        bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
      (rustAllocSpec A))
    (hmemcpy : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr chainCloneLocal1Name +
        bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
      sessionMemcpySpec)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true)
    (total : Nat) (hmax : total ≤ maxMessageKeys)
    (rem : List (MessageKeyGhost × MessageKeyGenerator))
    (hne : rem ≠ [])
    (doneLen : Nat) (htot : doneLen + rem.length = total)
    (s : State) (srcCur mkPtr' v11 v13 : BitVec 64) (w12b : BitVec 32) (F R : SepProp)
    (hpanic824 : ∀ (s : State) (P : SepProp),
      s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr chainCloneLocal1Name + 824#64 →
      s.status = .Running →
      s.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)))
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr chainCloneLocal1Name + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = mkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = srcCur)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = BitVec.ofNat 64 rem.length)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 (104 * doneLen))
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (keys' : List MessageKeyGhost) (v11' v13' : BitVec 64) (w12b' : BitVec 32),
      keys'.length = rem.length →
      sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr chainCloneLocal1Name + 688#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 208#64 →
      sf.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      sf.readReg64 (Reg.gpr 19#5) = mkPtr' →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sf
        (arrayAt (messageKeyAt A) 104 srcCur rem ∗
          arrayAt (messageKeyAt A) 104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (keys'.zip (rem.map Prod.snd)) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
          ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
          ((s0.sp - 120#64) ↦₆₄ v11') ∗
          ((s0.sp - 108#64) ↦₃₂ w12b') ∗
          ((s0.sp - 104#64) ↦₆₄ v13') ∗
          F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (arrayAt (messageKeyAt A) 104 srcCur rem ∗
        memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * rem.length) ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
        ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  code_fetches_range libsignalSessionCode chainCloneLocal1Bin b
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") 348 84
  code_fetches_range libsignalSessionCode chainCloneLocal1Bin b
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") 592 96
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic824 hcont ⊢
  examples_hide_fetches
  induction rem generalizing s doneLen srcCur v11 w12b v13 F with
  | nil => exact (hne rfl).elim
  | cons head rem' ih =>
    rcases head with ⟨gk, mkg⟩
    have hlt_done : doneLen < total := by simp at htot; omega
    have hrem_le : rem'.length + 1 ≤ maxMessageKeys := by simp at htot; omega
    have hcmp : (BitVec.ofNat 64 (104 * total) == BitVec.ofNat 64 (104 * doneLen)) = false :=
      mul104_beq_eq_false hlt_done hmax
    rw [arrayAt_cons, messageKeyAt_eq_source A gk mkg srcCur]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hseed_pos, hseed_le, hseed_cap_lt, hseed_ptr⟩ => ?_
    have hseed_lt63 : mkg.seed.length < 2 ^ 63 := by omega
    have hseed_toNat : (BitVec.ofNat 64 mkg.seed.length).toNat = mkg.seed.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hseed_beq0 : (BitVec.ofNat 64 mkg.seed.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hseed_pos (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hseed_lay : LayoutOk mkg.seed.length 1 := ⟨hseed_pos, hpow2, by omega⟩
    apply SepWPp.of_sepWP (mid := entry + bv% (660))
    wp_steps
    wp_apply
    have htr_sf : sf.trace = s0.trace := by rw [‹sf.trace = s.trace›, htrace]
    wp_compact
    wp_steps
    wp_apply
    rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
    wp_compact
    apply SepWP.done ‹_› ‹_›
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPp_pure_mid fun htrace_oom => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (824))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine hpanic824 _ _ ?_ ?_ ?_
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · exact htrace_oom
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod, htrace1⟩ => ?_
      rw [List.length_cons,
          memRegion_mk_cons mkPtr' doneLen rem'.length hrem_le,
          memRegion_104_eq_slots104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun d => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (404))
      wp_steps
      wp_apply
      have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
      wp_compact
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · let gk' := clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length)
          (sf_1.readReg64 (Reg.gpr 0#5))
        refine SepWPp.weaken_pre
          (fold_iter_messageKeys A gk mkg srcCur
            (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (sf_1.readReg64 (Reg.gpr 0#5)) _ _ _ _
            hseed_pos hseed_le hseed_cap_lt hseed_ptr hoom64) ?_
        rw [List.length_cons, ofNat_succ_sub_one, off_add_104]
        cases rem' with
        | nil =>
          simp only [List.length_nil, Nat.mul_zero, memRegion_zero, arrayAt_nil,
            sepConj_emp, emp_sepConj, sepConj_assoc]
          apply SepWPp.of_sepWP (mid := entry + bv% (688))
          wp_steps
          refine SepWP.done ?_ ?_ ?_
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · refine SepWPp.weaken_pre ?_
              (hcont _ [gk'] 0#64 1#64 mkg.counter rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_)
            · simp only [List.map, List.zip_cons_cons, List.zip_nil_right,
                arrayAt_cons, arrayAt_nil, sepConj_emp, sepConj_assoc]
              exact Entails.refl _
            · simp only [wp_norm]
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]
            · exact htr_sf2
            · simp only [wp_norm]; assumption
        | cons p2 rem'' =>
          have hrem'_pos : 0 < (p2 :: rem'').length := by simp
          have hrem'_beq0 : (BitVec.ofNat 64 (p2 :: rem'').length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrem'_pos
              (by unfold maxMessageKeys at hrem_le; simp at hrem_le ⊢; omega)
          apply SepWPp.of_sepWP (mid := entry + bv% (408))
          wp_steps
          refine SepWP.done ?_ ?_ ?_
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · have htot' : (doneLen + 1) + (p2 :: rem'').length = total := by
              simp at htot ⊢; omega
            refine SepWPp.weaken_pre ?_
              (ih (by simp) (doneLen + 1) htot' _ (srcCur + 104#64) 0#64 1#64 mkg.counter
                (messageKeyAt A (gk, mkg) srcCur ∗
                  messageKeyAt A (gk', mkg) (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) ∗ F)
                ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                fun sf_f keys'_tail v11' v13' w12b' hklen' hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f => ?_)
            · exact Entails.of_eq (by ac_rfl)
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]
            · simp only [wp_norm]
            · simp only [wp_norm]
            · simp only [wp_norm]
            · exact htr_sf2
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]
            · have hdone := hcont sf_f (gk' :: keys'_tail) v11' v13' w12b'
                (by simp [hklen']) hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f
              rw [List.map_cons, List.zip_cons_cons,
                arrayAt_cons (x := (gk, mkg)),
                arrayAt_cons (x := (gk', (gk, mkg).2)),
                ptr_off_add_104] at hdone
              dsimp only at hdone
              simp only [sepConj_assoc] at hdone
              refine SepWPp.weaken_pre ?_ hdone
              exact Entails.of_eq (by ac_rfl)

theorem chain_clone_mk_loop_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocHooks A abs)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true)
    (total : Nat) (hmax : total ≤ maxMessageKeys)
    (rem : List (MessageKeyGhost × MessageKeyGenerator))
    (hne : rem ≠ [])
    (doneLen : Nat) (htot : doneLen + rem.length = total)
    (s : State) (srcCur mkPtr' v11 v13 : BitVec 64) (w12b : BitVec 32) (F R : SepProp)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr chainCloneLocal1Name + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = mkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = srcCur)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = BitVec.ofNat 64 rem.length)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 (104 * doneLen))
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (keys' : List MessageKeyGhost) (v11' v13' : BitVec 64) (w12b' : BitVec 32),
      keys'.length = rem.length →
      sf.pc = (trTrapProgAt b C abs).fnAddr chainCloneLocal1Name + 688#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 208#64 →
      sf.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      sf.readReg64 (Reg.gpr 19#5) = mkPtr' →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPp (trTrapProgAt b C abs) (s0.readReg64 (Reg.gpr 30#5)) sf
        (arrayAt (messageKeyAt A) 104 srcCur rem ∗
          arrayAt (messageKeyAt A) 104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (keys'.zip (rem.map Prod.snd)) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
          ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
          ((s0.sp - 120#64) ↦₆₄ v11') ∗
          ((s0.sp - 108#64) ↦₃₂ w12b') ∗
          ((s0.sp - 104#64) ↦₆₄ v13') ∗
          F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 (Reg.gpr 30#5)) s
      (arrayAt (messageKeyAt A) 104 srcCur rem ∗
        memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * rem.length) ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
        ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) :=
  chain_clone_mk_loop_ext_trap
    (shim_ok_at_trap (b := b) (C := C) (abs := abs))
    (alloc_ok_at_trap (b := b) (C := C) (abs := abs) hA)
    (memcpy_ok_at_trap (b := b) (C := C) (abs := abs))
    x s0 hs0_align total hmax rem hne doneLen htot s srcCur mkPtr' v11 v13 w12b F R
    (fun s P => chain_clone_panic_824_trap (b := b) (C := C) (A := A) (abs := abs) (Q := Q) x s0 s P R)
    hpc hrun hsp hx29 hx19 hx26 hx27 hx28 htrace hvregs hcont

set_option maxHeartbeats 1600000 in
theorem chain_clone_mk_loop {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocHooks A abs)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true)
    (total : Nat) (hmax : total ≤ maxMessageKeys)
    (rem : List (MessageKeyGhost × MessageKeyGenerator))
    (hne : rem ≠ [])
    (doneLen : Nat) (htot : doneLen + rem.length = total)
    (s : State) (srcCur mkPtr' v11 v13 : BitVec 64) (w12b : BitVec 32) (F R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr chainCloneLocal1Name + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = mkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = srcCur)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = BitVec.ofNat 64 rem.length)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 (104 * doneLen))
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (keys' : List MessageKeyGhost) (v11' v13' : BitVec 64) (w12b' : BitVec 32),
      keys'.length = rem.length →
      sf.pc = (tripleRatchetProgAt b C ctl abs).fnAddr chainCloneLocal1Name + 688#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 208#64 →
      sf.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      sf.readReg64 (Reg.gpr 19#5) = mkPtr' →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 (Reg.gpr 30#5)) sf
        (arrayAt (messageKeyAt A) 104 srcCur rem ∗
          arrayAt (messageKeyAt A) 104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (keys'.zip (rem.map Prod.snd)) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
          ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
          ((s0.sp - 120#64) ↦₆₄ v11') ∗
          ((s0.sp - 108#64) ↦₃₂ w12b') ∗
          ((s0.sp - 104#64) ↦₆₄ v13') ∗
          F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 (Reg.gpr 30#5)) s
      (arrayAt (messageKeyAt A) 104 srcCur rem ∗
        memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * rem.length) ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
        ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) :=
  chain_clone_mk_loop_ext_trap
    (shim_ok_at (b := b) (C := C) (ctl := ctl) (abs := abs))
    (alloc_ok_at (b := b) (C := C) (ctl := ctl) (abs := abs) hA)
    (memcpy_ok_at (b := b) (C := C) (ctl := ctl) (abs := abs))
    x s0 hs0_align total hmax rem hne doneLen htot s srcCur mkPtr' v11 v13 w12b F R
    (fun s P => chain_clone_panic_824 (b := b) (C := C) (A := A) (ctl := ctl) (abs := abs) (Q := Q) x s0 s P R)
    hpc hrun hsp hx29 hx19 hx26 hx27 hx28 htrace hvregs hcont

/-! ## `message_keys` allocation and empty fast path -/

theorem vecBuf_mk_nil_eq (A : RustAlloc) :
    vecBuf A 104 8 (messageKeyAt A) 0#64 8#64 [] = emp := by
  unfold vecBuf
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by decide, by decide, by decide⟩
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _

theorem vecBuf_mk_pos_eq (A : RustAlloc) (mkPtr' : BitVec 64)
    (xs : List (MessageKeyGhost × MessageKeyGenerator))
    (hpos : 0 < xs.length) (hmax : xs.length ≤ maxMessageKeys) (hptr' : mkPtr' ≠ 0#64) :
    vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 xs.length) mkPtr' xs =
      A.live mkPtr' (104 * xs.length) 8 ∗
      arrayAt (messageKeyAt A) 104 mkPtr' xs := by
  unfold vecBuf
  have hlt64 : xs.length < 2 ^ 64 := by unfold maxMessageKeys at hmax; omega
  have htoNat : (BitVec.ofNat 64 xs.length).toNat = xs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hne0 : BitVec.ofNat 64 xs.length ≠ 0 := ofNat_ne_zero_of_pos hpos hlt64
  have hptr_ne : mkPtr' ≠ 0 := hptr'
  have hcap_lt : xs.length * 104 < 2 ^ 63 := by unfold maxMessageKeys at hmax; omega
  have hmul_comm : xs.length * 104 = 104 * xs.length := Nat.mul_comm _ _
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, Nat.zero_mul,
      ProofLib.memRegion_zero, sepConj_emp, hmul_comm]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by rw [htoNat], by rw [htoNat]; exact hcap_lt, hptr_ne⟩
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, Nat.zero_mul,
      ProofLib.memRegion_zero, sepConj_emp, hmul_comm]
    exact Entails.refl _

def chainMkSourceFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
  A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
  memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
    ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_mk_source (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hpos : 0 < gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
        gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
      ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
      arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
      chainMkSourceFrame A gc a := by
  unfold protoChainAt chainMkSourceFrame vecAt vecHeader vecBuf
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  rw [hzip_len, ha56, ha64]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          (if gc.1.mkCap = 0 then emp
           else A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
             arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
             memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
               ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104)) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          (if gc.1.mkCap = 0 then emp
           else A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
             arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
             memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
               ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104)) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    have hne : gc.1.mkCap ≠ 0 := by
      intro h0; rw [h0] at hle; change gc.2.messageKeys.length ≤ 0 at hle; omega
    simp only [hne, ↓reduceIte]
    apply Entails.pure_right ⟨hle, hlt, hptr⟩
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    have hne : gc.1.mkCap ≠ 0 := by
      intro h0; rw [h0] at hle; change gc.2.messageKeys.length ≤ 0 at hle; omega
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [hne, ↓reduceIte, sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
          arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
            ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
          memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
            ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

structure SpillSlots where
  v0 : BitVec 64
  w1a : BitVec 32
  w1b : BitVec 32
  v2 : BitVec 64
  v3 : BitVec 64
  v4 : BitVec 64
  v5 : BitVec 64
  v6 : BitVec 64
  v7 : BitVec 64

theorem spillSlotsExist_eq_struct (sp : BitVec 64) :
    spillSlotsExist sp =
      ∃∗ s : SpillSlots,
        ((sp - 208#64) ↦₆₄ s.v0) ∗
        ((sp - 200#64) ↦₃₂ s.w1a) ∗
        ((sp - 196#64) ↦₃₂ s.w1b) ∗
        ((sp - 192#64) ↦₆₄ s.v2) ∗
        ((sp - 184#64) ↦₆₄ s.v3) ∗
        ((sp - 176#64) ↦₆₄ s.v4) ∗
        ((sp - 168#64) ↦₆₄ s.v5) ∗
        ((sp - 160#64) ↦₆₄ s.v6) ∗
        ((sp - 152#64) ↦₆₄ s.v7) := by
  unfold spillSlotsExist
  apply sepProp_eq_of_entails
  · refine entails_sepExists_sepConj_left fun v0 => ?_
    refine entails_pull_exists fun w1a => ?_
    refine entails_pull_exists fun w1b => ?_
    refine entails_pull_exists fun v2 => ?_
    refine entails_pull_exists fun v3 => ?_
    refine entails_pull_exists fun v4 => ?_
    refine entails_pull_exists fun v5 => ?_
    refine entails_pull_exists fun v6 => ?_
    rw [sepExists_sepConj_right]
    refine entails_sepExists_left fun v7 => ?_
    apply Entails.sepExists_right ⟨v0, w1a, w1b, v2, v3, v4, v5, v6, v7⟩
    dsimp only
    simp only [sepConj_assoc]
    exact Entails.refl _
  · refine entails_sepExists_left fun s => ?_
    exact sepConj_mono (Entails.sepExists_right s.v0 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.w1a (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.w1b (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v2 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v3 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v4 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v5 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v6 (Entails.refl _))
      (Entails.sepExists_right s.v7 (Entails.refl _)))))))))

def savedRegsCore (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
  (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a)

theorem savedRegsOnStack_eq_core (s0 : State) :
    savedRegsOnStack s0 =
      ∃∗ p : BitVec 64 × BitVec 32,
        ((s0.sp - 120#64) ↦₆₄ p.1) ∗
        ((s0.sp - 108#64) ↦₃₂ p.2) ∗
        savedRegsCore s0 := by
  unfold savedRegsOnStack savedRegsCore
  rw [show (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
        (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
        (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)) =
      ((∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
        (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
          (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a))) by ac_rfl]
  apply sepProp_eq_of_entails
  · refine entails_sepExists_sepConj_left fun v11 => ?_
    refine entails_pull_exists fun w12b => ?_
    apply Entails.sepExists_right (v11, w12b)
    rw [sepConj_assoc]
    exact Entails.refl _
  · refine entails_sepExists_left fun p => ?_
    exact sepConj_mono (Entails.sepExists_right p.1 (Entails.refl _))
      (sepConj_mono_left (Entails.sepExists_right p.2 (Entails.refl _)))

theorem map_snd_zip_of_length_eq {α β : Type} (xs : List α) (ys : List β)
    (hlen : xs.length = ys.length) :
    (xs.zip ys).map Prod.snd = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs' ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys' =>
      simp only [List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih ys' (Nat.succ.inj hlen)

theorem mul_104_eq (n : Nat) :
    BitVec.ofNat 64 n * 104#64 = BitVec.ofNat 64 (104 * n) := by
  rw [Nat.mul_comm, BitVec.ofNat_mul]

theorem toNat_mul_104 {n : Nat} (hmax : n ≤ maxMessageKeys) :
    (BitVec.ofNat 64 (104 * n)).toNat = 104 * n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold maxMessageKeys at hmax; omega)]

set_option maxHeartbeats 1200000 in
theorem chain_clone_mks_nil_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hnil : x.gc.2.messageKeys = [])
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr chainCloneLocal1Name + 732#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      Qp := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  code_fetches_range libsignalSessionCode chainCloneLocal1Bin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") 732 4
  clear hfn
  have hep := fun s' => chain_clone_epilogue_trap (b := b) (C := C) (A := A)
    (abs := abs) (Qp := Qp)
    x s0 s' srkPtr' privPtr' 8#64 x25 x28 v9 v10 v13 w27 [] ckPin'
    hsrk hmax (by simp [hnil]) hsrc_klen
  unfold trTrapProgAt at hpc hep ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (736))
  wp_steps
  refine SepWP.done ?_ ?_ ?_
  · simp only [wp_norm]
  · simp only [wp_norm]; assumption
  · refine SepWPp.weaken_pre ?_
      (hep _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · have hbuf_nil :
          vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) 8#64
            ([].zip x.gc.2.messageKeys) = emp := by
        simpa [hnil] using vecBuf_mk_nil_eq A
      rw [hbuf_nil, emp_sepConj]
      exact Entails.refl _
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · unfold State.readReg32 at hw27 ⊢; simp only [wp_norm]; exact hw27
    · exact htrace
    · simp only [wp_norm]; assumption

set_option maxHeartbeats 1600000 in
theorem chain_clone_mks_nil {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hnil : x.gc.2.messageKeys = [])
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr chainCloneLocal1Name + 732#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      Qp :=
  SepWPp_kit_of_trTrap (chain_clone_mks_nil_trap x s0 s srkPtr' privPtr' x25 x28 v9 v10 v13
    w27 ckPin' hsrk hmax hsrc_klen hnil hpc hrun hsp hsp_align hx29 hx19 hx21 hx22 hx23 hx24
    hx25 hx28 hw27 htrace hvregs)

theorem chain_clone_mks_nonempty_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpos : 0 < x.gc.2.messageKeys.length)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr chainCloneLocal1Name + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 x.gc.2.messageKeys.length)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hshim := shim_ok_at_trap (b := b) (C := C) (abs := abs)
  have halloc := alloc_ok_at_trap (b := b) (C := C) (abs := abs) hA
  have hpanic860 := fun s P => chain_clone_panic_860_trap (b := b) (C := C) (A := A)
    (abs := abs)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    x s0 s P R
  have hzip_len : (x.gc.1.keys.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
    simp [hsrc_klen]
  have hzip_ne : x.gc.1.keys.zip x.gc.2.messageKeys ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hzip_len]; exact hpos)
  have hloop := fun s' srcCur mkPtr' v11 v13 w12b F =>
    chain_clone_mk_loop_trap (b := b) (C := C) (A := A)
      (abs := abs)
      (Q := fun sf P_f =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      hA x s0 hs0_align
      x.gc.2.messageKeys.length hmax
      (x.gc.1.keys.zip x.gc.2.messageKeys) hzip_ne
      0 (by simp [hzip_len])
      s' srcCur mkPtr' v11 v13 w12b F R
  have hep := fun s' mkPtr' v10' v13' keys' (hklen : keys'.length = x.gc.2.messageKeys.length) =>
    chain_clone_epilogue_trap (b := b) (C := C) (A := A)
      (abs := abs)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' mkPtr' x25 x28 mkPtr' v10' v13' w27 keys' ckPin'
      hsrk hmax hklen hsrc_klen
  dsimp only [sessionShimSpec] at hshim
  code_fetches_range libsignalSessionCode chainCloneLocal1Bin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") 260 88
  code_fetches_range libsignalSessionCode chainCloneLocal1Bin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") 688 28
  clear hfn
  unfold trTrapProgAt at hpc hshim halloc hpanic860 hloop hep ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic860 hloop hep ⊢
  examples_hide_fetches
  rw [chainAt_eq_mk_source A x.gc x.src hsrk hmax hsrc_klen hpos,
      spillSlotsExist_eq_struct s0.sp,
      savedRegsOnStack_eq_core s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ⟨v11, w12b⟩ => ?_
  refine SepWPp.exists_elim fun spSlots => ?_
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 208#64) ↦₆₄ spSlots.v0) ∗
        ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
        ((s0.sp - 196#64) ↦₃₂ spSlots.w1b) ∗
        ((s0.sp - 192#64) ↦₆₄ spSlots.v2) ∗
        ((s0.sp - 184#64) ↦₆₄ spSlots.v3) ∗
        ((s0.sp - 176#64) ↦₆₄ spSlots.v4) ∗
        ((s0.sp - 168#64) ↦₆₄ spSlots.v5) ∗
        ((s0.sp - 160#64) ↦₆₄ spSlots.v6) ∗
        ((s0.sp - 152#64) ↦₆₄ spSlots.v7) ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        savedRegsCore s0) =
      (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 208#64) ↦₆₄ spSlots.v0) ∗
        ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
        ((s0.sp - 196#64) ↦₃₂ spSlots.w1b) ∗
        ((s0.sp - 192#64) ↦₆₄ spSlots.v2) ∗
        ((s0.sp - 184#64) ↦₆₄ spSlots.v3) ∗
        ((s0.sp - 176#64) ↦₆₄ spSlots.v4) ∗
        ((s0.sp - 168#64) ↦₆₄ spSlots.v5) ∗
        ((s0.sp - 160#64) ↦₆₄ spSlots.v6) ∗
        ((s0.sp - 152#64) ↦₆₄ spSlots.v7) ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        savedRegsCore s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hmk_le, hmk_lt, hmk_ptr⟩ => ?_
  have hmul_eq : BitVec.ofNat 64 x.gc.2.messageKeys.length * 104#64 =
      BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length) :=
    mul_104_eq x.gc.2.messageKeys.length
  have hmul_toNat : (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)).toNat =
      104 * x.gc.2.messageKeys.length :=
    toNat_mul_104 hmax
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hmk_lay : LayoutOk (104 * x.gc.2.messageKeys.length) 8 :=
    ⟨by omega, hpow8, by unfold maxMessageKeys at hmax; omega⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (308))
  wp_steps
  wp_apply
  have htr_sf : sf.trace = s0.trace := by rw [‹sf.trace = s.trace›, htrace]
  rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
  wp_compact
  wp_steps
  wp_apply
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (860))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic860 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod8, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (408))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · let mkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
      refine SepWPp.weaken_pre ?_
        (hloop _ x.gc.1.mkPtr mkPtr' v11 v13 w12b
          (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
            ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
            chainMkSourceFrame A x.gc x.src ∗
            ((s0.sp - 208#64) ↦₆₄ x28) ∗
            ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
            ((s0.sp - 196#64) ↦₃₂ w27) ∗
            ((s0.sp - 192#64) ↦₆₄ x25) ∗
            ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
            ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
            ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            ((s0.sp - 152#64) ↦₆₄ x.dst) ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            savedRegsCore s0)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          fun sf_l keys' v11' v13' w12b' hklen_l hpc_l hrun_l hsp_l hx29_l hx19_l htr_l hvregs_l => ?_)
      · rw [hzip_len, BitVec.add_zero]
        exact Entails.of_eq (by dsimp only [mkPtr']; ac_rfl)
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]; assumption
      · simp only [wp_norm, hzip_len]
      · simp only [wp_norm, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      · exact htrace1
      · simp only [wp_norm]; assumption
      · have hklen : keys'.length = x.gc.2.messageKeys.length := hklen_l.trans hzip_len
        have hsp_l_align : sf_l.spAligned = true := by
          rw [State.spAligned, hsp_l]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        have htrunc32 : BitVec.truncate 32 (BitVec.zeroExtend 64 w27) = w27 :=
          (BitVec.setWidth_setWidth_of_le w27 (by decide)).trans (BitVec.setWidth_eq w27)
        simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
          map_snd_zip_of_length_eq x.gc.1.keys x.gc.2.messageKeys hsrc_klen,
          sepConj_assoc]
        apply SepWPp.of_sepWP (mid := entry + bv% (736))
        wp_steps
        refine SepWP.done ?_ ?_ ?_
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · refine SepWPp.weaken_pre ?_
            (hep _ mkPtr' (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) v13' keys' hklen
              ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          · have hzip'_len : (keys'.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
              simp [hklen]
            have hzip'_pos : 0 < (keys'.zip x.gc.2.messageKeys).length := by
              rw [hzip'_len]; exact hpos
            have hzip'_max : (keys'.zip x.gc.2.messageKeys).length ≤ maxMessageKeys := by
              rw [hzip'_len]; exact hmax
            have hbuf_eq := vecBuf_mk_pos_eq A mkPtr' (keys'.zip x.gc.2.messageKeys)
              hzip'_pos hzip'_max hoom64
            rw [hzip'_len] at hbuf_eq
            rw [hbuf_eq,
                chainAt_eq_mk_source A x.gc x.src hsrk hmax hsrc_klen hpos,
                spillSlotsExist_eq_struct s0.sp,
                savedRegsOnStack_eq_core s0]
            have hsp_fold :
                (((s0.sp - 208#64) ↦₆₄ x28) ∗
                  ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ w27) ∗
                  ((s0.sp - 192#64) ↦₆₄ x25) ∗
                  ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                  ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                  ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                  ((s0.sp - 152#64) ↦₆₄ x.dst)) ⊢
                (∃∗ s : SpillSlots,
                  ((s0.sp - 208#64) ↦₆₄ s.v0) ∗
                  ((s0.sp - 200#64) ↦₃₂ s.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ s.w1b) ∗
                  ((s0.sp - 192#64) ↦₆₄ s.v2) ∗
                  ((s0.sp - 184#64) ↦₆₄ s.v3) ∗
                  ((s0.sp - 176#64) ↦₆₄ s.v4) ∗
                  ((s0.sp - 168#64) ↦₆₄ s.v5) ∗
                  ((s0.sp - 160#64) ↦₆₄ s.v6) ∗
                  ((s0.sp - 152#64) ↦₆₄ s.v7)) := by
              apply Entails.sepExists_right
                ⟨x28, spSlots.w1a, w27, x25, privPtr',
                  BitVec.ofNat 64 x.gc.1.priv.bytes.length, srkPtr',
                  BitVec.ofNat 64 x.gc.1.srk.bytes.length, x.dst⟩
              dsimp only
              exact Entails.refl _
            have hsr_fold :
                (((s0.sp - 120#64) ↦₆₄ v11') ∗
                  ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                  savedRegsCore s0) ⊢
                (∃∗ p : BitVec 64 × BitVec 32,
                  ((s0.sp - 120#64) ↦₆₄ p.1) ∗
                  ((s0.sp - 108#64) ↦₃₂ p.2) ∗
                  savedRegsCore s0) := by
              apply Entails.sepExists_right (v11', w12b')
              dsimp only
              exact Entails.refl _
            have hsrc_fold :
                (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  chainMkSourceFrame A x.gc x.src) ⊢
                (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
                    x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
                  ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  chainMkSourceFrame A x.gc x.src) :=
              Entails.pure_right ⟨hmk_le, hmk_lt, hmk_ptr⟩ (Entails.refl _)
            have hgroup_pre :
                (arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  arrayAt (messageKeyAt A) 104 mkPtr' (keys'.zip x.gc.2.messageKeys) ∗
                  A.pool ∗
                  stackAt (s0.sp - 208#64) allocHookStack ∗
                  ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
                  ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
                  ((s0.sp - 120#64) ↦₆₄ v11') ∗
                  ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                  ((s0.sp - 104#64) ↦₆₄ v13') ∗
                  A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
                  memRegion x.dst 104 ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                  clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
                  ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  chainMkSourceFrame A x.gc x.src ∗
                  ((s0.sp - 208#64) ↦₆₄ x28) ∗
                  ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ w27) ∗
                  ((s0.sp - 192#64) ↦₆₄ x25) ∗
                  ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                  ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                  ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                  ((s0.sp - 152#64) ↦₆₄ x.dst) ∗
                  ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
                  savedRegsCore s0) =
                (memRegion x.dst 104 ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                  (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
                    arrayAt (messageKeyAt A) 104 mkPtr' (keys'.zip x.gc.2.messageKeys)) ∗
                  clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
                  (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                    arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                    chainMkSourceFrame A x.gc x.src) ∗
                  A.pool ∗
                  stackAt (s0.sp - 208#64) allocHookStack ∗
                  (((s0.sp - 208#64) ↦₆₄ x28) ∗
                    ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                    ((s0.sp - 196#64) ↦₃₂ w27) ∗
                    ((s0.sp - 192#64) ↦₆₄ x25) ∗
                    ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                    ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                    ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                    ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                    ((s0.sp - 152#64) ↦₆₄ x.dst)) ∗
                  ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
                  ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
                  ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
                  ((s0.sp - 104#64) ↦₆₄ v13') ∗
                  (((s0.sp - 120#64) ↦₆₄ v11') ∗
                    ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                    savedRegsCore s0)) := by
              ac_rfl
            rw [hgroup_pre]
            exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono hsrc_fold
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono hsp_fold
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right hsr_fold))))))))))))
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]; assumption
          · rw [State.spAligned] at hsp_l_align ⊢; simp only [wp_norm]; exact hsp_l_align
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · unfold State.readReg32; simp only [wp_norm, htrunc32]
          · exact htr_l
          · simp only [wp_norm]; exact hvregs_l

theorem chain_clone_mks_nonempty {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpos : 0 < x.gc.2.messageKeys.length)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr chainCloneLocal1Name + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 x.gc.2.messageKeys.length)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) :=
  SepWPp_kit_of_trTrap (chain_clone_mks_nonempty_trap hA x s0 s hs0_align srkPtr' privPtr'
    x25 x28 v9 v10 v13 w27 ckPin' R hsrk hmax hsrc_klen hpos hpc hrun hsp hsp_align hx29 hx19
    hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hw27 htrace hvregs)

/-! ## Relocatable `[LibsignalPlacement]` `MessageKey` clone loop (block `82`) -/

section Placed

open CryptoVerification CryptoVerification.E2E.Record.Placed

set_option maxHeartbeats 1200000 in
theorem chain_clone_local1_placed_mk_loop [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hshim : subroutine_ok (lsProg_82 H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok (lsProg_82 H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_82 H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true)
    (total : Nat) (hmax : total ≤ maxMessageKeys)
    (rem : List (MessageKeyGhost × MessageKeyGenerator))
    (hne : rem ≠ [])
    (doneLen : Nat) (htot : doneLen + rem.length = total)
    (s : State) (srcCur mkPtr' v11 v13 : BitVec 64) (w12b : BitVec 32) (F R : SepProp)
    (hpc : s.pc = (blkPl_82).base + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = mkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = srcCur)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = BitVec.ofNat 64 rem.length)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 (104 * doneLen))
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (keys' : List MessageKeyGhost) (v11' v13' : BitVec 64) (w12b' : BitVec 32),
      keys'.length = rem.length →
      sf.pc = (blkPl_82).base + 688#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 208#64 →
      sf.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      sf.readReg64 (Reg.gpr 19#5) = mkPtr' →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPp (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) sf
        (arrayAt (messageKeyAt A) 104 srcCur rem ∗
          arrayAt (messageKeyAt A) 104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (keys'.zip (rem.map Prod.snd)) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
          ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
          ((s0.sp - 120#64) ↦₆₄ v11') ∗
          ((s0.sp - 108#64) ↦₃₂ w12b') ∗
          ((s0.sp - 104#64) ↦₆₄ v13') ∗
          F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (arrayAt (messageKeyAt A) 104 srcCur rem ∗
        memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * rem.length) ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
        ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hpanic824 := fun s P => chain_clone_local1_placed_panic_824 (A := A)
    (H := H) (Q := Q) hpanic x s0 s P R
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic824 hcont ⊢
  induction rem generalizing s doneLen srcCur v11 w12b v13 F with
  | nil => exact (hne rfl).elim
  | cons head rem' ih =>
    rcases head with ⟨gk, mkg⟩
    have hlt_done : doneLen < total := by simp at htot; omega
    have hrem_le : rem'.length + 1 ≤ maxMessageKeys := by simp at htot; omega
    have hcmp : (BitVec.ofNat 64 (104 * total) == BitVec.ofNat 64 (104 * doneLen)) = false :=
      mul104_beq_eq_false hlt_done hmax
    rw [arrayAt_cons, messageKeyAt_eq_source A gk mkg srcCur]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hseed_pos, hseed_le, hseed_cap_lt, hseed_ptr⟩ => ?_
    have hseed_lt63 : mkg.seed.length < 2 ^ 63 := by omega
    have hseed_toNat : (BitVec.ofNat 64 mkg.seed.length).toNat = mkg.seed.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hseed_beq0 : (BitVec.ofNat 64 mkg.seed.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hseed_pos (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hseed_lay : LayoutOk mkg.seed.length 1 := ⟨hseed_pos, hpow2, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (660))
    wp_steps
    wp_call hshim ()
    have htr_sf : sf.trace = s0.trace := by rw [‹sf.trace = s.trace›, htrace]
    wp_compact
    wp_steps
    wp_call halloc (mkg.seed.length, 1)
    rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
    wp_compact
    apply SepWP.done ‹_› ‹_›
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPp_pure_mid fun htrace_oom => ?_
      apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (824))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine hpanic824 _ _ ?_ ?_ ?_
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · exact htrace_oom
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod, htrace1⟩ => ?_
      rw [List.length_cons,
          memRegion_mk_cons mkPtr' doneLen rem'.length hrem_le,
          memRegion_104_eq_slots104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun d => ?_
      apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (404))
      wp_steps
      wp_call hmemcpy (sf_1.readReg64 Reg.x0, gk.seed.ptr, mkg.seed)
      have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
      wp_compact
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · let gk' := clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length)
          (sf_1.readReg64 (Reg.gpr 0#5))
        refine SepWPp.weaken_pre
          (fold_iter_messageKeys A gk mkg srcCur
            (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (sf_1.readReg64 (Reg.gpr 0#5)) _ _ _ _
            hseed_pos hseed_le hseed_cap_lt hseed_ptr hoom64) ?_
        rw [List.length_cons, ofNat_succ_sub_one, off_add_104]
        cases rem' with
        | nil =>
          simp only [List.length_nil, Nat.mul_zero, memRegion_zero, arrayAt_nil,
            sepConj_emp, emp_sepConj, sepConj_assoc]
          apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (688))
          wp_steps
          refine SepWP.done ?_ ?_ ?_
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · refine SepWPp.weaken_pre ?_
              (hcont _ [gk'] 0#64 1#64 mkg.counter rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_)
            · simp only [List.map, List.zip_cons_cons, List.zip_nil_right,
                arrayAt_cons, arrayAt_nil, sepConj_emp, sepConj_assoc]
              exact Entails.refl _
            · simp only [wp_norm]
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]
            · exact htr_sf2
            · simp only [wp_norm]; assumption
        | cons p2 rem'' =>
          have hrem'_pos : 0 < (p2 :: rem'').length := by simp
          have hrem'_beq0 : (BitVec.ofNat 64 (p2 :: rem'').length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrem'_pos
              (by unfold maxMessageKeys at hrem_le; simp at hrem_le ⊢; omega)
          apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (408))
          wp_steps
          refine SepWP.done ?_ ?_ ?_
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · have htot' : (doneLen + 1) + (p2 :: rem'').length = total := by
              simp at htot ⊢; omega
            refine SepWPp.weaken_pre ?_
              (ih (by simp) (doneLen + 1) htot' _ (srcCur + 104#64) 0#64 1#64 mkg.counter
                (messageKeyAt A (gk, mkg) srcCur ∗
                  messageKeyAt A (gk', mkg) (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) ∗ F)
                ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                fun sf_f keys'_tail v11' v13' w12b' hklen' hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f => ?_)
            · exact Entails.of_eq (by ac_rfl)
            · simp only [wp_norm]
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]; assumption
            · simp only [wp_norm]
            · simp only [wp_norm]
            · simp only [wp_norm]
            · simp only [wp_norm]
            · exact htr_sf2
            · simp only [wp_norm]; assumption
            · have hdone := hcont sf_f (gk' :: keys'_tail) v11' v13' w12b'
                (by simp [hklen']) hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f
              rw [List.map_cons, List.zip_cons_cons,
                arrayAt_cons (x := (gk, mkg)),
                arrayAt_cons (x := (gk', (gk, mkg).2)),
                ptr_off_add_104] at hdone
              dsimp only at hdone
              simp only [sepConj_assoc] at hdone
              refine SepWPp.weaken_pre ?_ hdone
              exact Entails.of_eq (by ac_rfl)

theorem chain_clone_local1_placed_mks_nil [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hnil : x.gc.2.messageKeys = [])
    (hpc : s.pc = (blkPl_82).base + 732#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      Qp := by
  have hep := fun s' => chain_clone_local1_placed_epilogue (A := A) (H := H) (Qp := Qp)
    x s0 s' srkPtr' privPtr' 8#64 x25 x28 v9 v10 v13 w27 [] ckPin'
    hsrk hmax (by simp [hnil]) hsrc_klen
  apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (736))
  wp_steps
  refine SepWP.done ?_ ?_ ?_
  · simp only [wp_norm]
  · simp only [wp_norm]; assumption
  · refine SepWPp.weaken_pre ?_
      (hep _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · have hbuf_nil :
          vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) 8#64
            ([].zip x.gc.2.messageKeys) = emp := by
        simpa [hnil] using vecBuf_mk_nil_eq A
      rw [hbuf_nil, emp_sepConj]
      exact Entails.refl _
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · unfold State.readReg32 at hw27 ⊢; simp only [wp_norm]; exact hw27
    · exact htrace
    · simp only [wp_norm]; assumption

set_option maxHeartbeats 1200000 in
theorem chain_clone_local1_placed_mks_nonempty [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_82 H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok (lsProg_82 H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_82 H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpos : 0 < x.gc.2.messageKeys.length)
    (hpc : s.pc = (blkPl_82).base + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 x.gc.2.messageKeys.length)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hpanic860 := fun s P => chain_clone_local1_placed_panic_860 (A := A) (H := H)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    hpanic x s0 s P R
  have hzip_len : (x.gc.1.keys.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
    simp [hsrc_klen]
  have hzip_ne : x.gc.1.keys.zip x.gc.2.messageKeys ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hzip_len]; exact hpos)
  have hloop := fun s' srcCur mkPtr' v11 v13 w12b F =>
    chain_clone_local1_placed_mk_loop (A := A) (H := H)
      (Q := fun sf P_f =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      hshim halloc hmemcpy hpanic x s0 hs0_align
      x.gc.2.messageKeys.length hmax
      (x.gc.1.keys.zip x.gc.2.messageKeys) hzip_ne
      0 (by simp [hzip_len])
      s' srcCur mkPtr' v11 v13 w12b F R
  have hep := fun s' mkPtr' v10' v13' keys' (hklen : keys'.length = x.gc.2.messageKeys.length) =>
    chain_clone_local1_placed_epilogue (A := A) (H := H)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' mkPtr' x25 x28 mkPtr' v10' v13' w27 keys' ckPin'
      hsrk hmax hklen hsrc_klen
  dsimp only [sessionShimSpec] at hshim
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic860 hloop hep ⊢
  rw [chainAt_eq_mk_source A x.gc x.src hsrk hmax hsrc_klen hpos,
      spillSlotsExist_eq_struct s0.sp,
      savedRegsOnStack_eq_core s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ⟨v11, w12b⟩ => ?_
  refine SepWPp.exists_elim fun spSlots => ?_
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 208#64) ↦₆₄ spSlots.v0) ∗
        ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
        ((s0.sp - 196#64) ↦₃₂ spSlots.w1b) ∗
        ((s0.sp - 192#64) ↦₆₄ spSlots.v2) ∗
        ((s0.sp - 184#64) ↦₆₄ spSlots.v3) ∗
        ((s0.sp - 176#64) ↦₆₄ spSlots.v4) ∗
        ((s0.sp - 168#64) ↦₆₄ spSlots.v5) ∗
        ((s0.sp - 160#64) ↦₆₄ spSlots.v6) ∗
        ((s0.sp - 152#64) ↦₆₄ spSlots.v7) ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        savedRegsCore s0) =
      (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        ((s0.sp - 208#64) ↦₆₄ spSlots.v0) ∗
        ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
        ((s0.sp - 196#64) ↦₃₂ spSlots.w1b) ∗
        ((s0.sp - 192#64) ↦₆₄ spSlots.v2) ∗
        ((s0.sp - 184#64) ↦₆₄ spSlots.v3) ∗
        ((s0.sp - 176#64) ↦₆₄ spSlots.v4) ∗
        ((s0.sp - 168#64) ↦₆₄ spSlots.v5) ∗
        ((s0.sp - 160#64) ↦₆₄ spSlots.v6) ∗
        ((s0.sp - 152#64) ↦₆₄ spSlots.v7) ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        savedRegsCore s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hmk_le, hmk_lt, hmk_ptr⟩ => ?_
  have hmul_eq : BitVec.ofNat 64 x.gc.2.messageKeys.length * 104#64 =
      BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length) :=
    mul_104_eq x.gc.2.messageKeys.length
  have hmul_toNat : (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)).toNat =
      104 * x.gc.2.messageKeys.length :=
    toNat_mul_104 hmax
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hmk_lay : LayoutOk (104 * x.gc.2.messageKeys.length) 8 :=
    ⟨by omega, hpow8, by unfold maxMessageKeys at hmax; omega⟩
  apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (308))
  wp_steps
  wp_call hshim ()
  have htr_sf : sf.trace = s0.trace := by rw [‹sf.trace = s.trace›, htrace]
  rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
  wp_compact
  wp_steps
  wp_call halloc (104 * x.gc.2.messageKeys.length, 8)
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (860))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic860 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod8, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (408))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · let mkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
      refine SepWPp.weaken_pre ?_
        (hloop _ x.gc.1.mkPtr mkPtr' v11 v13 w12b
          (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
            ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
            chainMkSourceFrame A x.gc x.src ∗
            ((s0.sp - 208#64) ↦₆₄ x28) ∗
            ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
            ((s0.sp - 196#64) ↦₃₂ w27) ∗
            ((s0.sp - 192#64) ↦₆₄ x25) ∗
            ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
            ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
            ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            ((s0.sp - 152#64) ↦₆₄ x.dst) ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            savedRegsCore s0)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          fun sf_l keys' v11' v13' w12b' hklen_l hpc_l hrun_l hsp_l hx29_l hx19_l htr_l hvregs_l => ?_)
      · rw [hzip_len, BitVec.add_zero]
        exact Entails.of_eq (by dsimp only [mkPtr']; ac_rfl)
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]; assumption
      · simp only [wp_norm, hzip_len]
      · simp only [wp_norm, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      · exact htrace1
      · simp only [wp_norm]; assumption
      · have hklen : keys'.length = x.gc.2.messageKeys.length := hklen_l.trans hzip_len
        have hsp_l_align : sf_l.spAligned = true := by
          rw [State.spAligned, hsp_l]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        have htrunc32 : BitVec.truncate 32 (BitVec.zeroExtend 64 w27) = w27 :=
          (BitVec.setWidth_setWidth_of_le w27 (by decide)).trans (BitVec.setWidth_eq w27)
        simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
          map_snd_zip_of_length_eq x.gc.1.keys x.gc.2.messageKeys hsrc_klen,
          sepConj_assoc]
        apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (736))
        wp_steps
        refine SepWP.done ?_ ?_ ?_
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · refine SepWPp.weaken_pre ?_
            (hep _ mkPtr' (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) v13' keys' hklen
              ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          · have hzip'_len : (keys'.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
              simp [hklen]
            have hzip'_pos : 0 < (keys'.zip x.gc.2.messageKeys).length := by
              rw [hzip'_len]; exact hpos
            have hzip'_max : (keys'.zip x.gc.2.messageKeys).length ≤ maxMessageKeys := by
              rw [hzip'_len]; exact hmax
            have hbuf_eq := vecBuf_mk_pos_eq A mkPtr' (keys'.zip x.gc.2.messageKeys)
              hzip'_pos hzip'_max hoom64
            rw [hzip'_len] at hbuf_eq
            rw [hbuf_eq,
                chainAt_eq_mk_source A x.gc x.src hsrk hmax hsrc_klen hpos,
                spillSlotsExist_eq_struct s0.sp,
                savedRegsOnStack_eq_core s0]
            have hsp_fold :
                (((s0.sp - 208#64) ↦₆₄ x28) ∗
                  ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ w27) ∗
                  ((s0.sp - 192#64) ↦₆₄ x25) ∗
                  ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                  ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                  ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                  ((s0.sp - 152#64) ↦₆₄ x.dst)) ⊢
                (∃∗ s : SpillSlots,
                  ((s0.sp - 208#64) ↦₆₄ s.v0) ∗
                  ((s0.sp - 200#64) ↦₃₂ s.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ s.w1b) ∗
                  ((s0.sp - 192#64) ↦₆₄ s.v2) ∗
                  ((s0.sp - 184#64) ↦₆₄ s.v3) ∗
                  ((s0.sp - 176#64) ↦₆₄ s.v4) ∗
                  ((s0.sp - 168#64) ↦₆₄ s.v5) ∗
                  ((s0.sp - 160#64) ↦₆₄ s.v6) ∗
                  ((s0.sp - 152#64) ↦₆₄ s.v7)) := by
              apply Entails.sepExists_right
                ⟨x28, spSlots.w1a, w27, x25, privPtr',
                  BitVec.ofNat 64 x.gc.1.priv.bytes.length, srkPtr',
                  BitVec.ofNat 64 x.gc.1.srk.bytes.length, x.dst⟩
              dsimp only
              exact Entails.refl _
            have hsr_fold :
                (((s0.sp - 120#64) ↦₆₄ v11') ∗
                  ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                  savedRegsCore s0) ⊢
                (∃∗ p : BitVec 64 × BitVec 32,
                  ((s0.sp - 120#64) ↦₆₄ p.1) ∗
                  ((s0.sp - 108#64) ↦₃₂ p.2) ∗
                  savedRegsCore s0) := by
              apply Entails.sepExists_right (v11', w12b')
              dsimp only
              exact Entails.refl _
            have hsrc_fold :
                (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  chainMkSourceFrame A x.gc x.src) ⊢
                (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
                    x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
                  ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  chainMkSourceFrame A x.gc x.src) :=
              Entails.pure_right ⟨hmk_le, hmk_lt, hmk_ptr⟩ (Entails.refl _)
            have hgroup_pre :
                (arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  arrayAt (messageKeyAt A) 104 mkPtr' (keys'.zip x.gc.2.messageKeys) ∗
                  A.pool ∗
                  stackAt (s0.sp - 208#64) allocHookStack ∗
                  ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
                  ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
                  ((s0.sp - 120#64) ↦₆₄ v11') ∗
                  ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                  ((s0.sp - 104#64) ↦₆₄ v13') ∗
                  A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
                  memRegion x.dst 104 ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                  clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
                  ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  chainMkSourceFrame A x.gc x.src ∗
                  ((s0.sp - 208#64) ↦₆₄ x28) ∗
                  ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ w27) ∗
                  ((s0.sp - 192#64) ↦₆₄ x25) ∗
                  ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                  ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                  ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                  ((s0.sp - 152#64) ↦₆₄ x.dst) ∗
                  ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
                  savedRegsCore s0) =
                (memRegion x.dst 104 ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                  vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                  (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
                    arrayAt (messageKeyAt A) 104 mkPtr' (keys'.zip x.gc.2.messageKeys)) ∗
                  clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
                  (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                    arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                    chainMkSourceFrame A x.gc x.src) ∗
                  A.pool ∗
                  stackAt (s0.sp - 208#64) allocHookStack ∗
                  (((s0.sp - 208#64) ↦₆₄ x28) ∗
                    ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                    ((s0.sp - 196#64) ↦₃₂ w27) ∗
                    ((s0.sp - 192#64) ↦₆₄ x25) ∗
                    ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                    ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                    ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                    ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                    ((s0.sp - 152#64) ↦₆₄ x.dst)) ∗
                  ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
                  ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
                  ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
                  ((s0.sp - 104#64) ↦₆₄ v13') ∗
                  (((s0.sp - 120#64) ↦₆₄ v11') ∗
                    ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                    savedRegsCore s0)) := by
              ac_rfl
            rw [hgroup_pre]
            exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono hsrc_fold
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono hsp_fold
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right hsr_fold))))))))))))
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]; assumption
          · rw [State.spAligned] at hsp_l_align ⊢; simp only [wp_norm]; exact hsp_l_align
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · simp only [wp_norm]
          · unfold State.readReg32; simp only [wp_norm, htrunc32]
          · exact htr_l
          · simp only [wp_norm]; exact hvregs_l

end Placed

end CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
