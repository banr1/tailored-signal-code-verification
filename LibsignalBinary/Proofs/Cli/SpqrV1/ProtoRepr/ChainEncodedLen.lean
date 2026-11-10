/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLen
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EpochEncodedLen
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.Fetch
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Fetch
import ProofLib.SepLogic.WPp

/-!
# CLI `Chain::encoded_len` Verification

Proves stage lemmas (`direction`, `current_epoch`, `links`, `next_root`, `send_epoch`, `params`)
and top-level `subroutine_ok` contracts for `<spqr::proto::pq_ratchet::Chain as
prost::message::Message>::encoded_len` on the CLI image.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSpqrV1

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64
  sext64_truncate32 signExtend64_beq_zero64

attribute [local simp] sext64_truncate32 signExtend64_beq_zero64

/-! ## Step 3A: `direction + current_epoch + links + next_root` (`+0x0b8..+0x0ec`) -/

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_next_root (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry epochEntry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry)
    (g : ChainPBGhost) (a : BitVec 64) (ch : ChainPB)
    (hb : ChainBounds g ch)
    (hfit : chainPBEncodedLen ch < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 184#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (i32VarintFieldEncodedLen ch.direction))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (u64VarintFieldEncodedLen ch.currentEpoch))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (chainLinksFieldEncodedLen ch.links))
    (hP : P = chainUnpacked A g a ch ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 240#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (chainPrefix4 ch) →
      ChainHighCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  chain_fetches_range_cli b (Rust.withPanics abs) entry hfn 184 240
  obtain ⟨_, _, _, _, _, hnr_beq, _⟩ := hb
  have hp4_lt : chainPrefix4 ch < 2 ^ 64 := by
    unfold chainPBEncodedLen at hfit
    unfold chainPrefix4 chainPrefix3
    omega
  have hp3_lt : chainPrefix3 ch < 2 ^ 64 := by
    unfold chainPrefix4 at hp4_lt; omega
  have hadd12 := bv_add_ofNat_comm
    (i32VarintFieldEncodedLen ch.direction)
    (u64VarintFieldEncodedLen ch.currentEpoch)
  obtain ⟨hadd3, hcc3_1, hcc3_2, hcc3_3, hcc3_4⟩ :=
    adds_no_overflow_of_eq (a := chainLinksFieldEncodedLen ch.links)
      (b := i32VarintFieldEncodedLen ch.direction + u64VarintFieldEncodedLen ch.currentEpoch)
      (c := chainPrefix3 ch) rfl hp3_lt
  subst hP
  dsimp only [chainUnpacked]
  cases hne : ch.nextRoot.isEmpty with
  | true =>
    have hnr_len : ch.nextRoot.length = 0 := List.isEmpty_iff.mp hne |> congrArg List.length
    have hp4_eq : chainPrefix4 ch = chainPrefix3 ch := by
      dsimp [chainPrefix4, bytesFieldEncodedLen]; simp [hne]
    apply SepWPp.of_sepWP (mid := entry + 240#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all)
      (by simp_all [ChainHighCalleeSaved])
  | false =>
    have henc := bv_bytesField_nonempty hne
    obtain ⟨hadd4, hcc4_1, hcc4_2, hcc4_3, hcc4_4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen ch.nextRoot)
        (b := chainPrefix3 ch) (c := chainPrefix4 ch) rfl hp4_lt
    apply SepWPp.of_sepWP (mid := entry + 240#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all)
      (by simp_all [ChainHighCalleeSaved])

/-! ## Step 3B: `send_epoch` (`+0x0f0..+0x118`) -/

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_send_epoch (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry epochEntry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry)
    (g : ChainPBGhost) (a : BitVec 64) (ch : ChainPB)
    (hfit : chainPBEncodedLen ch < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 240#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (chainPrefix4 ch))
    (hP : P = chainUnpacked A g a ch ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 284#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (chainPrefix5 ch) →
      ChainHighCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  chain_fetches_range_cli b (Rust.withPanics abs) entry hfn 240 284
  have hp5_lt : chainPrefix5 ch < 2 ^ 64 := by
    unfold chainPBEncodedLen at hfit
    unfold chainPrefix5 chainPrefix4 chainPrefix3
    omega
  subst hP
  dsimp only [chainUnpacked]
  by_cases hse : ch.sendEpoch = 0#64
  · have hp5_eq : chainPrefix5 ch = chainPrefix4 ch := by
      dsimp [chainPrefix5, u64VarintFieldEncodedLen]; simp [hse]
    apply SepWPp.of_sepWP (mid := entry + 284#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all)
      (by simp_all [ChainHighCalleeSaved])
  · have hse_beq : (ch.sendEpoch == 0#64) = false := beq_eq_false_iff_ne.mpr hse
    have henc := chain_bv_u64VarintField_nonzero hse
    obtain ⟨hadd5, hcc5_1, hcc5_2, hcc5_3, hcc5_4⟩ :=
      adds_no_overflow_of_eq (a := u64VarintFieldEncodedLen ch.sendEpoch)
        (b := chainPrefix4 ch) (c := chainPrefix5 ch) rfl hp5_lt
    apply SepWPp.of_sepWP (mid := entry + 284#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all)
      (by simp_all [ChainHighCalleeSaved])

/-! ## Step 4A: `params: Option<ChainParams>` (`+0x11c..+0x174` and `+0x1a4..+0x1b0`) -/

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_params (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry epochEntry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry)
    (g : ChainPBGhost) (a : BitVec 64) (ch : ChainPB)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 284#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (chainPrefix5 ch))
    (hP : P = chainUnpacked A g a ch ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 436#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x8 = BitVec.ofNat 64 (chainPrefix5 ch) →
      sm.readReg64 .x9 = BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen ch.params) →
      ChainHighCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  chain_fetches_range_cli b (Rust.withPanics abs) entry hfn 284 376
  chain_fetches_range_cli b (Rust.withPanics abs) entry hfn 420 436
  subst hP
  cases hp : ch.params with
  | none =>
    have hP1 : chainUnpacked A g a ch =
        (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
        vecEpochBuf A g.links.cap g.links.ptr ch.links ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length) ∗
        vecU8Buf A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 48#64) ↦₆₄ ch.currentEpoch) ∗ ((a + 56#64) ↦₆₄ ch.sendEpoch) ∗
        ((a + 64#64) ↦₃₂ 0#32) ∗ memRegion (a + 68#64) 8 ∗
        ((a + 76#64) ↦₃₂ ch.direction) := by
      simp only [chainUnpacked, hp, optChainParamsPBAt, arm64_norm]
    rw [hP1]
    apply SepWPp.of_sepWP (mid := entry + 436#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [optChainParamsPBFieldEncodedLen])
      (by simp_all [ChainHighCalleeSaved])
  | some p =>
    have hP1 : chainUnpacked A g a ch =
        (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
        vecEpochBuf A g.links.cap g.links.ptr ch.links ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length) ∗
        vecU8Buf A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 48#64) ↦₆₄ ch.currentEpoch) ∗ ((a + 56#64) ↦₆₄ ch.sendEpoch) ∗
        ((a + 64#64) ↦₃₂ 1#32) ∗ ((a + 68#64) ↦₃₂ p.maxJump) ∗ ((a + 72#64) ↦₃₂ p.maxOooKeys) ∗
        ((a + 76#64) ↦₃₂ ch.direction) := by
      simp only [chainUnpacked, hp, optChainParamsPBAt, chainParamsPBAt, arm64_norm]
    rw [hP1]
    have hpeq := optChainParamsPBFieldEncodedLen_some_eq p
    by_cases hj : p.maxJump = 0#32
    · by_cases ho : p.maxOooKeys = 0#32
      · apply SepWPp.of_sepWP (mid := entry + 436#64)
        wp_steps
        apply SepWP.done (by simp_all) (by simp_all)
        rw [← hP1]
        exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all [u32VarintFieldEncodedLen])
          (by simp_all [ChainHighCalleeSaved])
      · have ho_beq : (p.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr ho
        have ho_bne : (p.maxOooKeys != 0#32) = true := bne_iff_ne.mpr ho
        have henc_o := bv_u32VarintField_nonzero ho
        have hadd_p : BitVec.ofNat 64 (u32VarintFieldEncodedLen p.maxOooKeys) + 2#64 =
            BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen (some p)) := by
          rw [hpeq, show u32VarintFieldEncodedLen p.maxJump = 0 by simp [u32VarintFieldEncodedLen, hj]]
          simpa using bv_add_ofNat_comm 2 (u32VarintFieldEncodedLen p.maxOooKeys)
        apply SepWPp.of_sepWP (mid := entry + 436#64)
        wp_steps
        apply SepWP.done (by simp_all) (by simp_all)
        rw [← hP1]
        exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all)
          (by simp_all [ChainHighCalleeSaved])
    · have hj_beq : (p.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hj
      have henc_j := bv_u32VarintField_add_three_nonzero hj
      by_cases ho : p.maxOooKeys = 0#32
      · have hpeq0 : optChainParamsPBFieldEncodedLen (some p) = 2 + u32VarintFieldEncodedLen p.maxJump := by
          rw [hpeq, show u32VarintFieldEncodedLen p.maxOooKeys = 0 by simp [u32VarintFieldEncodedLen, ho]]
          omega
        apply SepWPp.of_sepWP (mid := entry + 436#64)
        wp_steps
        apply SepWP.done (by simp_all) (by simp_all)
        rw [← hP1]
        exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all)
          (by simp_all [ChainHighCalleeSaved])
      · have ho_beq : (p.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr ho
        have henc_o := bv_u32VarintField_nonzero ho
        have hadd_p : BitVec.ofNat 64 (u32VarintFieldEncodedLen p.maxOooKeys) +
            BitVec.ofNat 64 (2 + u32VarintFieldEncodedLen p.maxJump) =
            BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen (some p)) := by
          rw [hpeq, bv_add_ofNat_comm]
        apply SepWPp.of_sepWP (mid := entry + 436#64)
        wp_steps
        apply SepWP.done (by simp_all) (by simp_all)
        rw [← hP1]
        exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
          (by simp_all) (by simp_all)
          (by simp_all [ChainHighCalleeSaved])

/-! ## Step 4B: Final Addition + Epilogue (`+0x1b4..+0x1d0`, `436..468`) -/

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_epilogue (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry epochEntry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b abs entry epochEntry)
    (g : ChainPBGhost) (a sp v56 : BitVec 64) (ch : ChainPB)
    (hfit : chainPBEncodedLen ch < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (chainPrefix5 ch))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen ch.params))
    (hhigh : ChainHighCalleeSaved s0 s)
    (hP : P = (chainUnpacked A g a ch ∗ chainSavedFrame sp s0 v56) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (chainPBEncodedLen ch) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  chain_fetches_range_cli b (Rust.withPanics abs) entry hfn 436 468
  rcases hhigh with ⟨h26, h27, h28⟩
  obtain ⟨hadd_final, hccf1, hccf2, hccf3, hccf4⟩ :=
    adds_no_overflow_of_eq (a := optChainParamsPBFieldEncodedLen ch.params)
      (b := chainPrefix5 ch) (c := chainPBEncodedLen ch) rfl hfit
  subst hP
  dsimp only [chainSavedFrame, chainStackFrame]
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by chainEncLen_cc_close)

/-! ## Top-Level `subroutine_ok` Proofs for `Chain::encoded_len` -/

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry epochEntry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsChainEncLenEntry b ext entry epochEntry)
    (hepoch : subroutine_ok (tripleRatchetProgAtExt b ext) epochEntry (epochEncodedLenSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (chainEncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, ch⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  have hepochs := epochEncodedLenFits_of_mem_links (ch := ch)
  simp only [chainEncodedLenPinnedSpec, chainPBPinnedAt_eq_unpacked,
    stackAt_chainEncodedLen_eq, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have hepochs_ch := hepochs hfit
  unfold ChainEncodedLenFits at hfit
  have hpre_u : s0.mem ⊨ chainUnpacked A g a ch ∗
      (stackAt (s0.sp - 80#64) epochEncodedLenStack ∗
        chainStackFrame s0.sp v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 ∗ R) := by
    convert hpre using 1
  have hb := chainUnpacked_bounds hpre_u
  have hmem0 : s0.mem ⊨
      ((chainUnpacked A g a ch ∗
        chainStackFrame s0.sp v80 v72 v64 v56 v48 v40 v32 v24 v16 v8) ∗
        (stackAt (s0.sp - 80#64) epochEncodedLenStack ∗ R)) := by
    convert hpre using 1; ac_rfl
  let F0 : SepProp := stackAt (s0.sp - 80#64) epochEncodedLenStack ∗ R
  refine ⟨(chainUnpacked A g a ch ∗
      chainStackFrame s0.sp v80 v72 v64 v56 v48 v40 v32 v24 v16 v8) ∗ F0, emp,
    by rw [sepConj_emp]; exact hmem0, ?_⟩
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_prologue_dir (F := F0) b A ext entry epochEntry hfn g a s0.sp
    v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 ch hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx8_1 hhigh1
  let FSave : SepProp := chainSavedFrame s0.sp s0 v56 ∗ F0
  have hP_save : (chainUnpacked A g a ch ∗ chainSavedFrame s0.sp s0 v56) ∗ F0 =
      chainUnpacked A g a ch ∗ FSave := by
    dsimp [FSave]; ac_rfl
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_current_epoch (F := FSave) b A ext entry epochEntry hfn g a ch hb
    hpc1 hrun1 hx19_1 hx21_1 hx8_1 hP_save ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx21_2 hx22_2 hx23_2 hhigh2
  have hsp2' : s2.sp = s0.sp - 80#64 := hsp2.trans hsp1
  have htr2' : s2.trace = s0.trace := htr2.trans htr1
  have hhigh2' : ChainHighCalleeSaved s0 s2 := hhigh1.trans hhigh2
  -- Continuation from `entry + 184#64` (`+0x0b8`) onwards:
  have hcont : ∀ s3 : State,
      s3.pc = entry + 184#64 →
      s3.status = .Running →
      s3.sp = s0.sp - 80#64 →
      s3.trace = s0.trace →
      s3.readReg64 .x19 = a →
      s3.readReg64 .x21 = BitVec.ofNat 64 (i32VarintFieldEncodedLen ch.direction) →
      s3.readReg64 .x22 = BitVec.ofNat 64 (u64VarintFieldEncodedLen ch.currentEpoch) →
      s3.readReg64 .x8 = BitVec.ofNat 64 (chainLinksFieldEncodedLen ch.links) →
      ChainHighCalleeSaved s0 s3 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s3
        ((chainUnpacked A g a ch ∗ chainSavedFrame s0.sp s0 v56) ∗ F0)
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ emp) → (sf.mem ⊨ (chainEncodedLenPinnedSpec A).post ⟨a, g, ch⟩ s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ emp) → (sf.mem ⊨ (chainEncodedLenPinnedSpec A).onPanic ⟨a, g, ch⟩ s0 sf ∗ R)) := by
    intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx21_3 hx22_3 hx8_3 hhigh3
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_next_root (F := FSave) b A ext entry epochEntry hfn g a ch hb hfit
      hpc3 hrun3 hx19_3 hx21_3 hx22_3 hx8_3 hP_save ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx8_4 hhigh4
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_send_epoch (F := FSave) b A ext entry epochEntry hfn g a ch hfit
      hpc4 hrun4 hx19_4 hx8_4 hP_save ?_
    intro s5 hpc5 hrun5 hsp5 htr5 hx19_5 hx8_5 hhigh5
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_params (F := FSave) b A ext entry epochEntry hfn g a ch
      hpc5 hrun5 hx19_5 hx8_5 hP_save ?_
    intro s6 hpc6 hrun6 hsp6 htr6 hx8_6 hx9_6 hhigh6
    have hsp6' : s6.sp = s0.sp - 80#64 := by rw [hsp6, hsp5, hsp4, hsp3]
    have hhigh6' : ChainHighCalleeSaved s0 s6 :=
      hhigh3.trans (hhigh4.trans (hhigh5.trans hhigh6))
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_epilogue (F := F0) b A ext entry epochEntry hfn g a s0.sp v56 ch hfit
      hpc6 hrun6 hsp6' halign hx8_6 hx9_6 hhigh6' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [chainEncodedLenPinnedSpec, chainPBPinnedAt_eq_unpacked,
      stackAt_chainEncodedLen_eq, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x25, v56,
      s0.readReg64 .x24, s0.readReg64 .x23, s0.readReg64 .x22, s0.readReg64 .x21,
      s0.readReg64 .x20, s0.readReg64 .x19,
      ⟨hx0_f, by rw [htrf, htr6, htr5, htr4, htr3]⟩, ?_⟩
    dsimp [F0, chainSavedFrame] at hm_f
    convert hm_f using 1; ac_rfl
  cases hle : ch.links.isEmpty with
  | true =>
    simp only [hle, ↓reduceIte] at hpc2
    have hlinks_nil : ch.links = [] := List.isEmpty_iff.mp hle
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_links_empty b ext entry epochEntry hfn ch hlinks_nil hpc2 hrun2 hx23_2 ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx21_3 hx22_3 hx8_3 hhigh3
    exact hcont s3 hpc3 hrun3 (hsp3.trans hsp2') (htr3.trans htr2')
      (hx19_3.trans hx19_2) (hx21_3.trans hx21_2) (hx22_3.trans hx22_2) hx8_3
      (hhigh2'.trans hhigh3)
  | false =>
    simp only [hle, Bool.false_eq_true, ↓reduceIte] at hpc2
    have hlinks_ne : ch.links ≠ [] := by
      intro hnil; rw [hnil] at hle; cases hle
    have hcap_ne : g.links.cap ≠ 0 := by
      have hpos : 0 < ch.links.length := List.length_pos_of_ne_nil hlinks_ne
      have hle_cap := hb.1
      intro h0
      rw [h0] at hle_cap
      change ch.links.length ≤ (0#64).toNat at hle_cap
      rw [BitVec.toNat_zero] at hle_cap
      omega
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_links_init (F := FSave) b A ext entry epochEntry hfn g a ch
      hpc2 hrun2 hx19_2 hx23_2 hP_save ?_
    intro s2i hpc2i hrun2i hsp2i htr2i hx19_2i hx20_2i hx21_2i hx22_2i hx23_2i hx24_2i hx25_2i hhigh2i
    have hsp2i' : s2i.sp = s0.sp - 80#64 := hsp2i.trans hsp2'
    have hsp2i_al : s2i.spAligned = true := by
      simp only [State.spAligned, beq_iff_eq, hsp2i']
      bv_bits
    let FLoop : SepProp :=
      (⌜ch.links.length ≤ g.links.cap.toNat ∧ g.links.cap.toNat * 112 < 2 ^ 63 ∧
          g.links.ptr ≠ 0⌝ ∗
        A.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
        memRegion (g.links.ptr + BitVec.ofNat 64 (ch.links.length * 112))
          ((g.links.cap.toNat - ch.links.length) * 112)) ∗
      (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length) ∗
      vecU8Buf A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
      ((a + 48#64) ↦₆₄ ch.currentEpoch) ∗ ((a + 56#64) ↦₆₄ ch.sendEpoch) ∗
      optChainParamsPBAt (a + 64#64) ch.params ∗ ((a + 76#64) ↦₃₂ ch.direction) ∗
      chainSavedFrame s0.sp s0 v56 ∗ R
    have hP_loop :
        ((chainUnpacked A g a ch ∗ chainSavedFrame s0.sp s0 v56) ∗ F0) =
        (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 g.links.ptr ch.links ∗
          stackAt s2i.sp epochEncodedLenStack) ∗ FLoop := by
      rw [hsp2i']
      dsimp only [chainUnpacked, F0, FLoop]
      rw [vecEpochBuf_eq_of_ne_zero hcap_ne]
      ac_rfl
    have hfit_loop : 0 + chainLinksBodiesEncodedLen ch.links + ch.links.length < 2 ^ 64 := by
      unfold chainPBEncodedLen chainLinksFieldEncodedLen at hfit
      omega
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_links_loop (F := FLoop) b A ext entry epochEntry hfn hepoch
      ch.links hlinks_ne g.links.ptr 0 ch.links.length
      (by have := hb.2.1; omega) hepochs_ch hfit_loop
      hpc2i hrun2i hsp2i_al hx20_2i hx23_2i hx24_2i hx25_2i hP_loop ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx21_3 hx22_3 hx8_3 hhigh3
    rw [Nat.zero_add] at hx8_3
    exact hcont s3 hpc3 hrun3 (hsp3.trans hsp2i') (htr3.trans (htr2i.trans htr2'))
      (hx19_3.trans hx19_2i)
      (hx21_3.trans (hx21_2i.trans hx21_2))
      (hx22_3.trans (hx22_2i.trans hx22_2))
      hx8_3
      (hhigh2'.trans (hhigh2i.trans hhigh3))

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.ChainEncodedLenLocal1PinnedOkExt b A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_entry_pinned_ok_ext b A ext _ _ (Or.inl ⟨rfl, rfl⟩)
    (CryptoVerification.Cli.SpqrV1.ProtoRepr.epochEncodedLen_local1_ok_ext b A ext)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.ChainEncodedLenLocal1OkExt b A ext :=
  chainEncodedLen_ok_of_pinned (CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local1_pinned_ok_ext b A ext)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.ChainEncodedLenLocal1PinnedOk b C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.ChainEncodedLenLocal1Ok b C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) :
    ChainEncodedLenLocal2PinnedOkExt b A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_entry_pinned_ok_ext b A ext _ _ (Or.inr ⟨rfl, rfl⟩)
    (CryptoVerification.Cli.SpqrV1.ProtoRepr.epochEncodedLen_local2_ok_ext b A ext)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) :
    ChainEncodedLenLocal2OkExt b A ext :=
  chainEncodedLen_ok_of_pinned (CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local2_pinned_ok_ext b A ext)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChainEncodedLenLocal2PinnedOk b C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChainEncodedLenLocal2Ok b C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.chainEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)

end CryptoVerification.SpqrV1.ProtoRepr
