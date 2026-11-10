/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncodedLen
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodePlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# Relocatable `spqr::send::<signal_session_ratchet::Coins>` Encoded Length & Buffer Allocation (Block `427`)

Proves `Option<VersionNegotiation>`, `Option<Chain>`, and `Option<pq_ratchet_state::Inner>`
encoded-length computation and output `Vec::with_capacity` allocation (`+4288..+4996`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.SpqrV1
open CryptoVerification.RustHeap
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.ProtoRepr hiding tripleRatchetProgAtExt
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec hiding allowPanic_not_exited
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced

variable [LibsignalPlacement]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero spqrSendPlacedEntry
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

/-! ## 1. Callee Contract Helpers for `spqr::send` (Block `427`) -/

theorem spqrSend_handle_alloc_error_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext) :
    (spqrSendPlacedProg ext).externAt? (lsρ spqrHandleErrorSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.handle_error

theorem spqrSend_shim_ok_enc_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    (s0 : State) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      (withStepInv s0 spqrSendShimStackSpec) := by
  have hshim : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym) noAllocShimSpec :=
    spqr_hook_ok_of_mem hA.shim
  apply subroutine_ok_withStepInv s0
  refine subroutine_ok_outcome_intro fun u R s hpc hrun hpre hal => ?_
  dsimp only [spqrSendShimStackSpec] at hpre
  have hpre' : s.mem ⊨ noAllocShimSpec.pre u s ∗ (stackAt s.sp spqrSendCalleeStack ∗ R) := by
    dsimp only [noAllocShimSpec]; rw [emp_sepConj]
    exact hpre
  refine hshim.mono_outcome u (stackAt s.sp spqrSendCalleeStack ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [noAllocShimSpec, spqrSendShimStackSpec] at hpost ⊢
    rwa [sepConj_assoc]
  · exact (allowPanic_not_exited hpan).elim
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

theorem spqrSend_rustAlloc_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    (s0 : State) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (withStepInv s0 (spqrSendRustAllocStackSpec A)) := by
  have halloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
    spqr_hook_ok_of_mem hA.alloc
  apply subroutine_ok_withStepInv s0
  refine subroutine_ok_outcome_intro fun sz R s hpc hrun hpre hal => ?_
  dsimp only [spqrSendRustAllocStackSpec] at hpre
  rw [stackAt_spqrSendCallee_split_enc s.sp allocHookStack (by decide)] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - allocHookStack)
  have hpre' : s.mem ⊨ (rustAllocSpec A).pre (sz, 1) s ∗ (F_rem ∗ R) := by
    dsimp only [rustAllocSpec]
    simp only [satisfies_pure_sepConj, sepConj_assoc] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hpos, hlt⟩, hm⟩
    have hx1' : (s.readReg64 .x1).toNat = 1 := by rw [hx1]; rfl
    refine ⟨⟨hx0, hx1', hpos, ⟨0, rfl⟩, by omega⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hm
  refine halloc.mono_outcome (sz, 1) (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocSpec, spqrSendRustAllocStackSpec] at hpost ⊢
    simp only [Nat.mod_one, true_and] at hpost
    rw [stackAt_spqrSendCallee_split_enc s.sp allocHookStack (by decide)]
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hpost
  · exact (allowPanic_not_exited hpan).elim
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

/-! ## 2. Combined `Option<VersionNegotiation>::encoded_len` (`+4288/+4364 -> +4768`) -/

/-- `spqrSendPlacedEntry + 4288#64 -> spqrSendPlacedEntry + 4768#64`:
Computes `x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn))` from
`versionNegotiationRest A g (s.sp + 4704#64) vn`. -/
theorem step_vn_len_some_3191c_placed {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4288#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : vn.authKey.length < 2 ^ 64) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4768#64) s
      (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' =>
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn)) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)) := by
  refine SepWP.seq (step_vn_len_authKey_3191c_placed (ext := ext) A s g vn F hpc hrun hsp_align hlen) ?_
  intro s1 P1 hpc1 _ ⟨hrun1, hsp1, htr1, hx8_1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp1, hP1⟩
  rw [← hsp1] at hP1
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.seq (step_vn_len_dir_31940_placed (ext := ext) A s1 g vn F hpc1 hrun1 (by rw [hsp1]; exact hsp_align)) ?_
  intro s2 P2 hpc2 _ ⟨hrun2, hsp2, htr2, hx8_2, hx9_2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp2, hP2⟩
  rw [← hsp2] at hP2
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.seq (step_vn_len_minVer_31974_placed (ext := ext) A s2 g vn F hpc2 hrun2 (by rw [hsp2, hsp1]; exact hsp_align)) ?_
  intro s3 P3 hpc3 _ ⟨hrun3, hsp3, htr3, hx8_3, hx9_3, hx10_3, hx19_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp3, hP3⟩
  rw [← hsp3] at hP3
  refine SepWP.weaken_pre hP3 ?_
  refine SepWP.seq (step_vn_len_chainParams_319a0_placed (ext := ext) A s3 g vn F hpc3 hrun3 (by rw [hsp3, hsp2, hsp1]; exact hsp_align)) ?_
  intro s4 P4 hpc4 _ ⟨hrun4, hsp4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hfp4, hP4⟩
  have hsp3_eq : s3.sp = s.sp := hsp3.trans (hsp2.trans hsp1)
  rw [hsp3_eq] at hP4
  refine SepWP.weaken_pre hP4 ?_
  refine SepWP.mono (step_vn_len_combine_31ad4_placed (ext := ext) s4 vn (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
    hpc4 hrun4 (hx8_4.trans (hx8_3.trans (hx8_2.trans hx8_1)))
    (hx9_4.trans (hx9_3.trans hx9_2)) (hx10_4.trans hx10_3) hx11_4) ?_
  intro s5 P5 _ _ ⟨hrun5, hsp5, htr5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hfp5, hP5⟩
  exact ⟨hrun5, hsp5.trans (hsp4.trans hsp3_eq),
    htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1))),
    hx19_5.trans (hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_1))),
    hx20_5,
    hx21_5.trans (hx21_4.trans (hx21_3.trans (hx21_2.trans hx21_1))),
    hx22_5.trans (hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_1))),
    hx23_5.trans (hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_1))),
    hx24_5.trans (hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_1))),
    hx25_5.trans (hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_1))),
    hx26_5.trans (hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_1))),
    hx27_5.trans (hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_1))),
    hx28_5.trans (hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_1))),
    hfp5.trans (hfp4.trans (hfp3.trans (hfp2.trans hfp1))),
    hP5⟩

/-- Unified `Option<VersionNegotiation>::encoded_len` (`+4288/+4364 -> +4768`):
Computes `x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)`. -/
theorem step_vn_len_unified_placed {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : PqRatchetStatePBGhost) (st : PqRatchetState) (F : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry +
      (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4768#64) s
      (optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) st.versionNegotiation ∗ F)
      (fun s' P' =>
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) st.versionNegotiation ∗ F)) := by
  cases hvn : st.versionNegotiation with
  | none =>
    rw [hvn] at hpc
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    exact step_vn_len_none_31968_placed (ext := ext) s
      (optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) none ∗ F) hpc hrun
  | some vn =>
    rw [hvn] at hpc
    simp only [Option.isSome_some, ↓reduceIte] at hpc
    have hlen_vn := vn_authKey_len_lt_of_state hvn hlen
    have hpre_eq :
        optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) (some vn) ∗ F =
        versionNegotiationRest A g.vn (s.sp + 4704#64) vn ∗
          (((s.sp + 4704#64) ↦₆₄ optVersionNegCap g.vn (some vn)) ∗ F) := by
      rw [optVersionNegotiationPBPinnedAt_eq A g.vn (s.sp + 4704#64) (some vn)]
      dsimp only [optVersionNegRest]
      ac_rfl
    refine SepWP.weaken_pre (Entails.of_eq hpre_eq) ?_
    refine SepWP.mono (step_vn_len_some_3191c_placed (ext := ext) A s g.vn vn
      (((s.sp + 4704#64) ↦₆₄ optVersionNegCap g.vn (some vn)) ∗ F) hpc hrun hsp_align hlen_vn) ?_
    intro s' P' _ _ ⟨hrun', hsp', htr', hx19', hx20', hx21', hx22', hx23', hx24', hx25', hx26', hx27', hx28', hfp', hP'⟩
    refine ⟨hrun', hsp', htr', hx19', hx20', hx21', hx22', hx23', hx24', hx25', hx26', hx27', hx28', hfp', ?_⟩
    exact Entails.trans hP' (Entails.of_eq hpre_eq.symm)

/-! ## 3. `Option<Chain>::encoded_len` (`+4768 -> +4844`) -/

/-- `spqrSendPlacedEntry + 4768#64 -> spqrSendPlacedEntry + 4844#64`:
Stores `x22` (`msg_cap`) to `[sp + 0x18]` (`sp + 24#64`), computes `Option<Chain>::encoded_len`
(calling `Chain::encoded_len [local#3]` at `lsmpl.base 485` when `st.chain = some ch`), and sets
`x22 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation + optChainPBFieldEncodedLen st.chain)`. -/
theorem step_send_chain_len_31afc_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    {s0 s1 : State}
    (hChainLen : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 485)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (sp msg_cap v_sp18 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s1.pc = spqrSendPlacedEntry + 4768#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = sp) (htr : s1.trace = s0.trace)
    (hx20 : s1.readReg64 .x20 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation))
    (hx22 : s1.readReg64 .x22 = msg_cap)
    (hx24 : s1.readReg64 .x24 = sp + 4704#64)
    (hx25 : s1.readReg64 .x25 = optChainCap g.chain st.chain)
    (hinv1 : StepInv s0 s1)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      ((sp + 24#64) ↦₆₄ v_sp18) ∗
      stackAt sp spqrSendCalleeStack) ∗ F)
    (hnext : ∀ s2 : State,
      s2.pc = spqrSendPlacedEntry + 4844#64 → s2.status = .Running → s2.sp = sp →
      s2.trace = s0.trace →
      s2.readReg64 .x19 = s1.readReg64 .x19 →
      s2.readReg64 .x21 = s1.readReg64 .x21 →
      s2.readReg64 .x22 =
        BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
          optChainPBFieldEncodedLen st.chain) →
      s2.readReg64 .x23 = s1.readReg64 .x23 →
      s2.readReg64 .x24 = sp + 4704#64 →
      s2.readReg64 .x25 = optChainCap g.chain st.chain →
      s2.readReg64 .x26 = s1.readReg64 .x26 →
      s2.readReg64 .x27 = s1.readReg64 .x27 →
      s2.readReg64 .x28 = s1.readReg64 .x28 →
      s2.readReg64 .fp = s1.readReg64 .fp → StepInv s0 s2 →
      SepWPp (spqrSendPlacedProg ext) ret s2
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          ((sp + 24#64) ↦₆₄ msg_cap) ∗
          stackAt sp spqrSendCalleeStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s1 P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_pure
    ((optChainCap g.chain st.chain + 1#64 == 0#64) = !st.chain.isSome ∧
     (optChainCap g.chain st.chain + 1#64 != 0#64) = st.chain.isSome)
    (fun R' hm => by
      unfold pqRatchetStatePBPinnedAt at hm
      rw [optChainPBPinnedAt_eq] at hm
      have hm' : s1.mem ⊨ optChainRest A g.chain ((sp + 4704#64) + 48#64) st.chain ∗
          (optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
           (((sp + 4704#64) + 48#64) ↦₆₄ optChainCap g.chain st.chain) ∗
           optPqRatchetInnerPBPinnedAt A g.inner ((sp + 4704#64) + 128#64) st.inner ∗
           ((sp + 24#64) ↦₆₄ v_sp18) ∗
           stackAt sp spqrSendCalleeStack ∗ F ∗ R') := by
        convert hm using 1; ac_rfl
      exact optChainRest_cap_bounds hm')
    fun ⟨hch_eq, hch_ne⟩ => ?_
  cases hch : st.chain with
  | none =>
    rw [hch] at hch_eq hch_ne
    simp only [Option.isSome_none, Bool.not_false] at hch_eq hch_ne
    have ⟨hadd1, hadd2⟩ := EncodedLen.adds_no_overflow_of_eq (a := 0)
      (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)
      (c := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen none)
      (by dsimp [optChainPBFieldEncodedLen])
      (by unfold pqRatchetStatePBEncodedLen at hlen; dsimp [optChainPBFieldEncodedLen]; omega)
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply SepWPp.of_sepWP_cs (mid := (blkPl_427).base + 4844#64); wp_steps
    apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext _
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [hch]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv1.trans hinv))
  | some ch =>
    rw [hch] at hch_eq hch_ne
    simp only [Option.isSome_some, Bool.not_true] at hch_eq hch_ne
    have ⟨hfit, hopt_lt, hvar_lt⟩ := chainPBEncodedLen_lt_of_state hch hlen
    have hls := EncodedLen.cmp_ls_false_of_lt hvar_lt hopt_lt
    have hult_ch : (BitVec.ofNat 64 (varintLen (BitVec.ofNat 64 (chainPBEncodedLen ch)))).ult
        (BitVec.ofNat 64 (optChainPBFieldEncodedLen (some ch))) = true := by
      rw [BitVec.ult_iff_lt, BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hopt_lt]
      exact hvar_lt
    have hopt_ch := bv_optChain_some_eq ch
    have ⟨hadd1, hadd2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optChainPBFieldEncodedLen (some ch))
      (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)
      (c := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen (some ch))
      rfl
      (by unfold pqRatchetStatePBEncodedLen at hlen; rw [hch] at hlen; omega)
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply SepWPp.of_sepWP_cs (mid := lsmpl.base 485)
    wp_steps
    apply Prost.EncodeToVec.SepWP.done
      (by simp only [arm64_norm, blkPl_427_ρ, ls_resolve_rel_427_blk_485, *])
      (by simp only [arm64_norm, *]); intro hinv_bl
    refine SepWPp.call_cs (x := ChainEncodedLenPinnedGhost.mk ((sp + 4704#64) + 0x30#64) g.chain ch)
      (F := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
        optPqRatchetInnerPBPinnedAt A g.inner ((sp + 4704#64) + 0x80#64) st.inner ∗
        ((sp + 24#64) ↦₆₄ msg_cap) ∗
        memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - 0x60) ∗ F)
      hChainLen
      (by simp only [arm64_norm, blkPl_427_ρ, ls_resolve_rel_427_blk_485])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
      (ret_pc := (blkPl_427).base + 4788#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
    · intro R' hm
      rw [pqRatchetStatePBPinnedAt, hch, optChainPBPinnedAt,
        stackAt_spqrSendCallee_split_enc sp 0x60 (by decide)] at hm
      simp only [arm64_norm] at hm
      simp only [withStepInv, chainEncodedLenPinnedSpec, arm64_norm, hsp,
        sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hinv1.trans hinv_bl, hfit⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
    · intro sf code R' _ hm
      exact allowPanic_not_exited hm
    · intro sf _ hm
      simp only [withStepInv, chainEncodedLenPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    · intro sm hpcm hrunm hspm hcsm hinv_call
      simp only [arm64_norm, hsp] at hspm
      dsimp only [withStepInv, chainEncodedLenPinnedSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
      simp only [arm64_norm, htr] at htrm
      rcases hcsm with ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, _⟩
      simp only [arm64_norm, hx20, hx22, hx24, hx25] at hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm
      apply SepWPp.of_sepWP_cs (mid := (blkPl_427).base + 4844#64); wp_steps
      apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_post
      refine SepWPp.weaken_pre ?_
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [hch]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (((hinv1.trans hinv_bl).trans hinv_call).trans hinv_post))
      rw [pqRatchetStatePBPinnedAt, hch, optChainPBPinnedAt,
        stackAt_spqrSendCallee_split_enc sp 0x60 (by decide)]
      simp only [arm64_norm, hsp]
      exact Entails.of_eq (by ac_rfl)

/-! ## 4. `Option<pq_ratchet_state::Inner>::encoded_len` (`+4844 -> +4920`) -/

/-- `spqrSendPlacedEntry + 4844#64 -> spqrSendPlacedEntry + 4920#64`:
Computes `Option<pq_ratchet_state::Inner>::encoded_len` (calling `v1::State::encoded_len [local#3]`
at `lsmpl.base 484` when `st.inner = some (.v1 v1s)`) and sets
`x20 = optPqRatchetInnerCap g.inner st.inner`,
`x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)`. -/
theorem step_send_inner_len_31b48_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    {s0 s2 : State} {v1JtAddr : BitVec 64}
    (hV1StateLen : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A v1JtAddr)))
    (sp : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s2.pc = spqrSendPlacedEntry + 4844#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp) (htr : s2.trace = s0.trace)
    (hx22 : s2.readReg64 .x22 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen st.chain))
    (hx24 : s2.readReg64 .x24 = sp + 4704#64)
    (hinv2 : StepInv s0 s2)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      (v1JtAddr ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt sp spqrSendCalleeStack) ∗ F)
    (hnext : ∀ s3 : State,
      s3.pc = spqrSendPlacedEntry + 4920#64 → s3.status = .Running → s3.sp = sp →
      s3.trace = s0.trace →
      s3.readReg64 .x19 = s2.readReg64 .x19 →
      s3.readReg64 .x20 = optPqRatchetInnerCap g.inner st.inner →
      s3.readReg64 .x21 = s2.readReg64 .x21 →
      s3.readReg64 .x22 = s2.readReg64 .x22 →
      s3.readReg64 .x23 = s2.readReg64 .x23 →
      s3.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      s3.readReg64 .x25 = s2.readReg64 .x25 →
      s3.readReg64 .x26 = s2.readReg64 .x26 →
      s3.readReg64 .x27 = s2.readReg64 .x27 →
      s3.readReg64 .x28 = s2.readReg64 .x28 →
      s3.readReg64 .fp = s2.readReg64 .fp → StepInv s0 s3 →
      SepWPp (spqrSendPlacedProg ext) ret s3
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          (v1JtAddr ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt sp spqrSendCalleeStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s2 P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_pure
    ((optPqRatchetInnerCap g.inner st.inner + 3#64 == 0#64) = !st.inner.isSome ∧
     (optPqRatchetInnerCap g.inner st.inner + 3#64 != 0#64) = st.inner.isSome)
    (fun R' hm => ?_) (fun hin_cap => ?_)
  · apply optPqRatchetInnerPBPinnedAt_cap_bounds (A := A) (p := (sp + 4704#64) + 0x80#64)
      (R := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
        optChainPBPinnedAt A g.chain ((sp + 4704#64) + 0x30#64) st.chain ∗
        (v1JtAddr ↦ᵣ v1StateJumpTableBytes) ∗
        stackAt sp spqrSendCalleeStack ∗ F ∗ R')
    rw [pqRatchetStatePBPinnedAt] at hm
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq]
    cases hin : st.inner with
    | none =>
      rw [hin] at hin_cap
      simp only [Option.isSome_none, Bool.not_false] at hin_cap
      have ⟨hadd1, hadd2⟩ := EncodedLen.adds_no_overflow_of_eq (a := 0)
        (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
          optChainPBFieldEncodedLen st.chain)
        (c := pqRatchetStatePBEncodedLen st)
        (by unfold pqRatchetStatePBEncodedLen; rw [hin]; dsimp [optPqRatchetInnerPBFieldEncodedLen])
        (by omega)
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply SepWPp.of_sepWP_cs (mid := (blkPl_427).base + 4920#64); wp_steps
      apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre ?_
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hin]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv2.trans hinv))
      rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq, hin]
      exact Entails.of_eq (by ac_rfl)
    | some innerVal =>
      cases innerVal with
      | v1 v1s =>
        rw [hin] at hin_cap
        simp only [Option.isSome_some, Bool.not_true] at hin_cap
        have ⟨hfit, hopt_lt, hvar_lt⟩ := v1StatePBEncodedLen_lt_of_state hin hlen
        have hls := EncodedLen.cmp_ls_false_of_lt hvar_lt hopt_lt
        have hopt_in := bv_optInner_some_eq v1s
        have ⟨hadd1, hadd2⟩ := EncodedLen.adds_no_overflow_of_eq
          (a := optPqRatchetInnerPBFieldEncodedLen (some (.v1 v1s)))
          (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
            optChainPBFieldEncodedLen st.chain)
          (c := pqRatchetStatePBEncodedLen st)
          (by unfold pqRatchetStatePBEncodedLen; rw [hin])
          (by omega)
        dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
        apply SepWPp.of_sepWP_cs (mid := lsmpl.base 484)
        wp_steps
        apply Prost.EncodeToVec.SepWP.done
          (by simp only [arm64_norm, blkPl_427_ρ, ls_resolve_rel_427_blk_484, *])
          (by simp only [arm64_norm, *]); intro hinv_bl
        refine SepWPp.call_cs (x := PinnedEncLenGhost.mk ((sp + 4704#64) + 0x80#64) g.inner v1s)
          (F := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
            optChainPBPinnedAt A g.chain ((sp + 4704#64) + 0x30#64) st.chain ∗
            memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - v1StateEncodedLenStack) ∗ F)
          hV1StateLen
          (by simp only [arm64_norm, blkPl_427_ρ, ls_resolve_rel_427_blk_484])
          (by simp only [arm64_norm, *])
          (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
          (ret_pc := (blkPl_427).base + 4872#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
        · intro R' hm
          rw [← optPqRatchetInnerPBPinnedAt_eq A g.inner ((sp + 4704#64) + 0x80#64) (some (.v1 v1s)),
            optPqRatchetInnerPBPinnedAt,
            stackAt_spqrSendCallee_split_enc sp v1StateEncodedLenStack (by decide)] at hm
          simp only [arm64_norm] at hm
          simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, arm64_norm, hsp, hx24,
            sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hinv2.trans hinv_bl, hfit⟩, ?_⟩
          exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
        · intro sf code R' _ hm
          exact allowPanic_not_exited hm
        · intro sf _ hm
          simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
          exact hm.1.elim
        · intro sm hpcm hrunm hspm hcsm hinv_call
          simp only [arm64_norm, hsp] at hspm
          dsimp only [withStepInv, v1StateEncodedLenRoPinnedSpec]
          rw [sepConj_assoc]
          refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
          simp only [arm64_norm, htr] at htrm
          rcases hcsm with ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, _⟩
          simp only [arm64_norm, hx22, hx24] at hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm
          apply SepWPp.of_sepWP_cs (mid := (blkPl_427).base + 4920#64); wp_steps
          apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_post
          refine SepWPp.weaken_pre ?_
            (hnext _
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by rw [hin]; simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (((hinv2.trans hinv_bl).trans hinv_call).trans hinv_post))
          rw [pqRatchetStatePBPinnedAt, hin, optPqRatchetInnerPBPinnedAt,
            stackAt_spqrSendCallee_split_enc sp v1StateEncodedLenStack (by decide)]
          simp only [arm64_norm, hsp]
          exact Entails.of_eq (by ac_rfl)

/-! ## 5. `Vec::with_capacity` Allocation (`+4920 -> +4996 / +5604`) -/

private theorem getLsbD_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_beq_zero_false_of_pos {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n = 0 at ht
  omega

/-- `spqrSendPlacedEntry + 4920#64 -> spqrSendPlacedEntry + 4996#64` or `spqrSendPlacedEntry + 5604#64`:
Allocates the output buffer of capacity `pqRatchetStatePBEncodedLen st` via `__rust_alloc`,
initializes `vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr []`,
stores `optChainCap g.chain st.chain` at `[sp + 16#64]`, and branches to `spqrSendPlacedEntry + 4996#64`
if `st.versionNegotiation.isSome`, or `spqrSendPlacedEntry + 5604#64` otherwise. -/
theorem step_send_alloc_31b94_placed
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (hshim : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      (withStepInv s0 spqrSendShimStackSpec))
    (halloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (withStepInv s0 (spqrSendRustAllocStackSpec A)))
    (hhandle : (spqrSendPlacedProg ext).externAt? (lsρ spqrHandleErrorSym) = some Rust.panicked)
    (sp v_sp10 v_590 v_598 v_5a0 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 4920#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st))
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      A.pool ∗
      stackAt sp spqrSendCalleeStack ∗
      ((sp + 16#64) ↦₆₄ v_sp10) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗
      ((sp + 1432#64) ↦₆₄ v_598) ∗
      ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      sm.pc = (if st.versionNegotiation.isSome then spqrSendPlacedEntry + 4996#64 else spqrSendPlacedEntry + 5604#64) →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = ptr →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
          A.pool ∗
          stackAt sp spqrSendCalleeStack ∗
          ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  have hbit63 := getLsbD_63_ofNat_eq_false hlen
  have helem63 := getElem_63_ofNat_eq_false hlen
  have hcbz_f := ofNat_beq_zero_false_of_pos hpos hlen
  refine sepWPp_extract_pure
    ((optVersionNegCap g.vn st.versionNegotiation + 1#64 == 0#64) = !st.versionNegotiation.isSome ∧
     (optVersionNegCap g.vn st.versionNegotiation + 1#64 != 0#64) = st.versionNegotiation.isSome)
    (fun R' hm => by
      unfold pqRatchetStatePBPinnedAt at hm
      rw [optVersionNegotiationPBPinnedAt_eq] at hm
      have hm' : s.mem ⊨ optVersionNegRest A g.vn (sp + 4704#64) st.versionNegotiation ∗
          (((sp + 4704#64) ↦₆₄ optVersionNegCap g.vn st.versionNegotiation) ∗
           optChainPBPinnedAt A g.chain ((sp + 4704#64) + 48#64) st.chain ∗
           optPqRatchetInnerPBPinnedAt A g.inner ((sp + 4704#64) + 128#64) st.inner ∗
           A.pool ∗ stackAt sp spqrSendCalleeStack ∗
           ((sp + 16#64) ↦₆₄ v_sp10) ∗
           ((sp + 1424#64) ↦₆₄ v_590) ∗
           ((sp + 1432#64) ↦₆₄ v_598) ∗
           ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F ∗ R') := by
        convert hm using 1; ac_rfl
      exact optVersionNegRest_cap_bounds hm')
    fun ⟨hvn_eq, hvn_ne⟩ => ?_
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply SepWPp.of_sepWP_cs (mid := lsρ spqrRustNoAllocShimSym); wp_steps
  apply Prost.EncodeToVec.SepWP.done
    (by simp only [arm64_norm, blkPl_427_ρ, *])
    (by simp only [arm64_norm, *])
  intro hinv1
  refine SepWPp.call_cs (x := ())
    (F := pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗ A.pool ∗
      ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F)
    hshim (by simp only [arm64_norm, blkPl_427_ρ]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
    (ret_pc := (blkPl_427).base + 4952#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
  · intro R' hm
    simp only [arm64_norm] at hm
    simp only [withStepInv, spqrSendShimStackSpec, arm64_norm, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0.trans hinv1, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, spqrSendShimStackSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro s1 hpcs1 hruns1 hsps1 hcss1 hinv_s1
    simp only [arm64_norm, hsp] at hsps1
    rcases hcss1 with ⟨hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_28, hs1_fp, _⟩
    simp only [arm64_norm, hx24, hx25, hx26]
      at hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_26 hs1_27 hs1_28 hs1_fp
    dsimp only [withStepInv, spqrSendShimStackSpec]
    simp only [arm64_norm, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrs1 => ?_
    have htrs1' : s1.trace = s0.trace := htrs1.trans htr
    apply SepWPp.of_sepWP_cs (mid := lsρ spqrRustAllocSym); wp_steps
    apply Prost.EncodeToVec.SepWP.done
      (by simp only [arm64_norm, blkPl_427_ρ, *])
      (by simp only [arm64_norm, *])
    intro hinv2
    have htoNat_len : (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)).toNat = pqRatchetStatePBEncodedLen st := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine SepWPp.call_cs (x := pqRatchetStatePBEncodedLen st)
      (F := pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
        ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
        ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F)
      halloc (by simp only [arm64_norm, blkPl_427_ρ]) (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, hsps1, beq_iff_eq]; exact halign)
      (ret_pc := (blkPl_427).base + 4968#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
    · intro R' hm
      simp only [arm64_norm] at hm
      simp only [withStepInv, spqrSendRustAllocStackSpec, arm64_norm, hsps1, htoNat_len,
        sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨(hinv0.trans hinv1).trans (hinv_s1.trans hinv2), hpos, hlen⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
    · intro sf code R' _ hm; exact allowPanic_not_exited hm
    · intro sf _ hm
      simp only [withStepInv, spqrSendRustAllocStackSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    · intro s2 hpcs2 hruns2 hsps2 hcss2 hinv_s2
      simp only [arm64_norm, hsps1] at hsps2
      rcases hcss2 with ⟨hs2_19, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, hs2_25, hs2_26, hs2_27, hs2_28, hs2_fp, _⟩
      simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_26, hs1_27, hs1_28, hs1_fp]
        at hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_26 hs2_27 hs2_28 hs2_fp
      have hinv_s2' : StepInv s0 s2 :=
        ((hinv0.trans hinv1).trans (hinv_s1.trans hinv2)).trans hinv_s2
      dsimp only [withStepInv, spqrSendRustAllocStackSpec]
      simp only [arm64_norm, hsps1]
      by_cases hoom : s2.readReg64 .x0 = 0#64
      · simp only [hoom, ↓reduceIte]
        refine SepWPp.pure_elim fun htrs2 => ?_
        have htrs2' : s2.trace = s0.trace ++ [allocFailedEvent] := by rw [htrs2, htrs1']
        apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym); wp_steps
        apply Prost.EncodeToVec.SepWP.done
          (by simp only [arm64_norm, blkPl_427_ρ, *])
          (by simp only [arm64_norm, *])
        refine SepWPp.panic
          (by simp only [wp_norm, arm64_norm, blkPl_427_ρ, *])
          (by wp_norm_lhs) fun hm_pan => ?_
        exact encodeToVecOnPanic_of_trace
          (by simpa only [Rust.panicked, wp_norm, arm64_norm] using htrs2') hm_pan
      · have hoom_f : (s2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
        simp only [hoom, ↓reduceIte, sepConj_assoc]
        refine SepWPp.pure_elim fun htrs2 => ?_
        have htrs2' : s2.trace = s0.trace := htrs2.trans htrs1'
        cases hvn_case : st.versionNegotiation with
        | none =>
          rw [hvn_case] at hvn_eq hvn_ne
          simp only [Option.isSome_none, Bool.not_false] at hvn_eq hvn_ne
          apply SepWPp.of_sepWP_cs (mid := (blkPl_427).base + 5604#64); wp_steps
          apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          intro hinv3
          refine SepWPp.weaken_pre ?_
            (hnext _ (s2.readReg64 .x0)
              (by rw [hvn_case]; simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (hinv_s2'.trans hinv3))
          rw [← vecU8At_empty_of_alloc A (sp + 1424#64) (s2.readReg64 .x0) (pqRatchetStatePBEncodedLen st) hpos hlen hoom]
          have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
          have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
          rw [h1432, h1440]
          exact Entails.of_eq (by ac_rfl)
        | some vn =>
          rw [hvn_case] at hvn_eq hvn_ne
          simp only [Option.isSome_some, Bool.not_true] at hvn_eq hvn_ne
          apply SepWPp.of_sepWP_cs (mid := (blkPl_427).base + 4996#64); wp_steps
          apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          intro hinv3
          refine SepWPp.weaken_pre ?_
            (hnext _ (s2.readReg64 .x0)
              (by rw [hvn_case]; simp only [↓reduceIte, arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (hinv_s2'.trans hinv3))
          rw [← vecU8At_empty_of_alloc A (sp + 1424#64) (s2.readReg64 .x0) (pqRatchetStatePBEncodedLen st) hpos hlen hoom]
          have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
          have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
          rw [h1432, h1440]
          exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.SpqrV1.Top.Send
