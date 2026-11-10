/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeys
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Segment S6 (`DeriveKeys`) Proofs for `try_decrypt_with_state`

Proves the relocatable `[LibsignalPlacement]` Segment S6 seam theorems (`deriveKeys_159_placed_ok`,
`deriveKeys_549_placed_ok`, `deriveKeys_159_placed_ok_x`, `deriveKeys_549_placed_ok_x`) over
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (
  Crypto TripleRatchet SessionState MessageKeyGenerator
)
open CryptoVerification (
  LibsignalPlacement lsmpl
)
open CryptoVerification.RustHeap (
  RustAlloc vecHeader vecU8At
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  protocolAddressAt signalMessageAt sessionStateAt tapeAfter
)
open CryptoVerification.LibsignalTripleRatchet (
  GenerateKeysGhost generateKeysStack generateKeysStackX
  mkgAt spqrRecvKeyAt messageKeysAt
  TrGhost trAt TryDecryptGhost
  LibsignalCodeRoLoaded withLsCodeRoLoaded logOff
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_131 blkPl_131
  blkPC_434 blkPl_434
  segDeriveKeysPC_at segVerifyMacPC_at
  tryDecryptMidMetaPlaced tryDecryptCommonHeap tryDecryptSubStack
  tryDecryptSavedRegs tryDecryptPlacedImg logOff_tryDecryptPlacedImg
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (
  extractLsb0_8_append56
  sp_fp_eq mr_cut_add
  pointsTo64_split32 pointsTo32_merge64
  optKeyAt_split optKeyAt_fold mkgAt_fold stackAt_sub
)
open scoped LibsignalBinary.Proofs.Placed.BudgetVmSteps
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  VmPreserved FreeOnlyEvs FitsEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (
  GenerateKeysEnv freeOnlyEvs_of_generateKeysEnv
  generateKeysSpecWithStack generateKeysSpec generateKeysSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  DeriveKeysStatePlaced VerifyMacStatePlaced S6SeamPlaced S6SeamXPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget (
  protocolAddressAt_atState signalMessageAt_atState sessionStateAt_atState
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

/-! ## 1. `atState` Normalization & `VmPreserved` Call Combinators -/

private theorem atState_eq_of_live_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {α : Type} (f : RustAlloc → α)
    (h : ∀ a b : RustAlloc, a.live = b.live → f a = f b) :
    f (A.atState lim st s) = f A.repAlloc :=
  h _ _ rfl

private theorem vecU8At_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At (A.atState lim st s) v cap ptr bs = vecU8At A.repAlloc v cap ptr bs := by
  unfold vecU8At
  rfl

private theorem mkgAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (p : BitVec 64) (g : MessageKeyGenerator) :
    mkgAt (A.atState lim st s) p g = mkgAt A.repAlloc p g := by
  unfold mkgAt
  rfl

private theorem spqrRecvKeyAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (p : BitVec 64) (k : Salt) :
    spqrRecvKeyAt (A.atState lim st s) p k = spqrRecvKeyAt A.repAlloc p k := by
  unfold spqrRecvKeyAt
  rfl

private theorem trAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (p : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt (A.atState lim st s) p trG tr = trAt A.repAlloc p trG tr := by
  unfold trAt
  rfl

/-- Two-phase `reaches_pc` combinator: the straight-line prefix `h1` runs via
`BudgetVmSteps.sepWP_rebase_vmPreserved` to transport `A.pool lim st s` to `A.pool lim st sm`,
and the callee step `h2` calls a `withLsCodeRoLoaded` budget contract whose postcondition
already indexes `A.pool` at the return state `sf`. -/
private theorem reaches_pc_of_vm_and_cro_call [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P R : SepProp} {P_mid : State → SepProp}
    {RegMid Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧
        (VmPreserved s sm → (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid sm ∗ R))))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      RegMid sm → SepWP prog target sm (P_mid sm)
        (fun sf P_f => LibsignalCodeRoLoaded lsmpl sf.mem → (sf.mem ⊨ P_f ∗ R) → Q sf)) :
    reaches_pc prog target s Q := by
  intro hL
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hvm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hvm hmm
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    rcases (h2 sm hpc hrun hclm hReg).elim hmm' (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpcf, hrunf, P_f, hmf, hq⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, hq (hclm.of_keepsFrozen hsteps'.keepsFrozen) hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Canonical free-only envelope for Segment S6 (`<MessageKeyGenerator>::generate_keys`). -/
abbrev s6FreeOnlyEnv (_ : MessageKeyGenerator) : List AllocEvent → Prop :=
  FreeOnlyEvs

theorem s6FreeOnlyEnv_inhabited (mkg : MessageKeyGenerator) :
    ∃ evs, s6FreeOnlyEnv mkg evs :=
  ⟨[], FreeOnlyEvs.nil⟩

/-! ## 2. Stack-Parametric Segment S6 Proofs (`blkPC_131` & `blkPC_434`) -/

private theorem deriveKeys_159_placed_ok_withStack [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (H : String → Option (State → State))
    {genStack : Nat}
    (hstack_sub : ∀ sp : BitVec 64,
      stackAt sp tryDecryptSubStack =
        memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - genStack) ∗
          stackAt sp genStack)
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    (hs6Env : ∀ (x : GenerateKeysGhost) evs, GenerateKeysEnv x evs → s6Env x.g evs)
    (hgen : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 69)
      (withLsCodeRoLoaded lsmpl (generateKeysSpecWithStack M A lim C.F genStack))) :
    S6SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A lim ctl s6Env := by
  intro x st trG tr st1 mkg newPqrState pqrKey draws R s0 s hseed_len _hfit h6
  unfold DeriveKeysStatePlaced at h6
  rcases h6 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25, hx27, hx28,
    seedCap, seedPtr, newPqrCap, newPqrPtr, msgW, hx8, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  unfold segDeriveKeysPC_at at hpc
  rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl] at hpc
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  unfold tryDecryptCommonHeap at hmem
  rw [sessionStateAt_atState, trAt_atState, RustCliAllocBudget.atState_live,
    vecU8At_atState, spqrRecvKeyAt_atState,
    protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
    RustCliAllocBudget.atState_pool] at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx27 hx28 hx29 hsp29_eq hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  have hreach : reaches_pc ((blkPC_131).rebase (blkPl_131).base H)
      ((blkPl_131).base + 1596#64) s
      (fun sf => ∃ evs, s6Env mkg evs ∧
        (sf.sp = sp ∧ (s0.sp &&& 15#64 == 0#64) = true ∧ sf.spAligned = true ∧
          sf.readReg64 .fp = sp + 1408#64 ∧ sf.trace = s0.trace ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        VerifyMacStatePlaced (blkPl_131).base A lim (M.stepEvents evs st) ctl
          x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0 sf) := by
    refine reaches_pc_of_vm_and_cro_call hmem (hcl := hcl)
      (mid := lsmpl.base 69)
      (RegMid := fun sm =>
        newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
        sm.readReg64 .x0 = sp + 400#64 ∧
        sm.readReg64 .x1 = sp + 864#64 ∧
        sm.readReg64 .x8 = sp + 1280#64 ∧
        sm.readReg64 .lr = (blkPl_131).base + 1596#64 ∧
        sm.readReg64 .x19 = x.ret ∧
        sm.readReg64 .x20 = sp + 320#64 ∧
        sm.readReg64 .x21 = x.ss ∧
        sm.readReg64 .x22 = x.msgA ∧
        sm.readReg64 .x23 = sp + 976#64 ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
        sm.readReg64 .x25 = sp + 400#64 ∧
        sm.readReg64 .x27 = sp + 56#64 ∧
        sm.readReg64 .x28 = sp + 1280#64 ∧
        sm.readReg64 .fp = sp + 1408#64 ∧
        sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      (P_mid := fun sm =>
        mkgAt A.repAlloc (sp + 400#64) mkg ∗
        spqrRecvKeyAt A.repAlloc (sp + 864#64) pqrKey ∗
        memRegion (sp + 1280#64) 84 ∗
        A.pool lim st sm ∗ stackAt sp tryDecryptSubStack ∗
        sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
        trAt A.repAlloc (sp + 56#64) trG tr ∗
        (if newPqrCap = 0 then emp else A.repAlloc.live newPqrPtr newPqrCap.toNat 1 ∗
          (newPqrPtr ↦ₛ newPqrState) ∗
          memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length)
            (newPqrCap.toNat - newPqrState.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 8 ∗
        ((sp + 8#64) ↦₆₄ newPqrCap) ∗
        memRegion (sp + 16#64) 12 ∗
        ((sp + 28#64) ↦₃₂ msgW) ∗
        ((sp + 32#64) ↦₆₄ x.locA) ∗
        ((sp + 40#64) ↦₆₄ newPqrPtr) ∗
        ((sp + 48#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 320#64) 80 ∗
        memRegion (sp + 440#64) 424 ∗
        memRegion (sp + 888#64) 216 ∗
        memRegion (sp + 1104#64) 176 ∗
        memRegion (sp + 1364#64) 44 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        tapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        tryDecryptSavedRegs s0.sp s0)
      ?_ ?_
    · by_vm_steps (
      wp_conv_pre =>
        simp only [sepConj_assoc]
        unfold vecU8At vecHeader
        rw [memRegion_split sp 8 8 (by decide),
          mr_cut_add sp 320 80 704 (by decide),
          mr_cut_add sp 400 8 696 (by decide),
          mr_cut_add sp 408 8 688 (by decide),
          mr_cut_add sp 416 8 680 (by decide),
          mr_cut_add sp 424 8 672 (by decide),
          mr_cut_add sp 432 8 664 (by decide),
          mr_cut_add sp 440 8 656 (by decide),
          mr_cut_add sp 448 8 648 (by decide),
          mr_cut_add sp 456 8 640 (by decide),
          mr_cut_add sp 464 8 632 (by decide),
          mr_cut_add sp 472 8 624 (by decide),
          mr_cut_add sp 480 8 616 (by decide),
          mr_cut_add sp 488 376 240 (by decide),
          mr_cut_add sp 864 8 232 (by decide),
          mr_cut_add sp 872 8 224 (by decide),
          mr_cut_add sp 880 8 216 (by decide),
          mr_cut_add sp 1116 4 160 (by decide),
          mr_cut_add sp 1120 8 152 (by decide),
          mr_cut_add sp 1128 8 144 (by decide),
          mr_cut_add sp 1136 8 136 (by decide),
          mr_cut_add sp 1144 8 128 (by decide),
          mr_cut_add sp 1152 8 120 (by decide),
          mr_cut_add sp 1160 8 112 (by decide)]
        simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
          memRegion_eight (sp + 8#64),
          memRegion_eight (sp + 400#64),
          memRegion_eight (sp + 408#64),
          memRegion_eight (sp + 416#64),
          memRegion_eight (sp + 424#64),
          memRegion_eight (sp + 432#64),
          memRegion_eight (sp + 440#64),
          memRegion_eight (sp + 448#64),
          memRegion_eight (sp + 456#64),
          memRegion_eight (sp + 464#64),
          memRegion_eight (sp + 472#64),
          memRegion_eight (sp + 480#64),
          memRegion_eight (sp + 864#64),
          memRegion_eight (sp + 872#64),
          memRegion_eight (sp + 880#64),
          memRegion_four (sp + 1116#64),
          memRegion_eight (sp + 1120#64),
          memRegion_eight (sp + 1128#64),
          memRegion_eight (sp + 1136#64),
          memRegion_eight (sp + 1144#64),
          memRegion_eight (sp + 1152#64),
          memRegion_eight (sp + 1160#64),
          CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.pointsTo64_split32 (sp + 400#64)]
      refine SepWP.focus_weaken (optKeyAt_split A.repAlloc (sp + 1304#64) pqrKey) (by sep_focus) ?_
      wp_pull_exists
      wp_focus_pure
      rintro ⟨hnp1, hnp2, hnp3⟩
      refine SepWP.focus_rw (pointsTo32_merge64 (sp + 1112#64) mkg.counter _) (by sep_focus) ?_
      wp_steps
      rw [show ((sp + 424#64) ↦₆₄ 32#64) = ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) by
        rw [hseed_len]]
      refine SepWP.focus_weaken (optKeyAt_fold A.repAlloc (sp + 864#64) _ _ _ pqrKey) (by sep_focus) ?_
      refine SepWP.focus_weaken (mkgAt_fold A.repAlloc (sp + 400#64) seedCap seedPtr _ _ mkg hseed)
        (by sep_focus) ?_
      have hm16 : memRegion (sp + 16#64) 12 = memRegion (sp + 16#64) 8 ∗ memRegion (sp + 24#64) 4 := by
        simpa using mr_cut_add sp 16 8 4 (by decide)
      have hm440 : memRegion (sp + 440#64) 424 =
          memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗ (memRegion (sp + 456#64) 8 ∗
          (memRegion (sp + 464#64) 8 ∗ (memRegion (sp + 472#64) 8 ∗ (memRegion (sp + 480#64) 8 ∗
          memRegion (sp + 488#64) 376))))) := by
        rw [mr_cut_add sp 440 8 416 (by decide),
          mr_cut_add sp 448 8 408 (by decide),
          mr_cut_add sp 456 8 400 (by decide),
          mr_cut_add sp 464 8 392 (by decide),
          mr_cut_add sp 472 8 384 (by decide),
          mr_cut_add sp 480 8 376 (by decide)]
      have hm1104 : memRegion (sp + 1104#64) 176 =
          memRegion (sp + 1104#64) 8 ∗ (memRegion (sp + 1112#64) 8 ∗ (memRegion (sp + 1120#64) 8 ∗
          (memRegion (sp + 1128#64) 8 ∗ (memRegion (sp + 1136#64) 8 ∗ (memRegion (sp + 1144#64) 8 ∗
          (memRegion (sp + 1152#64) 8 ∗ (memRegion (sp + 1160#64) 8 ∗ memRegion (sp + 1168#64) 112))))))) := by
        rw [mr_cut_add sp 1104 8 168 (by decide),
          mr_cut_add sp 1112 8 160 (by decide),
          mr_cut_add sp 1120 8 152 (by decide),
          mr_cut_add sp 1128 8 144 (by decide),
          mr_cut_add sp 1136 8 136 (by decide),
          mr_cut_add sp 1144 8 128 (by decide),
          mr_cut_add sp 1152 8 120 (by decide),
          mr_cut_add sp 1160 8 112 (by decide)]
      have hm1280 : memRegion (sp + 1280#64) 84 =
          memRegion (sp + 1280#64) 8 ∗ (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗
          (memRegion (sp + 1304#64) 8 ∗ (memRegion (sp + 1312#64) 8 ∗ (memRegion (sp + 1320#64) 8 ∗
          memRegion (sp + 1328#64) 36))))) := by
        rw [mr_cut_add sp 1280 8 76 (by decide),
          mr_cut_add sp 1288 8 68 (by decide),
          mr_cut_add sp 1296 8 60 (by decide),
          mr_cut_add sp 1304 8 52 (by decide),
          mr_cut_add sp 1312 8 44 (by decide),
          mr_cut_add sp 1320 8 36 (by decide)]
      have hm1328 : memRegion (sp + 1328#64) 80 =
          memRegion (sp + 1328#64) 36 ∗ memRegion (sp + 1364#64) 44 := by
        simpa using mr_cut_add sp 1328 36 44 (by decide)
      rw [hm16, hm440, hm1104, hm1280, hm1328]
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm hm_out
      rw [← A.pool_of_vmPreserved hvm] at hm_out
      refine ⟨⟨hnp1, hnp2, hnp3,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩, ?_⟩
      arm64_sep_close
      )
    · intro sm hpcm hrunm ⟨hcl_code, hcl_ro⟩ hReg
      rcases hReg with ⟨hnp1, hnp2, hnp3, hx0m, hx1m, hx8m, hlrm,
        hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
      rw [hstack_sub sp, show stackAt sp genStack = stackAt sm.sp genStack by rw [hspm]]
      wp_call hgen (⟨sp + 400#64, mkg, sp + 864#64, pqrKey, sp + 1280#64⟩, st)
      have hevs_gen : GenerateKeysEnv ⟨sp + 400#64, mkg, sp + 864#64, pqrKey, sp + 1280#64⟩ w := hpost
      have htrace_f : sf.trace = sm.trace := by assumption
      have hm320 : memRegion (sp + 320#64) 960 =
          memRegion (sp + 320#64) 80 ∗ (memRegion (sp + 400#64) 40 ∗
          (memRegion (sp + 440#64) 424 ∗ (memRegion (sp + 864#64) 24 ∗
          (memRegion (sp + 888#64) 216 ∗ memRegion (sp + 1104#64) 176)))) := by
        rw [mr_cut_add sp 320 80 880 (by decide),
          mr_cut_add sp 400 40 840 (by decide),
          mr_cut_add sp 440 424 416 (by decide),
          mr_cut_add sp 864 24 392 (by decide),
          mr_cut_add sp 888 216 176 (by decide)]
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_
      intro hcl_sf sf_mem
      have hsp_sf : sf.sp = sp := by simp only [wp_norm, arm64_norm, *]
      refine ⟨w, hs6Env ⟨sp + 400#64, mkg, sp + 864#64, pqrKey, sp + 1280#64⟩ w hevs_gen, ?_, ?_⟩
      · refine ⟨hsp_sf, hsp0_al',
          by simp only [State.spAligned, wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
      · unfold VerifyMacStatePlaced CryptoVerification.LibsignalTripleRatchet.Decrypt.VerifyMacStatePlaced
          segVerifyMacPC_at tryDecryptMidMetaPlaced tryDecryptCommonHeap
        rw [show (0x63c#64 : BitVec 64) = 1596#64 by rfl]
        refine ⟨by simp only [wp_norm, arm64_norm, *], ?_,
          by simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          newPqrCap, newPqrPtr, msgW, hmsgW, hnp1, hnp2, hnp3, ?_⟩
        · refine ⟨by simp only [wp_norm, arm64_norm, *],
            by rw [hsp_def]; exact hsp_sf,
            hsp0_al',
            by simp only [State.spAligned, wp_norm, arm64_norm, *],
            by change _ = s0.sp - 96#64; rw [hsp29_eq]; simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            hcl_sf,
            by simp only [wp_norm, arm64_norm, *]⟩
        · rw [hsp_def, sessionStateAt_atState, trAt_atState, RustCliAllocBudget.atState_live,
            protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
            logOff_tryDecryptPlacedImg, RustCliAllocBudget.atState_pool, hstack_sub sp,
            show BitVec.ofNat 64 tryDecryptSubStack = 260640#64 by rfl, hm320]
          rw [hspm] at sf_mem
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) sf_mem
  intro hL
  rcases hreach hL with ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, evs, hevs, _hmeta_core, hvmac⟩ | ⟨hpan_sf, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc_sf, hrun_sf, evs, hevs, hvmac⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan_sf, hoom⟩⟩

private theorem deriveKeys_549_placed_ok_withStack [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (H : String → Option (State → State))
    {genStack : Nat}
    (hstack_sub : ∀ sp : BitVec 64,
      stackAt sp tryDecryptSubStack =
        memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - genStack) ∗
          stackAt sp genStack)
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    (hs6Env : ∀ (x : GenerateKeysGhost) evs, GenerateKeysEnv x evs → s6Env x.g evs)
    (hgen : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 69)
      (withLsCodeRoLoaded lsmpl (generateKeysSpecWithStack M A lim C.F genStack))) :
    S6SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A lim ctl s6Env := by
  intro x st trG tr st1 mkg newPqrState pqrKey draws R s0 s hseed_len _hfit h6
  unfold DeriveKeysStatePlaced at h6
  rcases h6 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25, hx27, hx28,
    seedCap, seedPtr, newPqrCap, newPqrPtr, msgW, hx8, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  unfold segDeriveKeysPC_at at hpc
  rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl] at hpc
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  unfold tryDecryptCommonHeap at hmem
  rw [sessionStateAt_atState, trAt_atState, RustCliAllocBudget.atState_live,
    vecU8At_atState, spqrRecvKeyAt_atState,
    protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
    RustCliAllocBudget.atState_pool] at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx27 hx28 hx29 hsp29_eq hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  have hreach : reaches_pc ((blkPC_434).rebase (blkPl_434).base H)
      ((blkPl_434).base + 1596#64) s
      (fun sf => ∃ evs, s6Env mkg evs ∧
        (sf.sp = sp ∧ (s0.sp &&& 15#64 == 0#64) = true ∧ sf.spAligned = true ∧
          sf.readReg64 .fp = sp + 1408#64 ∧ sf.trace = s0.trace ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        VerifyMacStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
          x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0 sf) := by
    refine reaches_pc_of_vm_and_cro_call hmem (hcl := hcl)
      (mid := lsmpl.base 69)
      (RegMid := fun sm =>
        newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
        sm.readReg64 .x0 = sp + 400#64 ∧
        sm.readReg64 .x1 = sp + 864#64 ∧
        sm.readReg64 .x8 = sp + 1280#64 ∧
        sm.readReg64 .lr = (blkPl_434).base + 1596#64 ∧
        sm.readReg64 .x19 = x.ret ∧
        sm.readReg64 .x20 = sp + 320#64 ∧
        sm.readReg64 .x21 = x.ss ∧
        sm.readReg64 .x22 = x.msgA ∧
        sm.readReg64 .x23 = sp + 976#64 ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
        sm.readReg64 .x25 = sp + 400#64 ∧
        sm.readReg64 .x27 = sp + 56#64 ∧
        sm.readReg64 .x28 = sp + 1280#64 ∧
        sm.readReg64 .fp = sp + 1408#64 ∧
        sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      (P_mid := fun sm =>
        mkgAt A.repAlloc (sp + 400#64) mkg ∗
        spqrRecvKeyAt A.repAlloc (sp + 864#64) pqrKey ∗
        memRegion (sp + 1280#64) 84 ∗
        A.pool lim st sm ∗ stackAt sp tryDecryptSubStack ∗
        sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
        trAt A.repAlloc (sp + 56#64) trG tr ∗
        (if newPqrCap = 0 then emp else A.repAlloc.live newPqrPtr newPqrCap.toNat 1 ∗
          (newPqrPtr ↦ₛ newPqrState) ∗
          memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length)
            (newPqrCap.toNat - newPqrState.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 8 ∗
        ((sp + 8#64) ↦₆₄ newPqrCap) ∗
        memRegion (sp + 16#64) 12 ∗
        ((sp + 28#64) ↦₃₂ msgW) ∗
        ((sp + 32#64) ↦₆₄ x.locA) ∗
        ((sp + 40#64) ↦₆₄ newPqrPtr) ∗
        ((sp + 48#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 320#64) 80 ∗
        memRegion (sp + 440#64) 424 ∗
        memRegion (sp + 888#64) 216 ∗
        memRegion (sp + 1104#64) 176 ∗
        memRegion (sp + 1364#64) 44 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        tapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        tryDecryptSavedRegs s0.sp s0)
      ?_ ?_
    · by_vm_steps (
      wp_conv_pre =>
        simp only [sepConj_assoc]
        unfold vecU8At vecHeader
        rw [memRegion_split sp 8 8 (by decide),
          mr_cut_add sp 320 80 704 (by decide),
          mr_cut_add sp 400 8 696 (by decide),
          mr_cut_add sp 408 8 688 (by decide),
          mr_cut_add sp 416 8 680 (by decide),
          mr_cut_add sp 424 8 672 (by decide),
          mr_cut_add sp 432 8 664 (by decide),
          mr_cut_add sp 440 8 656 (by decide),
          mr_cut_add sp 448 8 648 (by decide),
          mr_cut_add sp 456 8 640 (by decide),
          mr_cut_add sp 464 8 632 (by decide),
          mr_cut_add sp 472 8 624 (by decide),
          mr_cut_add sp 480 8 616 (by decide),
          mr_cut_add sp 488 376 240 (by decide),
          mr_cut_add sp 864 8 232 (by decide),
          mr_cut_add sp 872 8 224 (by decide),
          mr_cut_add sp 880 8 216 (by decide),
          mr_cut_add sp 1116 4 160 (by decide),
          mr_cut_add sp 1120 8 152 (by decide),
          mr_cut_add sp 1128 8 144 (by decide),
          mr_cut_add sp 1136 8 136 (by decide),
          mr_cut_add sp 1144 8 128 (by decide),
          mr_cut_add sp 1152 8 120 (by decide),
          mr_cut_add sp 1160 8 112 (by decide)]
        simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
          memRegion_eight (sp + 8#64),
          memRegion_eight (sp + 400#64),
          memRegion_eight (sp + 408#64),
          memRegion_eight (sp + 416#64),
          memRegion_eight (sp + 424#64),
          memRegion_eight (sp + 432#64),
          memRegion_eight (sp + 440#64),
          memRegion_eight (sp + 448#64),
          memRegion_eight (sp + 456#64),
          memRegion_eight (sp + 464#64),
          memRegion_eight (sp + 472#64),
          memRegion_eight (sp + 480#64),
          memRegion_eight (sp + 864#64),
          memRegion_eight (sp + 872#64),
          memRegion_eight (sp + 880#64),
          memRegion_four (sp + 1116#64),
          memRegion_eight (sp + 1120#64),
          memRegion_eight (sp + 1128#64),
          memRegion_eight (sp + 1136#64),
          memRegion_eight (sp + 1144#64),
          memRegion_eight (sp + 1152#64),
          memRegion_eight (sp + 1160#64),
          CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.pointsTo64_split32 (sp + 400#64)]
      refine SepWP.focus_weaken (optKeyAt_split A.repAlloc (sp + 1304#64) pqrKey) (by sep_focus) ?_
      wp_pull_exists
      wp_focus_pure
      rintro ⟨hnp1, hnp2, hnp3⟩
      refine SepWP.focus_rw (pointsTo32_merge64 (sp + 1112#64) mkg.counter _) (by sep_focus) ?_
      wp_steps
      rw [show ((sp + 424#64) ↦₆₄ 32#64) = ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) by
        rw [hseed_len]]
      refine SepWP.focus_weaken (optKeyAt_fold A.repAlloc (sp + 864#64) _ _ _ pqrKey) (by sep_focus) ?_
      refine SepWP.focus_weaken (mkgAt_fold A.repAlloc (sp + 400#64) seedCap seedPtr _ _ mkg hseed)
        (by sep_focus) ?_
      have hm16 : memRegion (sp + 16#64) 12 = memRegion (sp + 16#64) 8 ∗ memRegion (sp + 24#64) 4 := by
        simpa using mr_cut_add sp 16 8 4 (by decide)
      have hm440 : memRegion (sp + 440#64) 424 =
          memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗ (memRegion (sp + 456#64) 8 ∗
          (memRegion (sp + 464#64) 8 ∗ (memRegion (sp + 472#64) 8 ∗ (memRegion (sp + 480#64) 8 ∗
          memRegion (sp + 488#64) 376))))) := by
        rw [mr_cut_add sp 440 8 416 (by decide),
          mr_cut_add sp 448 8 408 (by decide),
          mr_cut_add sp 456 8 400 (by decide),
          mr_cut_add sp 464 8 392 (by decide),
          mr_cut_add sp 472 8 384 (by decide),
          mr_cut_add sp 480 8 376 (by decide)]
      have hm1104 : memRegion (sp + 1104#64) 176 =
          memRegion (sp + 1104#64) 8 ∗ (memRegion (sp + 1112#64) 8 ∗ (memRegion (sp + 1120#64) 8 ∗
          (memRegion (sp + 1128#64) 8 ∗ (memRegion (sp + 1136#64) 8 ∗ (memRegion (sp + 1144#64) 8 ∗
          (memRegion (sp + 1152#64) 8 ∗ (memRegion (sp + 1160#64) 8 ∗ memRegion (sp + 1168#64) 112))))))) := by
        rw [mr_cut_add sp 1104 8 168 (by decide),
          mr_cut_add sp 1112 8 160 (by decide),
          mr_cut_add sp 1120 8 152 (by decide),
          mr_cut_add sp 1128 8 144 (by decide),
          mr_cut_add sp 1136 8 136 (by decide),
          mr_cut_add sp 1144 8 128 (by decide),
          mr_cut_add sp 1152 8 120 (by decide),
          mr_cut_add sp 1160 8 112 (by decide)]
      have hm1280 : memRegion (sp + 1280#64) 84 =
          memRegion (sp + 1280#64) 8 ∗ (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗
          (memRegion (sp + 1304#64) 8 ∗ (memRegion (sp + 1312#64) 8 ∗ (memRegion (sp + 1320#64) 8 ∗
          memRegion (sp + 1328#64) 36))))) := by
        rw [mr_cut_add sp 1280 8 76 (by decide),
          mr_cut_add sp 1288 8 68 (by decide),
          mr_cut_add sp 1296 8 60 (by decide),
          mr_cut_add sp 1304 8 52 (by decide),
          mr_cut_add sp 1312 8 44 (by decide),
          mr_cut_add sp 1320 8 36 (by decide)]
      have hm1328 : memRegion (sp + 1328#64) 80 =
          memRegion (sp + 1328#64) 36 ∗ memRegion (sp + 1364#64) 44 := by
        simpa using mr_cut_add sp 1328 36 44 (by decide)
      rw [hm16, hm440, hm1104, hm1280, hm1328]
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm hm_out
      rw [← A.pool_of_vmPreserved hvm] at hm_out
      refine ⟨⟨hnp1, hnp2, hnp3,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩, ?_⟩
      arm64_sep_close
      )
    · intro sm hpcm hrunm ⟨hcl_code, hcl_ro⟩ hReg
      rcases hReg with ⟨hnp1, hnp2, hnp3, hx0m, hx1m, hx8m, hlrm,
        hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
      rw [hstack_sub sp, show stackAt sp genStack = stackAt sm.sp genStack by rw [hspm]]
      wp_call hgen (⟨sp + 400#64, mkg, sp + 864#64, pqrKey, sp + 1280#64⟩, st)
      have hevs_gen : GenerateKeysEnv ⟨sp + 400#64, mkg, sp + 864#64, pqrKey, sp + 1280#64⟩ w := hpost
      have htrace_f : sf.trace = sm.trace := by assumption
      have hm320 : memRegion (sp + 320#64) 960 =
          memRegion (sp + 320#64) 80 ∗ (memRegion (sp + 400#64) 40 ∗
          (memRegion (sp + 440#64) 424 ∗ (memRegion (sp + 864#64) 24 ∗
          (memRegion (sp + 888#64) 216 ∗ memRegion (sp + 1104#64) 176)))) := by
        rw [mr_cut_add sp 320 80 880 (by decide),
          mr_cut_add sp 400 40 840 (by decide),
          mr_cut_add sp 440 424 416 (by decide),
          mr_cut_add sp 864 24 392 (by decide),
          mr_cut_add sp 888 216 176 (by decide)]
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_
      intro hcl_sf sf_mem
      have hsp_sf : sf.sp = sp := by simp only [wp_norm, arm64_norm, *]
      refine ⟨w, hs6Env ⟨sp + 400#64, mkg, sp + 864#64, pqrKey, sp + 1280#64⟩ w hevs_gen, ?_, ?_⟩
      · refine ⟨hsp_sf, hsp0_al',
          by simp only [State.spAligned, wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
      · unfold VerifyMacStatePlaced CryptoVerification.LibsignalTripleRatchet.Decrypt.VerifyMacStatePlaced
          segVerifyMacPC_at tryDecryptMidMetaPlaced tryDecryptCommonHeap
        rw [show (0x63c#64 : BitVec 64) = 1596#64 by rfl]
        refine ⟨by simp only [wp_norm, arm64_norm, *], ?_,
          by simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          by rw [hsp_def]; simp only [wp_norm, arm64_norm, *],
          newPqrCap, newPqrPtr, msgW, hmsgW, hnp1, hnp2, hnp3, ?_⟩
        · refine ⟨by simp only [wp_norm, arm64_norm, *],
            by rw [hsp_def]; exact hsp_sf,
            hsp0_al',
            by simp only [State.spAligned, wp_norm, arm64_norm, *],
            by change _ = s0.sp - 96#64; rw [hsp29_eq]; simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            hcl_sf,
            by simp only [wp_norm, arm64_norm, *]⟩
        · rw [hsp_def, sessionStateAt_atState, trAt_atState, RustCliAllocBudget.atState_live,
            protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
            logOff_tryDecryptPlacedImg, RustCliAllocBudget.atState_pool, hstack_sub sp,
            show BitVec.ofNat 64 tryDecryptSubStack = 260640#64 by rfl, hm320]
          rw [hspm] at sf_mem
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) sf_mem
  intro hL
  rcases hreach hL with ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, evs, hevs, _hmeta_core, hvmac⟩ | ⟨hpan_sf, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc_sf, hrun_sf, evs, hevs, hvmac⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan_sf, hoom⟩⟩

/-! ## 3. Public Relocatable Segment S6 Theorems (`159`, `549`, `159_x`, `549_x`) -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` Segment S6 (`blkPC_131` / `blkPl_131`),
parameterized by `{s6Env}` with `(hs6Env : ∀ mkg evs, GenerateKeysEnv evs → s6Env mkg evs)`
(defaulting to `s6FreeOnlyEnv`). -/
theorem deriveKeys_159_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (H : String → Option (State → State))
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    (hs6Env : ∀ (x : GenerateKeysGhost) evs, GenerateKeysEnv x evs → s6Env x.g evs)
    (hgen : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 69)
      (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F))) :
    S6SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A lim ctl s6Env :=
  deriveKeys_159_placed_ok_withStack C A lim ctl H
    (fun sp => stackAt_sub sp tryDecryptSubStack generateKeysStack) hs6Env hgen

/-- Budget-threaded relocatable `[LibsignalPlacement]` Segment S6 (`blkPC_434` / `blkPl_434`),
parameterized by `{s6Env}` with `(hs6Env : ∀ mkg evs, GenerateKeysEnv evs → s6Env mkg evs)`
(defaulting to `s6FreeOnlyEnv`). -/
theorem deriveKeys_549_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (H : String → Option (State → State))
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    (hs6Env : ∀ (x : GenerateKeysGhost) evs, GenerateKeysEnv x evs → s6Env x.g evs)
    (hgen : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 69)
      (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F))) :
    S6SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A lim ctl s6Env :=
  deriveKeys_549_placed_ok_withStack C A lim ctl H
    (fun sp => stackAt_sub sp tryDecryptSubStack generateKeysStack) hs6Env hgen

/-- `Stage2ContractsX` (`X`) budget-threaded relocatable `[LibsignalPlacement]` Segment S6
(`blkPC_131` / `blkPl_131`). -/
theorem deriveKeys_159_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (H : String → Option (State → State))
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    (hs6Env : ∀ (x : GenerateKeysGhost) evs, GenerateKeysEnv x evs → s6Env x.g evs)
    (hgen : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 69)
      (withLsCodeRoLoaded lsmpl (generateKeysSpecX M A lim C.F))) :
    S6SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A lim ctl s6Env :=
  deriveKeys_159_placed_ok_withStack C A lim ctl H
    (fun sp => stackAt_sub sp tryDecryptSubStack generateKeysStackX) hs6Env hgen

/-- `Stage2ContractsX` (`X`) budget-threaded relocatable `[LibsignalPlacement]` Segment S6
(`blkPC_434` / `blkPl_434`). -/
theorem deriveKeys_549_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (H : String → Option (State → State))
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    (hs6Env : ∀ (x : GenerateKeysGhost) evs, GenerateKeysEnv x evs → s6Env x.g evs)
    (hgen : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 69)
      (withLsCodeRoLoaded lsmpl (generateKeysSpecX M A lim C.F))) :
    S6SeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A lim ctl s6Env :=
  deriveKeys_549_placed_ok_withStack C A lim ctl H
    (fun sp => stackAt_sub sp tryDecryptSubStack generateKeysStackX) hs6Env hgen

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget
