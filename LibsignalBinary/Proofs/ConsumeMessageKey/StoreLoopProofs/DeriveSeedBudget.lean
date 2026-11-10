/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DeriveSeed
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `DeriveSeed` Sub-Segment (Block 24)

Proves `DeriveSeedPlacedSpec` and `DeriveSeedPlacedRoSpec` under `RustCliAllocBudget M` and
`SeamBudget`, ruling out `.OutOfMemory` and `x0 = 0#64` at `__rust_alloc(32, 1)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DeriveSeedBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState hmacWith keyToBytes32)
open CryptoGames.LibsignalSession (ChainKey RatchetState ReceiverChain)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
  blkPC_24 blkPl_24 libsignalRoLoaded_of_keepsFrozen lsLogFilterAddr lsmpl lsρ
)
open CryptoVerification.RustHeap (allocHookStack vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (RatchetGhost ratchetAt)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost cmkDummyImg cmkLoopFrame cmkLoopHeap cmkLoopHeap_placed
  cmkLoopHeap_placed_eq cmkLoopPC_placed cmkRustAllocSym cmkRustNoAllocShimSym
  cmkSavedRegs cmk_hook_ok_of_mem logFilterAddr logFilterAddr_cmkDummyImg
)
open CryptoVerification.LibsignalSession.StoreLoop (
  InsertKeyRegs bitvec_ofNat_lt_eq_false ci_lt_and_find_match
  cmkLoopFrame_eq_deriveSeed hmacWith_length
  keyToBytes32_length memRegion_32_eq_exists_words messageKeys_seed_eq
  pointsTo8_eq_pointsToBytes_singleton pointsToBytes_chainKeyBytes
  ratchetAt_expose_for_findIndex ratchetAt_reassemble_after_findIndex
  sepWPp_seq_lscl stackAt_7712_eq_alloc stackAt_7712_eq_find stackAt_7712_eq_hmac
  steps_of_sepWPp_placed words_entails_memRegion_32 words_entails_vecU8Buf_32
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (hmacSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks CmkEnv CmkLoopState_placed FindIndexPlacedOk
  cmkPlacedSpec cmkShimSpec findIndexPlacedSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget (
  ConcatEnv DeriveSeedPlacedRoSpec DeriveSeedPlacedSpec InsertKeyState_placed
  findIndex_placed_ok_at_state hmacAtStateSpec hmac_placed_ok_at_state hmac_placed_ro_ok_at_state
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget)

attribute [local irreducible] Program.fetch Program.externAt?

private theorem ratchetAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    ratchetAt (A.atState lim st s) = ratchetAt A.repAlloc :=
  rfl

private theorem vecU8Buf_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    vecU8Buf (A.atState lim st s) = vecU8Buf A.repAlloc :=
  rfl

private theorem deriveSeed_part1_steps [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State))
    {Inv : Memory → Prop}
    (hinv_kf : ∀ m m', Inv m → m.KeepsFrozen m' → Inv m')
    (_hinv_cl : ∀ {m}, Inv m → LibsignalCodeLoaded lsmpl m)
    (hhmac_at : ∀ {sm : State}, Inv sm.mem →
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F sm))
    (hA : CmkAllocHooks A lim H)
    (x : ConsumeMessageKeyGhost) (st : M.σ) (ckc : ChainKey) (b0 : BitVec 8)
    (R1 : SepProp) (s0 s : State)
    (hfit32 : FitsEvents M lim st (rustAllocEvents 32 1))
    (hpc' : s.pc = (blkPl_24).base + 820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (_hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx26 : s.readReg64 .x26 = x.theirA)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : s.readReg64 .x28 = ckc.index.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hL : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem)
    (hinv : Inv s.mem)
    (hm1 : s.mem ⊨
      (A.pool lim st s ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 320#64) ↦₈ b0) ∗
       memRegion (s0.sp - 224#64) 32 ∗
       stackAt s.sp 7712) ∗ R1) :
    let stA := M.stepEvents (rustAllocEvents 32 1) st
    ∃ s2, Steps ((blkPC_24).rebase (blkPl_24).base H) s s2 ∧
      s2.pc = (blkPl_24).base + 864#64 ∧
      s2.status = .Running ∧
      LibsignalCodeLoaded lsmpl s2.mem ∧
      s2.sp = s0.sp - 480#64 ∧
      s2.spAligned = true ∧
      s2.trace = s0.trace ∧
      calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧
      s2.readReg64 .x19 = 1#64 ∧
      s2.readReg64 .x21 = x.ckA ∧
      s2.readReg64 .x23 = x.self ∧
      s2.readReg64 .x26 = x.theirA ∧
      s2.readReg64 .x27 = s0.sp - 224#64 ∧
      s2.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
      s2.readReg64 .x29 = s0.sp - 96#64 ∧
      s2.readReg64 .x0 ≠ 0#64 ∧
      (s2.mem ⊨
        (A.pool lim stA s2 ∗
         A.live (s2.readReg64 .x0) 32 1 ∗
         memRegion (s2.readReg64 .x0) 32 ∗
         (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
         ((s0.sp - 320#64) ↦₈ 1#8) ∗
         ((s0.sp - 224#64) ↦ₛ hmacWith F (keyToBytes32 ckc.key) [1#8]) ∗
         stackAt s2.sp 7712) ∗ R1) := by
  dsimp only
  let stA : M.σ := M.stepEvents (rustAllocEvents 32 1) st
  have hshim : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustNoAllocShimSym) cmkShimSpec :=
    cmk_hook_ok_of_mem hA.2.2.1
  have halloc_nooom :
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustAllocSym)
        (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (cmk_hook_ok_of_mem hA.1)
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  have hmsg1_len : ([1#8] : List (BitVec 8)).length = 1 := rfl
  have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : RustLayoutOk 32 1 := ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
  have hfe32_raw : FitsEvents M lim st [.alloc 32] := by
    simpa [rustAllocEvents] using hfit32
  rcases hfe32_raw with ⟨⟨_hwma32, _henf32, _hram32, _hva32⟩, -⟩
  have hwp1 : SepWPp ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + bv% (864)) s
      (A.pool lim st s ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 320#64) ↦₈ b0) ∗
       memRegion (s0.sp - 224#64) 32 ∗
       stackAt s.sp 7712)
      (fun s2 P_f =>
        s2.sp = s0.sp - 480#64 ∧
        s2.spAligned = true ∧
        s2.trace = s0.trace ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧
        s2.readReg64 .x19 = 1#64 ∧
        s2.readReg64 .x21 = x.ckA ∧
        s2.readReg64 .x23 = x.self ∧
        s2.readReg64 .x26 = x.theirA ∧
        s2.readReg64 .x27 = s0.sp - 224#64 ∧
        s2.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x0 ≠ 0#64 ∧
        (s2.mem ⊨ P_f ∗ R1 →
          s2.mem ⊨
            (A.pool lim stA s2 ∗
             A.live (s2.readReg64 .x0) 32 1 ∗
             memRegion (s2.readReg64 .x0) 32 ∗
             (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
             ((s0.sp - 320#64) ↦₈ 1#8) ∗
             ((s0.sp - 224#64) ↦ₛ hmacWith F (keyToBytes32 ckc.key) [1#8]) ∗
             stackAt s2.sp 7712) ∗ R1))
      (fun _ _ => False) := by
    apply SepWPp.seq_frozen hinv_kf hinv (mid := lsmpl.base 73)
    wp_steps_sync_pool (lsmpl.base 73)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hinv1
    have hhmac1 := hhmac_at hinv1
    dsimp only [hmacAtStateSpec, hmacSpec, withVmPreserved,
      CryptoVerification.LibsignalSession.hmacSpec] at hhmac1
    dsimp only [cmkShimSpec, withVmPreserved,
      CryptoVerification.LibsignalSession.cmkShimSpec] at hshim
    rw [pointsTo8_eq_pointsToBytes_singleton (s0.sp - 320#64) 1#8,
        stackAt_7712_eq_hmac s.sp]
    apply SepWPp.of_sepWP_ret
    wp_call hhmac1 (s0.sp - 224#64, x.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [1#8])
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    apply SepWP.fold (Entails.of_eq (stackAt_7712_eq_hmac s.sp).symm) (by sep_focus)
    rw [stackAt_7712_eq_alloc s.sp]
    wp_steps_sync_pool (lsρ cmkRustNoAllocShimSym)
    wp_call hshim ()
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
    have hsp1 : sf_1.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
    wp_steps_sync_pool (lsρ cmkRustAllocSym)
    wp_call halloc_nooom (32, 1, st)
    have hsp2 : sf_2.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
    have htr_sf0 : sf.trace = s0.trace := (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, *])
    have htr_sf1 : sf_1.trace = s0.trace := (‹sf_1.trace = _›).trans (by simp only [wp_norm, arm64_norm, *])
    have htrace_alloc : sf_2.trace = s0.trace :=
      (‹AllocCallPreserved _ sf_2›).2.1.trans (by simp only [wp_norm, arm64_norm, *])
    have hoom' : sf_2.readReg64 Reg.x0 ≠ 0 := ‹sf_2.readReg64 .x0 ≠ 0#64›
    rw [hsp1]
    apply SepWP.fold (Entails.of_eq (stackAt_7712_eq_alloc s.sp).symm) (by sep_focus)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *],
       by simpa [State.spAligned, wp_norm, arm64_norm, hsp2, hsp] using hsp_align,
       htrace_alloc,
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       hoom',
       fun hm => ?_⟩
    simp only [hsp2, ← pointsTo8_eq_pointsToBytes_singleton] at hm ⊢
    exact Satisfies.mono (Entails.of_eq (by dsimp +zetaDelta only [stA]; sep_ac_rfl)) hm
  obtain ⟨s2, hsteps1, ⟨hpc2, hrun2, hcl2, P_f1, hmf1, hsp2, hsp2_align, htr2, hvregs2,
      hx19_2, hx21_2, hx23_2, hx26_2, hx27_2, hx28_2, hx29_2, hoom2, hm_post1⟩ | ⟨_, _, _, hqp⟩⟩ :=
    steps_of_sepWPp_placed hcl hm1 hL hwp1
  · exact ⟨s2, hsteps1, hpc2, hrun2, hcl2, hsp2, hsp2_align, htr2, hvregs2,
      hx19_2, hx21_2, hx23_2, hx26_2, hx27_2, hx28_2, hx29_2, hoom2, hm_post1 hmf1⟩
  · exact False.elim hqp

private theorem deriveSeed_part2_steps [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State))
    (hfind_ok : FindIndexPlacedOk H A)
    (x : ConsumeMessageKeyGhost) (stA : M.σ)
    (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : ChainKey) (ci : Nat) (chc : ReceiverChain)
    (R2 : SepProp) (s0 s2 : State)
    (hfind_idx : stc.findReceiverChainIndex x.their = some ci)
    (hchc : stc.receiverChains[ci]? = some chc)
    (hpc2 : s2.pc = (blkPl_24).base + 864#64)
    (hrun2 : s2.status = .Running)
    (hcl2 : LibsignalCodeLoaded lsmpl s2.mem)
    (hsp2 : s2.sp = s0.sp - 480#64)
    (hsp2_align : s2.spAligned = true)
    (htr2 : s2.trace = s0.trace)
    (hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hx19_2 : s2.readReg64 .x19 = 1#64)
    (hx21_2 : s2.readReg64 .x21 = x.ckA)
    (hx23_2 : s2.readReg64 .x23 = x.self)
    (hx26_2 : s2.readReg64 .x26 = x.theirA)
    (hx27_2 : s2.readReg64 .x27 = s0.sp - 224#64)
    (hx28_2 : s2.readReg64 .x28 = ckc.index.zeroExtend 64)
    (hx29_2 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hoom' : s2.readReg64 .x0 ≠ 0#64)
    (hL2 : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s2.mem)
    (hm2 : s2.mem ⊨
      (ratchetAt A.repAlloc x.self Gc stc ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool lim stA s2 ∗
       A.live (s2.readReg64 .x0) 32 1 ∗
       memRegion (s2.readReg64 .x0) 32 ∗
       ((s0.sp - 224#64) ↦ₛ hmacWith F (keyToBytes32 ckc.key) [1#8]) ∗
       stackAt s2.sp 7712) ∗ R2) :
    ∃ sA, Steps ((blkPC_24).rebase (blkPl_24).base H) s2 sA ∧
      sA.pc = (blkPl_24).base + bv% (916) ∧
      sA.status = .Running ∧
      LibsignalCodeLoaded lsmpl sA.mem ∧
      sA.sp = s0.sp - 480#64 ∧
      sA.spAligned = true ∧
      sA.readReg64 .x29 = s0.sp - 96#64 ∧
      (sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0) ∧
      InsertKeyRegs x Gc ckc ci (s2.readReg64 .x0) s0 sA ∧
      (sA.mem ⊨
        (ratchetAt A.repAlloc x.self Gc stc ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         A.pool lim stA sA ∗
         vecU8Buf A.repAlloc 32#64 (s2.readReg64 .x0) (ckc.messageKeys F).seed ∗
         memRegion (s0.sp - 224#64) 32 ∗
         stackAt (s0.sp - 480#64) 7712) ∗ R2) := by
  have hci_lt : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
  have hchains_pos : 0 < stc.receiverChains.length := by omega
  have hseed_eq : (ckc.messageKeys F).seed = hmacWith F (keyToBytes32 ckc.key) [1#8] :=
    messageKeys_seed_eq F ckc
  have hseed_len : (hmacWith F (keyToBytes32 ckc.key) [1#8]).length = 32 :=
    hmacWith_length F (keyToBytes32 ckc.key) [1#8]
  obtain ⟨sw0, sw1, sw2, sw3, _hseed_unpack, hseed_pts⟩ := exists_unpack64_of_length_32 hseed_len
  have hoom_beq : (s2.readReg64 Reg.x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom'
  have hwp2 : SepWPp ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + bv% (916)) s2
      (ratchetAt A.repAlloc x.self Gc stc ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool lim stA s2 ∗
       A.live (s2.readReg64 .x0) 32 1 ∗
       memRegion (s2.readReg64 .x0) 32 ∗
       ((s0.sp - 224#64) ↦ₛ hmacWith F (keyToBytes32 ckc.key) [1#8]) ∗
       stackAt s2.sp 7712)
      (fun sA P_f =>
        sA.sp = s0.sp - 480#64 ∧
        sA.spAligned = true ∧
        sA.readReg64 .x29 = s0.sp - 96#64 ∧
        (sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0) ∧
        InsertKeyRegs x Gc ckc ci (s2.readReg64 .x0) s0 sA ∧
        (sA.mem ⊨ P_f ∗ R2 →
          sA.mem ⊨
            (ratchetAt A.repAlloc x.self Gc stc ∗
             (x.theirA ↦ₛ x.their.bytes.toList) ∗
             (lsLogFilterAddr ↦₆₄ 0#64) ∗
             A.pool lim stA sA ∗
             vecU8Buf A.repAlloc 32#64 (s2.readReg64 .x0) (ckc.messageKeys F).seed ∗
             memRegion (s0.sp - 224#64) 32 ∗
             stackAt (s0.sp - 480#64) 7712) ∗ R2))
      (fun _ _ => False) := by
    apply SepWPp.fold (ratchetAt_expose_for_findIndex A.repAlloc x.self Gc stc hchains_pos) (by sep_focus)
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, hcap_ne⟩ => ?_
    have hzip_len : (Gc.chains.zip stc.receiverChains).length = stc.receiverChains.length := by
      simp [hchains_len]
    have hzip_lt : (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63 := by
      rw [hzip_len]; omega
    have hlen_lt_64 : stc.receiverChains.length < 2 ^ 64 := by omega
    have hlen_toNat : (BitVec.ofNat 64 stc.receiverChains.length).toNat = (Gc.chains.zip stc.receiverChains).length := by
      rw [hzip_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt_64]
    have ⟨_, hfind_zip⟩ := ci_lt_and_find_match hchains_len hfind_idx hchc
    rw [hseed_pts (s0.sp - 224#64),
        memRegion_32_eq_exists_words (s2.readReg64 Reg.x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro dw0
    apply SepWPp.exists_elim; intro dw1
    apply SepWPp.exists_elim; intro dw2
    apply SepWPp.exists_elim; intro dw3
    apply sepWPp_seq_lscl (mid := lsmpl.base 26) hcl2
    wp_steps_sync_pool (lsmpl.base 26)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl3
    have hfind1 := findIndex_placed_ok_at_state hfind_ok hcl3
    dsimp only [findIndexPlacedSpec, withVmPreserved,
      CryptoVerification.LibsignalSession.findIndexPlacedSpec] at hfind1
    rw [stackAt_7712_eq_find s2.sp]
    apply SepWPp.of_sepWP_ret
    wp_call hfind1 (Gc.chainsPtr, Gc.chains.zip stc.receiverChains, x.theirA, x.their)
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    have hsp3 : sf.sp = s2.sp := by simp only [wp_norm, arm64_norm, *]
    have htr_sf3 : sf.trace = s0.trace := (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, *])
    apply SepWP.fold (Entails.of_eq (stackAt_7712_eq_find s2.sp).symm) (by sep_focus)
    rw [hsp2]
    simp only [hfind_zip] at *
    have ⟨hx0_sf3, hx1_sf3⟩ : sf.readReg64 Reg.x0 = 1#64 ∧ (sf.readReg64 Reg.x1).toNat = ci := by
      assumption
    have hx1_eq : sf.readReg64 Reg.x1 = BitVec.ofNat 64 ci := by
      apply BitVec.eq_of_toNat_eq
      rw [hx1_sf3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hcs_false : (BitVec.ofNat 64 stc.receiverChains.length).ule (BitVec.ofNat 64 ci) = false :=
      bitvec_ofNat_lt_eq_false hci_lt hlen_lt_64
    wp_steps_sync_pool ((blkPl_24).base + bv% (916))
    have hreasm := ratchetAt_reassemble_after_findIndex A.repAlloc x.self Gc stc
      hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne hcap_ne
    rw [RustCliAllocBudget.repAlloc_live] at hreasm
    apply SepWP.fold hreasm (by sep_focus)
    have hvec32 := words_entails_vecU8Buf_32 A.repAlloc (s2.readReg64 (Reg.gpr 0#5))
      (ckc.messageKeys F).seed hoom' (hseed_eq ▸ hseed_len) (hseed_eq ▸ hseed_pts)
    rw [RustCliAllocBudget.repAlloc_live] at hvec32
    apply SepWP.fold hvec32 (by sep_focus)
    have hmreg32 := words_entails_memRegion_32 (s0.sp - 224#64) sw0 sw1 sw2 sw3
    have hsp_off1 : (s0.sp - 224#64) + 8#64 = s0.sp - 216#64 := by bv_arith
    have hsp_off2 : (s0.sp - 224#64) + 16#64 = s0.sp - 208#64 := by bv_arith
    have hsp_off3 : (s0.sp - 224#64) + 24#64 = s0.sp - 200#64 := by bv_arith
    rw [hsp_off1, hsp_off2, hsp_off3] at hmreg32
    apply SepWP.fold hmreg32 (by sep_focus)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *],
       by simpa [State.spAligned, wp_norm, arm64_norm, hsp3, hsp2] using hsp2_align,
       by simp only [wp_norm, arm64_norm, *],
       ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
       ?_, fun hm => ?_⟩
    · unfold InsertKeyRegs
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
    · exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  obtain ⟨sA, hsteps2, ⟨hpcA, hrunA, hclA, P_f2, hmf2, hspA, hsp_alignA, hx29A, htraceA,
      hregsA, hm_post2⟩ | ⟨_, _, _, hqp⟩⟩ :=
    steps_of_sepWPp_placed hcl2 hm2 hL2 hwp2
  · exact ⟨sA, hsteps2, hpcA, hrunA, hclA, hspA, hsp_alignA, hx29A, htraceA, hregsA, hm_post2 hmf2⟩
  · exact False.elim hqp

private theorem deriveSeed_placed_ok_of_hmac [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State))
    {Inv : Memory → Prop}
    (hinv_kf : ∀ m m', Inv m → m.KeepsFrozen m' → Inv m')
    (hinv_cl : ∀ {m}, Inv m → LibsignalCodeLoaded lsmpl m)
    (hhmac_at : ∀ {sm : State}, Inv sm.mem →
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F sm))
    (hA : CmkAllocHooks A lim H) (hfind_ok : FindIndexPlacedOk H A)
    (x : ConsumeMessageKeyGhost) (st_init st : M.σ)
    (remPost : List AllocEvent → Prop)
    (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : ChainKey) (ci : Nat) (chc : ReceiverChain)
    (R : SepProp) (s0 s : State)
    (_hlt : ckc.index < x.counter)
    (hfind_idx : stc.findReceiverChainIndex x.their = some ci)
    (hchc : stc.receiverChains[ci]? = some chc)
    (hne_post : ∃ evs, remPost evs)
    (hstate : CmkLoopState_placed A lim x st_init st
      (ConcatEnv (fun evs => evs = rustAllocEvents 32 1) remPost)
      Gc stc ckc R cmkLoopPC_placed s0 s)
    (hL : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem)
    (hinv : Inv s.mem) :
    ∃ sA, Steps ((blkPC_24).rebase (blkPl_24).base H) s sA ∧
      ((∃ stA seedPtr,
          InsertKeyState_placed F A lim x st_init stA remPost Gc stc ckc ci seedPtr R s0 sA) ∨
       (sA.status = .Panicked ∧ (sA.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 sA ∗ R))) := by
  rcases hstate with ⟨hsb, hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hcl, hvregs⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, hx19_fn, hmem⟩
  have hx19 : s.readReg64 .x19 = 1#64 := hx19_fn rfl
  clear hx19_fn
  have hseq_seed : ∀ e1 e2, (fun evs => evs = rustAllocEvents 32 1) e1 → remPost e2 →
      ConcatEnv (fun evs => evs = rustAllocEvents 32 1) remPost (e1 ++ e2) :=
    fun e1 e2 h1 h2 => ⟨e1, e2, rfl, h1, h2⟩
  have hfit32 : FitsEvents M lim st (rustAllocEvents 32 1) :=
    hsb.fitsSeg hseq_seed hne_post (rustAllocEvents 32 1) rfl
  let stA : M.σ := M.stepEvents (rustAllocEvents 32 1) st
  have hsbA : SeamBudget M lim (CmkEnv x) st_init stA remPost :=
    hsb.step hseq_seed (evs_seg := rustAllocEvents 32 1) rfl
  have hpc' : s.pc = (blkPl_24).base + 820#64 := hpc
  clear hpc
  rw [cmkLoopHeap_placed_eq] at hmem
  unfold cmkLoopHeap at hmem
  rw [ratchetAt_atState, RustCliAllocBudget.atState_pool, logFilterAddr_cmkDummyImg,
      pointsToBytes_chainKeyBytes x.ckA ckc,
      cmkLoopFrame_eq_deriveSeed s0.sp x.ret x.counter,
      ← hsp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨b0, hmem⟩
  let R_inv : SepProp :=
    ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
    memRegion x.ret 88 ∗
    memRegion (s0.sp - 480#64) 112 ∗
    ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
    memRegion (s0.sp - 360#64) 4 ∗
    ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
    memRegion (s0.sp - 352#64) 32 ∗
    memRegion (s0.sp - 319#64) 95 ∗
    memRegion (s0.sp - 192#64) 96 ∗
    cmkSavedRegs s0.sp s0 ∗ R
  let R1 : SepProp :=
    ratchetAt A.repAlloc x.self Gc stc ∗
    (x.theirA ↦ₛ x.their.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    R_inv
  have hm1 : s.mem ⊨
      (A.pool lim st s ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 320#64) ↦₈ b0) ∗
       memRegion (s0.sp - 224#64) 32 ∗
       stackAt s.sp 7712) ∗ R1 :=
    Satisfies.mono (Entails.of_eq (by dsimp +zetaDelta only [R1, R_inv]; sep_ac_rfl)) hmem
  obtain ⟨s2, hsteps1, hpc2, hrun2, hcl2, hsp2, hsp2_align, htr2, hvregs2,
      hx19_2, hx21_2, hx23_2, hx26_2, hx27_2, hx28_2, hx29_2, hoom2, hm_s2⟩ :=
    deriveSeed_part1_steps F A lim H hinv_kf hinv_cl hhmac_at hA x st ckc b0 R1 s0 s
      hfit32 hpc' hrun hsp hsp0_align hsp_align
      hx19 hx21 hx23 hx26 hx27 hx28 hx29 htrace hvregs hcl hL hinv hm1
  let R2 : SepProp := (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗ ((s0.sp - 320#64) ↦₈ 1#8) ∗ R_inv
  have hm2 : s2.mem ⊨
      (ratchetAt A.repAlloc x.self Gc stc ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool lim stA s2 ∗
       A.live (s2.readReg64 .x0) 32 1 ∗
       memRegion (s2.readReg64 .x0) 32 ∗
       ((s0.sp - 224#64) ↦ₛ hmacWith F (keyToBytes32 ckc.key) [1#8]) ∗
       stackAt s2.sp 7712) ∗ R2 :=
    Satisfies.mono (Entails.of_eq (by dsimp +zetaDelta only [stA, R1, R2]; sep_ac_rfl)) hm_s2
  have hL2 : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s2.mem := hsteps1.codeLoaded hL
  obtain ⟨sA, hsteps2, hpcA, hrunA, hclA, hspA, hsp_alignA, hx29A, htraceA, hregsA, hm_sA⟩ :=
    deriveSeed_part2_steps F A lim H hfind_ok x stA Gc stc ckc ci chc R2 s0 s2
      hfind_idx hchc hpc2 hrun2 hcl2 hsp2 hsp2_align htr2 hvregs2
      hx19_2 hx21_2 hx23_2 hx26_2 hx27_2 hx28_2 hx29_2 hoom2 hL2 hm2
  refine ⟨sA, hsteps1.trans hsteps2, Or.inl ⟨stA, s2.readReg64 .x0, hsbA, ?_⟩⟩
  refine ⟨hpcA, ⟨hrunA, hspA, hsp0_align, hsp_alignA, hx29A, htraceA.1, hclA, htraceA.2⟩,
    hregsA, hoom2, ?_⟩
  rw [cmkLoopHeap_placed_eq]
  unfold cmkLoopHeap
  rw [ratchetAt_atState, vecU8Buf_atState, RustCliAllocBudget.atState_pool, logFilterAddr_cmkDummyImg,
      pointsToBytes_chainKeyBytes x.ckA ckc,
      cmkLoopFrame_eq_deriveSeed s0.sp x.ret x.counter]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Satisfies.mono (Entails.sepExists_right 1#8 ?_) hm_sA
  exact Entails.of_eq (by dsimp +zetaDelta only [R2, R_inv]; sep_ac_rfl)

theorem deriveSeed_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State)) :
    DeriveSeedPlacedSpec F A lim H := by
  intro hA hfind_ok hhmac_ok x st_init st remPost Gc stc ckc ci chc R s0 s hlt hfind_idx hchc hne_post hstate hL
  let ⟨_, _, ⟨_, _, _, _, _, _, hcl, _⟩, _⟩ := hstate
  exact deriveSeed_placed_ok_of_hmac F A lim H
    (Inv := LibsignalCodeLoaded lsmpl)
    (fun _ _ h hkf => h.of_keepsFrozen hkf) (fun h => h)
    (fun h => hmac_placed_ok_at_state hhmac_ok h)
    hA hfind_ok x st_init st remPost Gc stc ckc ci chc R s0 s hlt hfind_idx hchc hne_post hstate hL hcl

theorem deriveSeed_placed_ro_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State)) :
    DeriveSeedPlacedRoSpec F A lim H := by
  intro hA hfind_ok hhmac_ok x st_init st remPost Gc stc ckc ci chc R s0 s hlt hfind_idx hchc hne_post hstate hL hro
  let ⟨_, _, ⟨_, _, _, _, _, _, hcl, _⟩, _⟩ := hstate
  exact deriveSeed_placed_ok_of_hmac F A lim H
    (Inv := fun m => LibsignalCodeLoaded lsmpl m ∧ LibsignalRoLoaded lsmpl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen hr hkf⟩)
    (fun h => h.1)
    (fun ⟨hc, hr⟩ => hmac_placed_ro_ok_at_state hhmac_ok hc hr)
    hA hfind_ok x st_init st remPost Gc stc ckc ci chc R s0 s hlt hfind_idx hchc hne_post hstate hL ⟨hcl, hro⟩

end LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DeriveSeedBudget
