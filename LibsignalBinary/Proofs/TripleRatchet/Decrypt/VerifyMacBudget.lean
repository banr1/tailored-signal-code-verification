/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMac
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Segment 7 (`verify_mac_with_addresses`) Proofs

Re-exports `vmacEvents`, `s7Env`, and the block `130` (`159`) theorems from `VerifyMacBudgetAux`,
and proves the block `433` (`549`) theorems (`verifyMac_true_549_placed_ok`,
`verifyMac_false_549_placed_ok`, `verifyMac_549_placed_ok`, and their `_x` `decFn` variants) over
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget

open Arm64 ProofLib
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  Crypto MessageKeys SessionState SignalProtocolError TripleRatchet
)
open CryptoVerification (
  LibsignalPlacement lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsmpl lsρ
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (
  okTagVec protocolAddressAt serializeAddresses serviceIdParse signalMessageAt
  uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TrGhost TryDecryptGhost VerifyMacWithAddressesGhost extHookStack
  sessionShimSpec verifyMacResultAt verifyMacWithAddressesStack
  verifyMacWithAddressesStackX withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_434 blkLib_eq_434 blkPl_434 speBodyAt tryDecryptCommonHeap
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt (
  Satisfies.mono_focus SepWP.setPC_ite_false SepWPp.elim_exists SepWPp.elim_exists_focus
  SepWPp.elim_memRegion1_focus SepWPp.elim_memRegion8_focus SepWPp.elim_pure
  SepWPp.elim_pure_focus SepWPp.elim_vecU8_focus SepWPp.mono_focus
  errTail_reg190_s7_split errTail_sp_s7_entails_memRegion
  errTail_sp_split layoutOk_of_cap_ne_zero lsMacFailedCoinsRoSym macFailedBytes
  macFailed_alloc_split macFailed_assemble macFailed_overlap_prep
  messageKeysAt_eq mks_parts_entails_memRegion newPqr_dealloc_prep noPanic_callee
  rodata_macFailed_549_intro rodata_macFailed_1_to_2 rodata_macFailed_2_back
  rodata_macFailed_split1 sepWPp_to_steps_or_panic stackAt_sub_split
  stackAt_vmac_split_alloc stackAt_vmac_to_ext trAt_eq_rest
  verifyMacResultAt_parts_entails_memRegion verifyMac_scr_split
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt.AuthDecryptFacts (
  spAligned_of_sp_eq
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget SeqEnv
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  rustCliDeallocBudgetSpec rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomSpecWithStack
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (
  hooksException sepWP_seg_ls_vm
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustAllocSpecWithStack rustDeallocExternSpecWithStack withStack
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (
  macLsLogOff verifyMacWithAddressesPlacedSpec
  verifyMacWithAddressesPlacedSpecWithStack verifyMacWithAddressesPlacedSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  AesDecryptStatePlaced ErrTailStatePlaced S7SeamPlaced S7SeamXPlaced
  VerifyMacStatePlaced tryDecryptFnOnPanic tryDecryptOnPanic
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget (
  SepWPp.call_cro_frame_placed SepWPp.call_frame_placed SepWPp.of_sepWP_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux (
  SepWPp.drop_focus logOff_eq_macLsLogOff protocolAddressAt_atState
  sessionStateAt_atState setPC_setMem_ite_false signalMessageAt_atState speBodyAt_atState
  subroutine_ok_allocNoOomWithStack_of_budgetWithStack trAt_atState
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

private theorem sepWP_seg_433 [LibsignalPlacement] {H : String → Option (State → State)}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_434).rebase (blkPl_434).base (hooksException H)) mid (s.setMem m_strip) Pre
        (fun sm' Pm => ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
          SepWP ((blkPC_434).rebase (blkPl_434).base H) target (sm'.setMem m_real) Pm post oom)) :
    SepWP ((blkPC_434).rebase (blkPl_434).base H) target s Pre post oom :=
  sepWP_seg_ls_vm (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H)) blkLib_eq_434 (by rfl) hseg

local macro "wp_sync_433 " mid:term : tactic =>
  `(tactic| (
    apply sepWP_seg_433 (mid := $mid); intro _m_strip; wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm])) (hnext := ?_)))

/-! ## 1. Re-Exports from `VerifyMacBudgetAux` (Envelope & Block `130` / `159` Proofs) -/

abbrev vmacEvents := VerifyMacBudgetAux.vmacEvents
abbrev s7Env := VerifyMacBudgetAux.s7Env
abbrev freeOnlyEvs_rustDeallocEvents := VerifyMacBudgetAux.freeOnlyEvs_rustDeallocEvents

abbrev verifyMac_true_159_placed_ok := @VerifyMacBudgetAux.verifyMac_true_159_placed_ok
abbrev verifyMac_false_159_placed_ok := @VerifyMacBudgetAux.verifyMac_false_159_placed_ok
abbrev verifyMac_159_placed_ok := @VerifyMacBudgetAux.verifyMac_159_placed_ok
abbrev verifyMac_true_159_placed_ok_x := @VerifyMacBudgetAux.verifyMac_true_159_placed_ok_x
abbrev verifyMac_false_159_placed_ok_x := @VerifyMacBudgetAux.verifyMac_false_159_placed_ok_x
abbrev verifyMac_159_placed_ok_x := @VerifyMacBudgetAux.verifyMac_159_placed_ok_x

/-! ## 2. Block `433` (`549`) Segment-7 Proofs (`S7SeamPlaced` & `S7SeamXPlaced`) -/

theorem verifyMac_true_549_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec M A lim C.F uuidTryParse)))
    (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hfits : FitsEnv M lim st (s7Env C.F uuidTryParse x tr mks newPqrState))
    (hok : x.msg.verifyMacWithAddresses C.F
      (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true)
    (h7 : VerifyMacStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      ((∃ evs, s7Env C.F uuidTryParse x tr mks newPqrState evs ∧
          AesDecryptStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
            x trG tr st1 mks newPqrState draws R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R))) := by
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold tryDecryptCommonHeap at hmem
  rw [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState, protocolAddressAt_atState,
      signalMessageAt_atState, logOff_eq_macLsLogOff, A.atState_live_eq_repAlloc, A.atState_pool] at hmem
  rw [trAt_eq_rest A.repAlloc s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)] at hmem
  change s.pc = (blkPl_434).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + bv% (1656)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_sync_433 (lsmpl.base 62)
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  let vmacGhost : VerifyMacWithAddressesGhost :=
    ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
     s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
     s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩
  refine SepWPp.call_cro_frame_placed
    (spec := verifyMacWithAddressesPlacedSpec M A lim C.F uuidTryParse)
    (x := (vmacGhost, st))
    (T := signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          macLsLogOff ∗
          A.pool lim st _ ∗
          stackAt (s0.sp - 1504#64) verifyMacWithAddressesStack)
    (ret_pc := (blkPl_434).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack, vmacGhost]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                hfits.seq_left.seq_left⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by
      dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack] at h
      rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack] at hm_pan
      exact noPanic_callee hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack, vmacGhost]
  change SepWPp _ _ _
    ((⌜s1.trace = _⌝ ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      protocolAddressAt A.repAlloc x.loc x.locA ∗
      ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
      ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
      ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
      verifyMacResultAt (s0.sp - 1104#64)
        (x.msg.verifyMacWithAddresses C.F
          (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey) ∗
      macLsLogOff ∗
      A.pool lim (M.stepEvents (vmacEvents C.F uuidTryParse x tr mks) st) s1 ∗
      stackAt _ verifyMacWithAddressesStack) ∗ _) _ _
  rw [hok]
  unfold verifyMacResultAt
  simp only [↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_434).base + bv% (1656))
  wp_sync_433 ((blkPl_434).base + bv% (1656))
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rfl) (by exact hrun1)
  intro _ _ hmf
  refine ⟨vmacEvents C.F uuidTryParse x tr mks, SeqEnv.inl (SeqEnv.inl rfl),
    by rfl, ⟨hrun1, hsp1, hsp0,
      spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1,
      ?_, htr1, hcl2, by simp only [wp_norm, hvregs_1]⟩,
    by simp only [wp_norm, hx19_1],
    by simp only [wp_norm, hx20_1],
    by simp only [wp_norm, hx21_1],
    by simp only [wp_norm, hx22_1],
    by simp only [wp_norm],
    by simp only [wp_norm, hx24_1],
    by simp only [wp_norm, hx25_1],
    by simp only [wp_norm, hx27_1],
    by simp only [wp_norm, hx28_1],
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
  · simp only [wp_norm, hx29_1]
  · unfold tryDecryptCommonHeap
    rw [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState, protocolAddressAt_atState,
        signalMessageAt_atState, logOff_eq_macLsLogOff, A.atState_live_eq_repAlloc, A.atState_pool]
    rw [trAt_eq_rest A.repAlloc s0.sp trG tr,
        messageKeysAt_eq (s0.sp - 1504#64) mks,
        verifyMac_scr_split (s0.sp - 1504#64),
        stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)]
    have hmf1 := Satisfies.mono_focus
      (verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 1#8) (by sep_focus) hmf
    clear hmf
    simp only [wp_norm, sepConj_assoc] at hmf1 ⊢
    sep_close

set_option maxHeartbeats 800000 in
theorem verifyMac_false_549_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec M A lim C.F uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hfits : FitsEnv M lim st (s7Env C.F uuidTryParse x tr mks newPqrState))
    (hok : x.msg.verifyMacWithAddresses C.F
      (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : VerifyMacStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      ((∃ evs, s7Env C.F uuidTryParse x tr mks newPqrState evs ∧
          ErrTailStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
            x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R))) := by
  have halloc_nooom := subroutine_ok_allocNoOom_of_budget halloc
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold tryDecryptCommonHeap at hmem
  rw [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState, protocolAddressAt_atState,
      signalMessageAt_atState, logOff_eq_macLsLogOff, A.atState_live_eq_repAlloc, A.atState_pool] at hmem
  rw [trAt_eq_rest A.repAlloc s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)] at hmem
  change s.pc = (blkPl_434).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + bv% (780)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_sync_433 (lsmpl.base 62)
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  let vmacGhost : VerifyMacWithAddressesGhost :=
    ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
     s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
     s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩
  let vmacEvs := vmacEvents C.F uuidTryParse x tr mks
  refine SepWPp.call_cro_frame_placed
    (spec := verifyMacWithAddressesPlacedSpec M A lim C.F uuidTryParse)
    (x := (vmacGhost, st))
    (T := signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          macLsLogOff ∗
          A.pool lim st _ ∗
          stackAt (s0.sp - 1504#64) verifyMacWithAddressesStack)
    (ret_pc := (blkPl_434).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack, vmacGhost]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                hfits.seq_left.seq_left⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by
      dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack] at h
      rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack] at hm_pan
      exact noPanic_callee hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesPlacedSpec, verifyMacWithAddressesPlacedSpecWithStack, vmacGhost]
  change SepWPp _ _ _
    ((⌜s1.trace = _⌝ ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      protocolAddressAt A.repAlloc x.loc x.locA ∗
      ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
      ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
      ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
      verifyMacResultAt (s0.sp - 1104#64)
        (x.msg.verifyMacWithAddresses C.F
          (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey) ∗
      macLsLogOff ∗
      A.pool lim (M.stepEvents vmacEvs st) s1 ∗
      stackAt _ verifyMacWithAddressesStack) ∗ _) _ _
  rw [hok]
  unfold verifyMacResultAt
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  rw [stackAt_vmac_split_alloc (s0.sp - 1504#64)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsRustNoAllocShimSym)
  wp_sync_433 (lsρ lsRustNoAllocShimSym)
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.call_frame_placed (spec := sessionShimBudgetSpec) (x := ())
    (T := emp) (ret_pc := (blkPl_434).base + bv% (2328))
    hcl2 hshim (by rfl) (by exact hrun1)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [sessionShimBudgetSpec, sessionShimSpec]; rw [pure_sepConj]; simp)
    trivial
    (by rw [emp_sepConj])
    (fun _ _ _ _ h => by dsimp only [sessionShimBudgetSpec, sessionShimSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ _ hm_pan => by dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
  dsimp only [sessionShimBudgetSpec, sessionShimSpec]
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hvm2
  apply SepWPp.elim_pure; intro htr2
  simp only [wp_norm, htr1] at htr2
  refine SepWPp.transport_budgetPool hvm2 (hnext := ?_)
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsRustAllocSym)
  wp_sync_433 (lsρ lsRustAllocSym)
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  have hfit_alloc : FitsEvents M lim (M.stepEvents vmacEvs st) (rustAllocEvents 23 1) :=
    FitsEnv.eq_iff.mp (hfits.seq_left.seq_right rfl)
  refine SepWPp.call_frame_placed (spec := rustCliAllocNoOomSpec M A lim false)
    (x := (23, 1, M.stepEvents vmacEvs st))
    (T := A.pool lim (M.stepEvents vmacEvs st) _ ∗
          stackAt (s0.sp - 1504#64) allocHookStack)
    (ret_pc := (blkPl_434).base + bv% (2340))
    hcl3 halloc_nooom (by rfl) (by exact hrun2)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [rustCliAllocNoOomSpec]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩, hfit_alloc, by simp (config := { decide := true }) only [wp_norm, arm64_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [rustCliAllocNoOomSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ _ hm_pan => by dsimp only [rustCliAllocNoOomSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
  dsimp only [rustCliAllocNoOomSpec]
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp2, sepConj_assoc]
  apply SepWPp.elim_pure; rintro ⟨hacp3, hp, _⟩
  have htr3 : s3.trace = s0.trace := hacp3.2.1.trans (by simp only [wp_norm, htr2])
  rw [← M.stepEvents_append vmacEvs (rustAllocEvents 23 1) st]
  set p := s3.readReg64 .x0
  have hmf_ent := verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 0#8
  refine SepWPp.mono_focus hmf_ent (by sep_focus) ?_
  rw [macFailed_alloc_split p]
  refine SepWPp.elim_memRegion8_focus (a := p) (by sep_focus) fun pw0 => ?_
  refine SepWPp.elim_memRegion8_focus (a := p + 8#64) (by sep_focus) fun pw1 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun sw0 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun sw1 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun sw2 => ?_
  refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun sb0 => ?_
  intro R' hm3
  have hm3_ro := rodata_macFailed_549_intro hcl3.2 hm3
  clear hm3
  rw [rodata_macFailed_split1, ← sepConj_assoc] at hm3_ro
  revert R' hm3_ro
  change SepWPp _ _ _ _ _ _
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_434).base + bv% (2360))
  apply sepWP_seg_433 (mid := (blkPl_434).base + bv% (2360))
  intro _m_strip
  wp_steps
  apply setPC_setMem_ite_false (by rw [beq_eq_false_iff_ne]; exact hp)
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by wp_norm_lhs)) (hnext := ?_)
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hcl3b
  simp only [sepConj_assoc]
  rw [rodata_macFailed_1_to_2]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl3b (mid := (blkPl_434).base + bv% (2380))
  wp_sync_433 ((blkPl_434).base + bv% (2380))
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hcl4
  simp only [sepConj_assoc]
  rw [rodata_macFailed_2_back]
  refine SepWPp.drop_focus (Drop := lsρ lsMacFailedCoinsRoSym ↦ᵣ macFailedBytes) (by sep_focus) ?_
  refine SepWPp.mono_focus (macFailed_overlap_prep p) (by sep_focus) ?_
  refine SepWPp.elim_memRegion8_focus (a := p + 15#64) (by sep_focus) fun pw2 => ?_
  simp only [← sepConj_assoc]
  by_cases hpqr_cap : newPqrCap = 0#64
  · simp only [sepConj_assoc]
    refine SepWPp.mono_focus
      (show (if newPqrCap = 0 then emp else A.repAlloc.live newPqrPtr newPqrCap.toNat 1 ∗
        (newPqrPtr ↦ₛ newPqrState) ∗
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ⊢ emp by
        simp only [hpqr_cap]; exact Entails.refl _) (by sep_focus) ?_
    simp only [emp_sepConj, ← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_434).base + bv% (780))
    wp_sync_433 ((blkPl_434).base + bv% (780))
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl5
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rfl) (by exact hrun3)
    intro _ _ hmf
    refine ⟨vmacEvs ++ rustAllocEvents 23 1, SeqEnv.inl (SeqEnv.append rfl rfl),
      by rfl, ⟨hrun3, hsp3, hsp0,
        spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3,
        ?_, htr3, hcl5, by simp only [wp_norm, hvregs_3]⟩,
      by simp only [wp_norm, hx19_3],
      by simp only [wp_norm, hx20_3],
      by simp only [wp_norm]; rfl, ?_⟩
    · simp only [wp_norm, hx29_3]
    · unfold tryDecryptCommonHeap
      rw [sessionStateAt_atState, trAt_atState, speBodyAt_atState, protocolAddressAt_atState,
          protocolAddressAt_atState, signalMessageAt_atState, logOff_eq_macLsLogOff, A.atState_pool]
      unfold speBodyAt
      rw [trAt_eq_rest A.repAlloc s0.sp trG tr,
          stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide),
          stackAt_vmac_split_alloc (s0.sp - 1504#64),
          errTail_sp_split s0.sp,
          errTail_reg190_s7_split s0.sp]
      rw [← A.repAlloc_live_norm] at hmf
      have hmf1 := Satisfies.mono_focus (macFailed_assemble A.repAlloc s0.sp p hp) (by sep_focus) hmf
      have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
      sep_close
  · simp only [sepConj_assoc]
    refine SepWPp.mono_focus
      (newPqr_dealloc_prep A.repAlloc newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt)
      (by sep_focus) ?_
    rw [A.repAlloc_live_norm]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl4 (mid := lsρ lsRustDeallocSym)
    wp_sync_433 (lsρ lsRustDeallocSym)
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl5
    refine SepWPp.call_frame_placed (spec := rustCliDeallocBudgetSpec M A lim)
      (x := (newPqrPtr, newPqrCap.toNat, 1, M.stepEvents (vmacEvs ++ rustAllocEvents 23 1) st))
      (T := A.pool lim (M.stepEvents (vmacEvs ++ rustAllocEvents 23 1) st) _ ∗
            A.live newPqrPtr newPqrCap.toNat 1 ∗
            memRegion newPqrPtr newPqrCap.toNat ∗
            stackAt (s0.sp - 1504#64) allocHookStack)
      (ret_pc := (blkPl_434).base + bv% (2520))
      hcl5 hdealloc (by rfl) (by exact hrun3)
      (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
      (by dsimp only [rustCliDeallocBudgetSpec]; simp only [wp_norm, hsp3]; rfl)
      (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm], by simp (config := { decide := true }) only [wp_norm, arm64_norm]⟩)
      (by sep_focus)
      (fun _ _ _ _ h => by dsimp only [rustCliDeallocBudgetSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun _ _ _ hm_pan => by dsimp only [rustCliDeallocBudgetSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hcl5
    intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl5
    simp only [wp_norm, hsp3] at hsp4
    rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
    simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
    dsimp only [rustCliDeallocBudgetSpec]
    simp only [wp_norm, hsp3, sepConj_assoc]
    apply SepWPp.elim_pure; rintro ⟨hacp4, _⟩
    have htr4 : s4.trace = s0.trace := hacp4.2.1.trans (by simp only [wp_norm, htr3])
    rw [← M.stepEvents_append (vmacEvs ++ rustAllocEvents 23 1) (rustDeallocEvents newPqrCap.toNat 1) st]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl5 (mid := (blkPl_434).base + bv% (780))
    wp_sync_433 ((blkPl_434).base + bv% (780))
    apply SepWP.done (by rfl) (by exact hrun4)
    intro hcl6
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rfl) (by exact hrun4)
    intro _ _ hmf
    refine ⟨(vmacEvs ++ rustAllocEvents 23 1) ++ rustDeallocEvents newPqrCap.toNat 1,
      SeqEnv.append (SeqEnv.append rfl rfl) (freeOnlyEvs_rustDeallocEvents newPqrCap.toNat 1),
      by rfl, ⟨hrun4, hsp4, hsp0,
        spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4,
        ?_, htr4, hcl6, by simp only [wp_norm, hvregs_4]⟩,
      by simp only [wp_norm, hx19_4],
      by simp only [wp_norm, hx20_4],
      by simp only [wp_norm, hx26_4]; rfl, ?_⟩
    · simp only [wp_norm, hx29_4]
    · unfold tryDecryptCommonHeap
      rw [sessionStateAt_atState, trAt_atState, speBodyAt_atState, protocolAddressAt_atState,
          protocolAddressAt_atState, signalMessageAt_atState, logOff_eq_macLsLogOff, A.atState_pool]
      unfold speBodyAt
      rw [trAt_eq_rest A.repAlloc s0.sp trG tr,
          stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide),
          stackAt_vmac_split_alloc (s0.sp - 1504#64),
          errTail_sp_split s0.sp,
          errTail_reg190_s7_split s0.sp]
      rw [← A.repAlloc_live_norm] at hmf
      have hmf1 := Satisfies.mono_focus (macFailed_assemble A.repAlloc s0.sp p hp) (by sep_focus) hmf
      have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
      sep_close

theorem verifyMac_549_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec M A lim C.F uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    S7SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S (s7Env C.F uuidTryParse) := by
  intro x st trG tr st1 mks newPqrState draws R s0 s hfits h7 hL
  by_cases hok : x.msg.verifyMacWithAddresses C.F
      (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true
  · simp only [hok, ↓reduceIte]
    exact verifyMac_true_549_placed_ok C A lim ctl S H hVMac
      x st trG tr st1 mks newPqrState draws R s0 s hfits hok h7 hL
  · have hok_false : x.msg.verifyMacWithAddresses C.F
        (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false :=
      Bool.eq_false_iff.mpr hok
    simp only [hok_false, Bool.false_eq_true, ↓reduceIte]
    exact verifyMac_false_549_placed_ok C A lim ctl S H hVMac hshim halloc hdealloc
      x st trG tr st1 mks newPqrState draws R s0 s hfits hok_false h7 hL

theorem verifyMac_true_549_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpecX M A lim C.F uuidTryParse)))
    (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hfits : FitsEnv M lim st (s7Env C.F uuidTryParse x tr mks newPqrState))
    (hok : x.msg.verifyMacWithAddresses C.F
      (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true)
    (h7 : VerifyMacStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      ((∃ evs, s7Env C.F uuidTryParse x tr mks newPqrState evs ∧
          AesDecryptStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
            x trG tr st1 mks newPqrState draws R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ tryDecryptFnOnPanic C decFn uuidTryParse S x s0 s' ∗ R))) := by
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold tryDecryptCommonHeap at hmem
  rw [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState, protocolAddressAt_atState,
      signalMessageAt_atState, logOff_eq_macLsLogOff, A.atState_live_eq_repAlloc, A.atState_pool] at hmem
  rw [trAt_eq_rest A.repAlloc s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStackX (by decide)] at hmem
  change s.pc = (blkPl_434).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + bv% (1656)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_sync_433 (lsmpl.base 62)
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  let vmacGhost : VerifyMacWithAddressesGhost :=
    ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
     s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
     s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩
  refine SepWPp.call_cro_frame_placed
    (spec := verifyMacWithAddressesPlacedSpecX M A lim C.F uuidTryParse)
    (x := (vmacGhost, st))
    (T := signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          macLsLogOff ∗
          A.pool lim st _ ∗
          stackAt (s0.sp - 1504#64) verifyMacWithAddressesStackX)
    (ret_pc := (blkPl_434).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesPlacedSpecX, verifyMacWithAddressesPlacedSpecWithStack, vmacGhost]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                hfits.seq_left.seq_left⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by
      dsimp only [verifyMacWithAddressesPlacedSpecX, verifyMacWithAddressesPlacedSpecWithStack] at h
      rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesPlacedSpecX, verifyMacWithAddressesPlacedSpecWithStack] at hm_pan
      exact noPanic_callee hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesPlacedSpecX, verifyMacWithAddressesPlacedSpecWithStack, vmacGhost]
  change SepWPp _ _ _
    ((⌜s1.trace = _⌝ ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      protocolAddressAt A.repAlloc x.loc x.locA ∗
      ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
      ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
      ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
      verifyMacResultAt (s0.sp - 1104#64)
        (x.msg.verifyMacWithAddresses C.F
          (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey) ∗
      macLsLogOff ∗
      A.pool lim (M.stepEvents (vmacEvents C.F uuidTryParse x tr mks) st) s1 ∗
      stackAt _ verifyMacWithAddressesStackX) ∗ _) _ _
  rw [hok]
  unfold verifyMacResultAt
  simp only [↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_434).base + bv% (1656))
  wp_sync_433 ((blkPl_434).base + bv% (1656))
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rfl) (by exact hrun1)
  intro _ _ hmf
  refine ⟨vmacEvents C.F uuidTryParse x tr mks, SeqEnv.inl (SeqEnv.inl rfl),
    by rfl, ⟨hrun1, hsp1, hsp0,
      spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1,
      ?_, htr1, hcl2, by simp only [wp_norm, hvregs_1]⟩,
    by simp only [wp_norm, hx19_1],
    by simp only [wp_norm, hx20_1],
    by simp only [wp_norm, hx21_1],
    by simp only [wp_norm, hx22_1],
    by simp only [wp_norm],
    by simp only [wp_norm, hx24_1],
    by simp only [wp_norm, hx25_1],
    by simp only [wp_norm, hx27_1],
    by simp only [wp_norm, hx28_1],
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
  · simp only [wp_norm, hx29_1]
  · unfold tryDecryptCommonHeap
    rw [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState, protocolAddressAt_atState,
        signalMessageAt_atState, logOff_eq_macLsLogOff, A.atState_live_eq_repAlloc, A.atState_pool]
    rw [trAt_eq_rest A.repAlloc s0.sp trG tr,
        messageKeysAt_eq (s0.sp - 1504#64) mks,
        verifyMac_scr_split (s0.sp - 1504#64),
        stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStackX (by decide)]
    have hmf1 := Satisfies.mono_focus
      (verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 1#8) (by sep_focus) hmf
    clear hmf
    simp only [wp_norm, sepConj_assoc] at hmf1 ⊢
    sep_close

set_option maxHeartbeats 800000 in
theorem verifyMac_false_549_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpecX M A lim C.F uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustNoAllocShimSym) (withStack sessionShimBudgetSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustAllocSym) (rustAllocSpecWithStack M A lim false extHookStack))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack M A lim extHookStack))
    (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hfits : FitsEnv M lim st (s7Env C.F uuidTryParse x tr mks newPqrState))
    (hok : x.msg.verifyMacWithAddresses C.F
      (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : VerifyMacStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      ((∃ evs, s7Env C.F uuidTryParse x tr mks newPqrState evs ∧
          ErrTailStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
            x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ tryDecryptFnOnPanic C decFn uuidTryParse S x s0 s' ∗ R))) := by
  have halloc_nooom := subroutine_ok_allocNoOomWithStack_of_budgetWithStack halloc
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold tryDecryptCommonHeap at hmem
  rw [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState, protocolAddressAt_atState,
      signalMessageAt_atState, logOff_eq_macLsLogOff, A.atState_live_eq_repAlloc, A.atState_pool] at hmem
  rw [trAt_eq_rest A.repAlloc s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStackX (by decide)] at hmem
  change s.pc = (blkPl_434).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + bv% (780)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_sync_433 (lsmpl.base 62)
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  let vmacGhost : VerifyMacWithAddressesGhost :=
    ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
     s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
     s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩
  let vmacEvs := vmacEvents C.F uuidTryParse x tr mks
  refine SepWPp.call_cro_frame_placed
    (spec := verifyMacWithAddressesPlacedSpecX M A lim C.F uuidTryParse)
    (x := (vmacGhost, st))
    (T := signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          macLsLogOff ∗
          A.pool lim st _ ∗
          stackAt (s0.sp - 1504#64) verifyMacWithAddressesStackX)
    (ret_pc := (blkPl_434).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesPlacedSpecX, verifyMacWithAddressesPlacedSpecWithStack, vmacGhost]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                hfits.seq_left.seq_left⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by
      dsimp only [verifyMacWithAddressesPlacedSpecX, verifyMacWithAddressesPlacedSpecWithStack] at h
      rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesPlacedSpecX, verifyMacWithAddressesPlacedSpecWithStack] at hm_pan
      exact noPanic_callee hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesPlacedSpecX, verifyMacWithAddressesPlacedSpecWithStack, vmacGhost]
  change SepWPp _ _ _
    ((⌜s1.trace = _⌝ ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      protocolAddressAt A.repAlloc x.loc x.locA ∗
      ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
      ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
      ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
      verifyMacResultAt (s0.sp - 1104#64)
        (x.msg.verifyMacWithAddresses C.F
          (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey) ∗
      macLsLogOff ∗
      A.pool lim (M.stepEvents vmacEvs st) s1 ∗
      stackAt _ verifyMacWithAddressesStackX) ∗ _) _ _
  rw [hok]
  unfold verifyMacResultAt
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  refine SepWPp.mono_focus (stackAt_vmac_to_ext (s0.sp - 1504#64)) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsRustNoAllocShimSym)
  wp_sync_433 (lsρ lsRustNoAllocShimSym)
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.call_frame_placed (spec := withStack sessionShimBudgetSpec extHookStack) (x := ())
    (T := stackAt (s0.sp - 1504#64) extHookStack) (ret_pc := (blkPl_434).base + bv% (2328))
    hcl2 hshim (by rfl) (by exact hrun1)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack, sessionShimBudgetSpec, sessionShimSpec]; simp only [wp_norm, hsp1, pure_sepConj, true_and, emp_sepConj])
    trivial
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack, sessionShimBudgetSpec, sessionShimSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ _ hm_pan => by dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack, sessionShimBudgetSpec, sessionShimSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
  dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack, sessionShimBudgetSpec, sessionShimSpec]
  simp only [wp_norm, hsp1, sepConj_assoc]
  apply SepWPp.elim_pure; intro hvm2
  apply SepWPp.elim_pure; intro htr2
  simp only [htr1] at htr2
  refine SepWPp.transport_budgetPool hvm2 (hnext := ?_)
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsRustAllocSym)
  wp_sync_433 (lsρ lsRustAllocSym)
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  have hfit_alloc : FitsEvents M lim (M.stepEvents vmacEvs st) (rustAllocEvents 23 1) :=
    FitsEnv.eq_iff.mp (hfits.seq_left.seq_right rfl)
  refine SepWPp.call_frame_placed
    (spec := rustCliAllocNoOomSpecWithStack M A lim false extHookStack)
    (x := (23, 1, M.stepEvents vmacEvs st))
    (T := A.pool lim (M.stepEvents vmacEvs st) _ ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_434).base + bv% (2340))
    hcl3 halloc_nooom (by rfl) (by exact hrun2)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [rustCliAllocNoOomSpecWithStack]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩, hfit_alloc, by simp (config := { decide := true }) only [wp_norm, arm64_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [rustCliAllocNoOomSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ _ hm_pan => by dsimp only [rustCliAllocNoOomSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
  dsimp only [rustCliAllocNoOomSpecWithStack]
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp2, sepConj_assoc]
  apply SepWPp.elim_pure; rintro ⟨hacp3, hp, _⟩
  have htr3 : s3.trace = s0.trace := hacp3.2.1.trans (by simp only [wp_norm, htr2])
  rw [← M.stepEvents_append vmacEvs (rustAllocEvents 23 1) st]
  set p := s3.readReg64 .x0
  have hmf_ent := verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 0#8
  refine SepWPp.mono_focus hmf_ent (by sep_focus) ?_
  rw [macFailed_alloc_split p]
  refine SepWPp.elim_memRegion8_focus (a := p) (by sep_focus) fun pw0 => ?_
  refine SepWPp.elim_memRegion8_focus (a := p + 8#64) (by sep_focus) fun pw1 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun sw0 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun sw1 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun sw2 => ?_
  refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun sb0 => ?_
  intro R' hm3
  have hm3_ro := rodata_macFailed_549_intro hcl3.2 hm3
  clear hm3
  rw [rodata_macFailed_split1, ← sepConj_assoc] at hm3_ro
  revert R' hm3_ro
  change SepWPp _ _ _ _ _ _
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_434).base + bv% (2360))
  apply sepWP_seg_433 (mid := (blkPl_434).base + bv% (2360))
  intro _m_strip
  wp_steps
  apply setPC_setMem_ite_false (by rw [beq_eq_false_iff_ne]; exact hp)
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by wp_norm_lhs)) (hnext := ?_)
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hcl3b
  simp only [sepConj_assoc]
  rw [rodata_macFailed_1_to_2]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl3b (mid := (blkPl_434).base + bv% (2380))
  wp_sync_433 ((blkPl_434).base + bv% (2380))
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hcl4
  simp only [sepConj_assoc]
  rw [rodata_macFailed_2_back]
  refine SepWPp.drop_focus (Drop := lsρ lsMacFailedCoinsRoSym ↦ᵣ macFailedBytes) (by sep_focus) ?_
  refine SepWPp.mono_focus (macFailed_overlap_prep p) (by sep_focus) ?_
  refine SepWPp.elim_memRegion8_focus (a := p + 15#64) (by sep_focus) fun pw2 => ?_
  simp only [← sepConj_assoc]
  by_cases hpqr_cap : newPqrCap = 0#64
  · simp only [sepConj_assoc]
    refine SepWPp.mono_focus
      (show (if newPqrCap = 0 then emp else A.repAlloc.live newPqrPtr newPqrCap.toNat 1 ∗
        (newPqrPtr ↦ₛ newPqrState) ∗
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ⊢ emp by
        simp only [hpqr_cap]; exact Entails.refl _) (by sep_focus) ?_
    simp only [emp_sepConj, ← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_434).base + bv% (780))
    wp_sync_433 ((blkPl_434).base + bv% (780))
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl5
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rfl) (by exact hrun3)
    intro _ _ hmf
    refine ⟨vmacEvs ++ rustAllocEvents 23 1, SeqEnv.inl (SeqEnv.append rfl rfl),
      by rfl, ⟨hrun3, hsp3, hsp0,
        spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3,
        ?_, htr3, hcl5, by simp only [wp_norm, hvregs_3]⟩,
      by simp only [wp_norm, hx19_3],
      by simp only [wp_norm, hx20_3],
      by simp only [wp_norm]; rfl, ?_⟩
    · simp only [wp_norm, hx29_3]
    · unfold tryDecryptCommonHeap
      rw [sessionStateAt_atState, trAt_atState, speBodyAt_atState, protocolAddressAt_atState,
          protocolAddressAt_atState, signalMessageAt_atState, logOff_eq_macLsLogOff, A.atState_pool]
      unfold speBodyAt
      rw [trAt_eq_rest A.repAlloc s0.sp trG tr,
          stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
          errTail_sp_split s0.sp,
          errTail_reg190_s7_split s0.sp]
      rw [← A.repAlloc_live_norm] at hmf
      have hmf1 := Satisfies.mono_focus (macFailed_assemble A.repAlloc s0.sp p hp) (by sep_focus) hmf
      have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
      sep_close
  · simp only [sepConj_assoc]
    refine SepWPp.mono_focus
      (newPqr_dealloc_prep A.repAlloc newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt)
      (by sep_focus) ?_
    rw [A.repAlloc_live_norm]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl4 (mid := lsρ lsRustDeallocSym)
    wp_sync_433 (lsρ lsRustDeallocSym)
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl5
    refine SepWPp.call_frame_placed
      (spec := rustDeallocExternSpecWithStack M A lim extHookStack)
      (x := (newPqrPtr, newPqrCap.toNat, 1, M.stepEvents (vmacEvs ++ rustAllocEvents 23 1) st))
      (T := A.pool lim (M.stepEvents (vmacEvs ++ rustAllocEvents 23 1) st) _ ∗
            A.live newPqrPtr newPqrCap.toNat 1 ∗
            memRegion newPqrPtr newPqrCap.toNat ∗
            stackAt (s0.sp - 1504#64) extHookStack)
      (ret_pc := (blkPl_434).base + bv% (2520))
      hcl5 hdealloc (by rfl) (by exact hrun3)
      (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
      (by dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]; simp only [wp_norm, hsp3]; rfl)
      (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                  ⟨layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt, by decide⟩,
                  by simp (config := { decide := true }) only [wp_norm, arm64_norm]⟩)
      (by sep_focus)
      (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun _ _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hcl5
    intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl5
    simp only [wp_norm, hsp3] at hsp4
    rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
    simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
    dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    simp only [wp_norm, hsp3, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr4
    simp only [htr3] at htr4
    rw [← M.stepEvents_append (vmacEvs ++ rustAllocEvents 23 1) (rustDeallocEvents newPqrCap.toNat 1) st]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl5 (mid := (blkPl_434).base + bv% (780))
    wp_sync_433 ((blkPl_434).base + bv% (780))
    apply SepWP.done (by rfl) (by exact hrun4)
    intro hcl6
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rfl) (by exact hrun4)
    intro _ _ hmf
    refine ⟨(vmacEvs ++ rustAllocEvents 23 1) ++ rustDeallocEvents newPqrCap.toNat 1,
      SeqEnv.append (SeqEnv.append rfl rfl) (freeOnlyEvs_rustDeallocEvents newPqrCap.toNat 1),
      by rfl, ⟨hrun4, hsp4, hsp0,
        spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4,
        ?_, htr4, hcl6, by simp only [wp_norm, hvregs_4]⟩,
      by simp only [wp_norm, hx19_4],
      by simp only [wp_norm, hx20_4],
      by simp only [wp_norm, hx26_4]; rfl, ?_⟩
    · simp only [wp_norm, hx29_4]
    · unfold tryDecryptCommonHeap
      rw [sessionStateAt_atState, trAt_atState, speBodyAt_atState, protocolAddressAt_atState,
          protocolAddressAt_atState, signalMessageAt_atState, logOff_eq_macLsLogOff, A.atState_pool]
      unfold speBodyAt
      rw [trAt_eq_rest A.repAlloc s0.sp trG tr,
          stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
          errTail_sp_split s0.sp,
          errTail_reg190_s7_split s0.sp]
      rw [← A.repAlloc_live_norm] at hmf
      have hmf1 := Satisfies.mono_focus (macFailed_assemble A.repAlloc s0.sp p hp) (by sep_focus) hmf
      have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
      sep_close

theorem verifyMac_549_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpecX M A lim C.F uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustNoAllocShimSym) (withStack sessionShimBudgetSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustAllocSym) (rustAllocSpecWithStack M A lim false extHookStack))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack M A lim extHookStack)) :
    S7SeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C decFn A lim ctl uuidTryParse S (s7Env C.F uuidTryParse) := by
  intro x st trG tr st1 mks newPqrState draws R s0 s hfits h7 hL
  by_cases hok : x.msg.verifyMacWithAddresses C.F
      (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true
  · simp only [hok, ↓reduceIte]
    exact verifyMac_true_549_placed_ok_x C decFn A lim ctl S H hVMac
      x st trG tr st1 mks newPqrState draws R s0 s hfits hok h7 hL
  · have hok_false : x.msg.verifyMacWithAddresses C.F
        (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false :=
      Bool.eq_false_iff.mpr hok
    simp only [hok_false, Bool.false_eq_true, ↓reduceIte]
    exact verifyMac_false_549_placed_ok_x C decFn A lim ctl S H hVMac hshim halloc hdealloc
      x st trG tr st1 mks newPqrState draws R s0 s hfits hok_false h7 hL

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget
