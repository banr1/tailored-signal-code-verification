/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProofBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargets
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSymBudget
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable Tight-Panic `S1` & `ErrTail` Theorems

Proves `errTail_placed_okT` and `errTail_placed_okT_x` (`ErrTailSeamTightPlaced`,
`ErrTailSeamTightXPlaced`), derives standard `ErrTailSeamPlaced` / `ErrTailSeamXPlaced` corollaries,
and specializes the pinned tight-panic Segment S1 theorems over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargetsBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession
  (Crypto SessionState SignalProtocolError TripleRatchet)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_57 blkPl_57 lsmpl)
open CryptoVerification.RustHeap (RustAlloc arrayAt)
open CryptoVerification.LibsignalSessionRepr (chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr
  (UuidParser decryptDraws protocolAddressAt sessionStateAt signalMessageAt speWord
   tapeAfter utf8 uuidTryParse vecResultAt)
open CryptoVerification.LibsignalTripleRatchet
  (SpqrModel TrGhost TryDecryptGhost decResultFnAt logOff trAt)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (dropChainStack lsRustDeallocSym)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (speBodyAt speTag tryDecryptCommonHeap tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
  (blkPC_131 blkPl_131 decRel_afterTrFrom errTail_stack_recombine
   exists_words3_of_memRegion_24 exists_words5_of_errTailBody exists_words5_of_speBodyAt
   exists_words6_of_memRegion_48 sepWP_to_reaches_pc_midMeta_placed
   stackAt_tryDecryptSubStack_sub trAt_expose_errTail
   tryDecryptDummyImg tryDecryptMidMeta_placed tryDecryptWPInv words5At)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
  (ErrTailSeamPlaced ErrTailSeamXPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
  (ErrTailSeamTightPlaced ErrTailSeamTightXPlaced
   tryDecryptFnSpecTightPlaced tryDecryptSpecTightPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
  (ErrTailStatePlaced_to_placed ErrTailStateXPlaced_to_placed
   ErrTailStateX_placed ErrTailState_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProofBudget
  (errTail_all_steps_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget
  (S1SeamTightFreePlaced S1SeamTightFreeXPlaced
   S1SeamTightGenPlaced S1SeamTightGenXPlaced
   S1SeamTightPinnedGenPlaced S1SeamTightPinnedGenXPlaced
   decResultFnAt_atState
   loadRatchet_after_call_error_tight_placed loadRatchet_after_call_error_tight_x_placed
   loadRatchet_gen_placed_okT loadRatchet_gen_placed_okT_x
   loadRatchet_placed_okT loadRatchet_placed_okT_x
   loadRatchet_tight_pinned_gen_placed_ok loadRatchet_tight_pinned_gen_placed_ok_x
   reaches_epilogue_to_outcome_tight_fn_placed reaches_epilogue_to_outcome_tight_placed
   reaches_epilogue_to_outcome_tight_seam_fn_placed reaches_epilogue_to_outcome_tight_seam_placed)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget
  (trFromPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
  (chainAt_atState_fn invalidMessageStrAt_atState live_atState
   protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState
   vecResultAt_atState vecU8_atState)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Relocatable `[LibsignalPlacement]` Tight `P3kR1bc` Combinators & `ErrTail` Proofs -/

namespace P3kR1bc

export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget (
  reaches_epilogue_to_outcome_tight_seam_placed
  reaches_epilogue_to_outcome_tight_placed
  reaches_epilogue_to_outcome_tight_seam_fn_placed
  reaches_epilogue_to_outcome_tight_fn_placed
  loadRatchet_after_call_error_tight_placed
  loadRatchet_after_call_error_tight_x_placed
)

theorem errTail_ok_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : TryDecryptGhost) (st_init st : M.σ)
    (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State)
    (he : e ≠ .panic)
    (hmod1 : (x.model C S uuidTryParse).1 = .error e)
    (hmod2 : (x.model C S uuidTryParse).2 = st1)
    (hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st FreeOnlyEvs)
    (herr : ErrTailState_placed A lim st ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptSpecTightPlaced C A lim ctl uuidTryParse S tdEnv) (x, st_init) R s0 s := by
  rcases herr with ⟨hpc, hmeta, hx19, hx20, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta_placed.to_wpInv hmeta
  have hcl : LibsignalCodeLoaded lsmpl s.mem := hmeta.2.2.2.2.2.2.1
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  let A0 : RustAlloc := A.atState lim st s
  have hmem_tr :
      s.mem ⊨ trAt A0 (sp + 0x38#64) trG tr ∗
        (sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ speBodyAt A0 (utf8 "decrypt") (sp + 0x168#64) e ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp, A0]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ speBodyAt A.repAlloc (utf8 "decrypt") (sp + 0x168#64) e ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp, A0] at hmem1 ⊢
    rw [chainAt_atState_fn, live_atState, sessionStateAt_atState] at hmem1
    have hspe_eq : speBodyAt (A.atState lim st s) (utf8 "decrypt") (sp + 0x168#64) e =
        speBodyAt A.repAlloc (utf8 "decrypt") (sp + 0x168#64) e := by
      cases e <;> simp only [speBodyAt, invalidMessageStrAt_atState, vecU8_atState]
    rw [hspe_eq] at hmem1
    convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_speBodyAt he hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 = memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide, memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗ (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    rw [h140_split] at hmem3; dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp := errTail_all_steps_wp_placed (A := A) (lim := lim) (ast := st) (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2)
    hdealloc hcs_le hcs_lt hpc hmeta_wp hcl hx19 hx20 hx26
  unfold tryDecryptCommonHeap at hmem4
  dsimp only [A0] at hmem4
  rw [protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hpool_eq : (A.atState lim st s).pool = A.pool lim st s := rfl
  rw [hpool_eq] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool lim st s ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptDummyImg ∗ tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  apply reaches_epilogue_to_outcome_tight_seam_placed x st_init st x.G.afterTrFrom R s0 s hnpan hG' hsb
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta_placed hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩; subst hPf
  have hm_ex :
      sf.mem ⊨
        (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
         ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ speTag e) ∗
         words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ stackAt sp dropChainStack ∗
         memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptDummyImg ∗ tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨evs_exit, hm_ex⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_ex
  rcases hm_ex with ⟨hevs_exit, hm_ex⟩
  refine ⟨evs_exit, hevs_exit, hmeta_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [sessionStateAt_atState, vecResultAt_atState,
      protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hpool_f : (A.atState lim (M.stepEvents evs_exit st) sf).pool =
      A.pool lim (M.stepEvents evs_exit st) sf := rfl
  rw [hpool_f]
  have hdec_ent :
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      vecResultAt A.repAlloc x.ret (x.model C S uuidTryParse).1 := by
    rw [hmod1]; exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptDummyImg ∗
          (stackAt sp dropChainStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗ A.pool lim (M.stepEvents evs_exit st) sf) ∗ R := by
    dsimp only [sp] at hm_ex ⊢; convert hm_ex using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono hdec_ent (sepConj_mono_left
      (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4)))) hmem_f_re

theorem errTail_ok_tight_x_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : TryDecryptGhost) (st_init st : M.σ)
    (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State)
    (he : e ≠ .panic)
    (hmod1 : (x.modelFn C decFn S uuidTryParse).1 = .error e)
    (hmod2 : (x.modelFn C decFn S uuidTryParse).2 = st1)
    (hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st FreeOnlyEvs)
    (herr : ErrTailStateX_placed A lim st ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptFnSpecTightPlaced C decFn A lim ctl uuidTryParse S tdEnv) (x, st_init) R s0 s := by
  rcases herr with ⟨hpc, hmeta, hx19, hx20, b, hb, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta_placed.to_wpInv hmeta
  have hcl : LibsignalCodeLoaded lsmpl s.mem := hmeta.2.2.2.2.2.2.1
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  set tag := if b then speTag e else speWord 20
  let A0 : RustAlloc := A.atState lim st s
  have hmem_tr :
      s.mem ⊨ trAt A0 (sp + 0x38#64) trG tr ∗
        (sessionStateAt A0 x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         (if b then speBodyAt A0 (utf8 "decrypt") (sp + 0x168#64) e else memRegion (sp + 0x168#64) 40) ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp, A0]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ (if b then speBodyAt A.repAlloc (utf8 "decrypt") (sp + 0x168#64) e else memRegion (sp + 0x168#64) 40) ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp, A0] at hmem1 ⊢
    rw [chainAt_atState_fn, live_atState, sessionStateAt_atState] at hmem1
    have hspe_eq : speBodyAt (A.atState lim st s) (utf8 "decrypt") (sp + 0x168#64) e =
        speBodyAt A.repAlloc (utf8 "decrypt") (sp + 0x168#64) e := by
      cases e <;> simp only [speBodyAt, invalidMessageStrAt_atState, vecU8_atState]
    rw [hspe_eq] at hmem1
    convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_errTailBody he hb hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 = memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide, memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗ (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A0 ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    rw [h140_split] at hmem3; dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp := errTail_all_steps_wp_placed (A := A) (lim := lim) (ast := st) (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2)
    hdealloc hcs_le hcs_lt hpc hmeta_wp hcl hx19 hx20 hx26
  unfold tryDecryptCommonHeap at hmem4
  dsimp only [A0] at hmem4
  rw [protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hpool_eq : (A.atState lim st s).pool = A.pool lim st s := rfl
  rw [hpool_eq] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool lim st s ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptDummyImg ∗ tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.modelFn C decFn S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.modelFn C decFn S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  apply reaches_epilogue_to_outcome_tight_seam_fn_placed x st_init st x.G.afterTrFrom R s0 s hnpan hG' hsb
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta_placed hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩; subst hPf
  have hm_ex :
      sf.mem ⊨
        (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
         ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ tag) ∗
         words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ stackAt sp dropChainStack ∗
         memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptDummyImg ∗ tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨evs_exit, hm_ex⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_ex
  rcases hm_ex with ⟨hevs_exit, hm_ex⟩
  refine ⟨evs_exit, hevs_exit, hmeta_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [sessionStateAt_atState, decResultFnAt_atState,
      protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hpool_f : (A.atState lim (M.stepEvents evs_exit st) sf).pool =
      A.pool lim (M.stepEvents evs_exit st) sf := rfl
  rw [hpool_f]
  have hdec_ent :
      ((x.ret ↦₆₄ tag) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      decResultFnAt A.repAlloc x.ret (x.modelFn C decFn S uuidTryParse).1 := by
    rw [hmod1]; exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ tag) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptDummyImg ∗
          (stackAt sp dropChainStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗ A.pool lim (M.stepEvents evs_exit st) sf) ∗ R := by
    dsimp only [sp] at hm_ex ⊢; convert hm_ex using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono hdec_ent (sepConj_mono_left
      (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4)))) hmem_f_re

end P3kR1bc

/-! ## 2. Top-Level Relocatable `[LibsignalPlacement]` Tight `S1` & `ErrTail` Seam Theorems -/

export P3kR1bc (errTail_ok_tight_placed errTail_ok_tight_x_placed)

export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget (
  S1SeamTightGenPlaced
  S1SeamTightPinnedGenPlaced
  S1SeamTightGenXPlaced
  S1SeamTightPinnedGenXPlaced
  S1SeamTightFreePlaced
  S1SeamTightFreeXPlaced
  loadRatchet_tight_pinned_gen_placed_ok
  loadRatchet_tight_pinned_gen_placed_ok_x
  loadRatchet_gen_placed_okT
  loadRatchet_gen_placed_okT_x
  loadRatchet_placed_okT
  loadRatchet_placed_okT_x
)

abbrev S1SeamTightPinnedFreePlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1SeamTightPinnedGenPlaced prog entry C A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

abbrev S1SeamTightPinnedFreeXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1SeamTightPinnedGenXPlaced prog entry C decFn A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

/-- Relocatable `[LibsignalPlacement]` pinned Segment S1 theorem with tight panic
(`S1SeamTightPinnedFreePlaced`). -/
theorem loadRatchet_pinned_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec M A lim))
    (hs1Ok : ∀ x evs, FreeOnlyEvs evs → s1OkEnv x evs) :
    S1SeamTightPinnedFreePlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      C A lim ctl uuidTryParse S tdEnv s1OkEnv :=
  loadRatchet_tight_pinned_gen_placed_ok htrFrom (fun _ h => h) hs1Ok

/-- Relocatable `[LibsignalPlacement]` pinned `decFn` (`X`) Segment S1 theorem with tight panic
(`S1SeamTightPinnedFreeXPlaced`). -/
theorem loadRatchet_pinned_placed_okT_x [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec M A lim))
    (hs1Ok : ∀ x evs, FreeOnlyEvs evs → s1OkEnv x evs) :
    S1SeamTightPinnedFreeXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      C decFn A lim ctl uuidTryParse S tdEnv s1OkEnv :=
  loadRatchet_tight_pinned_gen_placed_ok_x htrFrom (fun _ h => h) hs1Ok

/-- Relocatable `[LibsignalPlacement]` budget-threaded `ErrTail` theorem with tight panic
(`ErrTailSeamTightPlaced`). -/
theorem errTail_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    ErrTailSeamTightPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      C A lim ctl uuidTryParse S tdEnv := by
  intro x st_init st trG tr st1 e R s0 s he hmod1 hmod2 hsb herr
  exact P3kR1bc.errTail_ok_tight_placed hdealloc x st_init st trG tr st1 e R s0 s
    he hmod1 hmod2 hsb (ErrTailStatePlaced_to_placed herr).1

/-- Relocatable `[LibsignalPlacement]` budget-threaded `decFn` (`X`) `ErrTail` theorem with tight
panic (`ErrTailSeamTightXPlaced`). -/
theorem errTail_placed_okT_x [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    ErrTailSeamTightXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      C decFn A lim ctl uuidTryParse S tdEnv := by
  intro x st_init st trG tr st1 e R s0 s he hmod1 hmod2 hsb herr
  exact P3kR1bc.errTail_ok_tight_x_placed hdealloc x st_init st trG tr st1 e R s0 s
    he hmod1 hmod2 hsb (ErrTailStateXPlaced_to_placed herr).1

/-- Standard `ErrTailSeamPlaced` corollary via `ErrTailSeamTightPlaced.weaken`. -/
theorem errTail_seam_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    ErrTailSeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      C A lim ctl uuidTryParse S tdEnv :=
  (errTail_placed_okT hdealloc).weaken

/-- `decFn` (`X`) `ErrTailSeamXPlaced` corollary via `ErrTailSeamTightXPlaced.weaken`. -/
theorem errTail_seam_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    ErrTailSeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      C decFn A lim ctl uuidTryParse S tdEnv :=
  (errTail_placed_okT_x hdealloc).weaken

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargetsBudget
