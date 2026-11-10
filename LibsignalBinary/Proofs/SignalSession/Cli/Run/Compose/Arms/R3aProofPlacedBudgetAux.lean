/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cHelpersPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFinishStep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailBuildMessage
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# Budget-Threaded `signal_session::run` Arm `R3a` Auxiliary Helpers and Tails

Frame-splitting, word-relocation, `FreeOnlyEvs` event combinators, Block `85`
`SignalMessage::try_from` budget transfer, and accept/reject epilogue tails (including
`CodeOk`-parametric variants) for Arm `R3a` on Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSessionApi (ApiError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.E2E.Pqxdh.ResponderWire (ls_subroutine_ok_cro_of_block)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails (words64At)
open CryptoVerification.LibsignalPublicApi.StoreKit (NoFsEv withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal apiDecResultAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost okTagVec protocolAddressAt vecResultAt)
open CryptoVerification.RustHeap (RustAlloc vecAt vecHeader vecU8 vecU8At)
open CryptoVerification.SignalSession (Inputs lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallW RunCall addrWords callAt callHeap cliWrOk inputOf namedWrites
   ownedBytes ownedBytes_dealloc ownedBytes_zero_entails_emp runResAt runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Bytes InRunPlaced RejectKind RunHistOk RunNeeds RunSem SlotAns addrNameHeap
   addrUpperAt addrUpperAt_entails_memRegion finish joinMem protocolAddressAt_eq_parts
   rejectMem runFiles runFsp runLocalBytes runLocals runLocalsFrom runLocals_empty_eq
   runPcPlaced runPcPlaced_eq runProgPlaced runSaved slotOut slotTrace)
open CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers
  (R1cCodeOk r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
   r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setPState
   r1c_calleeSavedVRegs_writeReg64 r1c_extractLsb_append_hi r1c_extractLsb_append_lo
   r1c_fs_setMem r1c_fs_setPC r1c_fs_setPState r1c_fs_writeReg64 r1c_fs_writeVReg128
   r1c_mem_setPState r1c_readReg64_setPState r1c_sepWPp_exists_left r1c_sepWPp_pure_left
   r1c_sepWPp_weaken_pre r1c_spAligned r1c_sp_setPState r1c_status_setPState
   r1c_symtab_setPState r1c_trace_setPState)
open CryptoVerification.SignalSession.Cli.RunDrop (SpeOwned speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunProofs (slotOut_err_ne_store)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame runNeed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen lsRetAddr624_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cHelpersPlacedBudget
  (r1c_call_dealloc r1c_call_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlacedEnv RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (runNeed_bounds_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
  (tripleRatchetHooksWPlaced_of_codecHooks tryFromDepsPlaced_of_codecHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget (dropSpeOwnedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
  (TryFromEnv tryFromPlacedSpec tryFrom_placed_ok_of_deps)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

attribute [local simp, local arm64_norm, local wp_norm]
  r1c_extractLsb_append_lo r1c_extractLsb_append_hi
  r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
  r1c_calleeSavedVRegs_writeReg64
  r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPState
  r1c_readReg64_setPState r1c_sp_setPState r1c_mem_setPState r1c_status_setPState
  r1c_trace_setPState r1c_symtab_setPState r1c_fs_setPState
  r1c_fs_writeReg64 r1c_fs_writeVReg128 r1c_fs_setPC r1c_fs_setMem

local macro "r3a_close_post" : tactic =>
  `(tactic| (repeat' apply And.intro; all_goals (simp (config := { zetaDelta := true }) only [runPcPlaced_eq, RejectKind.pcOff, lsRustDeallocSymCli, lsρ, BitVec.ofNat_eq_ofNat, runFsp, wp_norm, arm64_norm, *]; try bv_omega)))

/-! ## 1. `VmPreserved` Framing, `FreeOnlyEvs` Combinators, and Block `85` Callee Transfer -/

theorem r3a_storesAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a : BitVec 64) (g' : StoresGhost) :
    storesAt (A.atState lim st s) a g' = storesAt A.repAlloc a g' := rfl

theorem r3a_vecU8_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 (A.atState lim st s) v bs = vecU8 A.repAlloc v bs := rfl

theorem r3a_sepWPp_exists_left {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x ∗ F) Q Qp oom) :
    SepWPp prog ret s ((∃∗ x : α, P x) ∗ F) Q Qp oom := by
  rw [sepExists_sepConj_left]
  exact r1c_sepWPp_exists_left h

theorem r3a_runResAt_some_none_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (r : BitVec 64) :
    runResAt (A.atState lim st s) cliWrOk r (some none) =
      runResAt A.repAlloc cliWrOk r (some none) := rfl

theorem r3a_addrNameHeap_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : AddrGhost) :
    addrNameHeap (A.atState lim st s) g = addrNameHeap A.repAlloc g := rfl

theorem r3a_frame_seq_vm [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P_in P P' F : SepProp} {post : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : R1cCodeOk s.mem) (hP : P_in ⊢ P ∗ F)
    (h : SepWP prog mid s P (fun s1 P1 => VmPreserved s s1 ∧ post s1 ∧ (P1 ⊢ P')))
    (hk : ∀ s1 : State, VmPreserved s s1 → R1cCodeOk s1.mem → s1.pc = mid →
      s1.status = .Running → post s1 → SepWPp prog ret s1 (P' ∗ F) Q Qp oom) :
    SepWPp prog ret s P_in Q Qp oom := by
  intro R hm hL
  have hm0 : s.mem ⊨ P ∗ (F ∗ R) :=
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  rcases h.elim hm0 hL with ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hvm1, hpost1, hent1⟩ | ⟨_, hfalse⟩⟩
  · have hm1' : s1.mem ⊨ (P' ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent1) hm1
    obtain ⟨sf, hsteps2, hout⟩ :=
      hk s1 hvm1 (hinv.of_keepsFrozen hsteps.keepsFrozen) hpc1 hrun1 hpost1 R hm1'
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem r3a_freeOnly_nil : FreeOnlyEvs [] := by
  intro _ h; cases h

theorem r3a_freeOnly_dealloc (sz al : Nat) : FreeOnlyEvs (rustDeallocEvents sz al) := by
  intro ev h
  simp only [rustDeallocEvents, List.mem_singleton] at h
  exact ⟨al, sz, h⟩

theorem r3a_freeOnly_append {e1 e2 : List AllocEvent}
    (h1 : FreeOnlyEvs e1) (h2 : FreeOnlyEvs e2) : FreeOnlyEvs (e1 ++ e2) := by
  intro ev h
  rcases List.mem_append.mp h with hm1 | hm2
  · exact h1 ev hm1
  · exact h2 ev hm2

theorem tryFromEnv_iff_bytes {a₁ a₂ ret₁ ret₂ : BitVec 64} {rest : List (BitVec 8)}
    {evs : List AllocEvent} :
    TryFromEnv ⟨a₁, rest, ret₁⟩ evs ↔ TryFromEnv ⟨a₂, rest, ret₂⟩ evs := by
  constructor
  · rintro (_ | h | ⟨h1, h2⟩)
    · exact .nil
    · exact .loopOnly h
    · exact .loopPost h1 h2
  · rintro (_ | h | ⟨h1, h2⟩)
    · exact .nil
    · exact .loopOnly h
    · exact .loopPost h1 h2

theorem r3a_sigTryFrom_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A lim)) :=
  ls_subroutine_ok_cro_of_block (callerProg := runProgPlaced H) (i := 579) (j := 85)
    (tryFrom_placed_ok_of_deps
      (tripleRatchetHooksWPlaced_of_codecHooks hh.codecHooks)
      (tryFromDepsPlaced_of_codecHooks hh.codecHooks))
    (by decide) (by decide) (by decide)

/-! ## 2. Spatial Word Lists, Frame Splits, and Relocation Helpers -/

def r3a_words64At : BitVec 64 → List (BitVec 64) → SepProp
  | _, [] => emp
  | a, w :: ws => (a ↦₆₄ w) ∗ r3a_words64At (a + 8#64) ws

theorem r3a_tw (a : BitVec 64) (ws : List (BitVec 64)) :
    words64At a ws = r3a_words64At a ws := by
  induction ws generalizing a with
  | nil => rfl
  | cons _ _ ih => simp only [words64At, r3a_words64At, ih]

theorem r3a_cs_regs {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
    sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
    sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
    sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
    sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
    sf.readReg64 .fp = s.readReg64 .fp ∧
    calleeSavedVRegs sf = calleeSavedVRegs s := by
  unfold CalleeSavedPreserved at h; simp_all

def r3a_hiGaps (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x240#64) 32 ∗ memRegion (fsp + 0x280#64) 160 ∗ memRegion (fsp + 0x350#64) 48 ∗
    memRegion (fsp + 0x390#64) 208 ∗ memRegion (fsp + 0x548#64) 7784 ∗ memRegion (fsp + 0x23e0#64) 1552

def r3a_frameGaps (fsp : BitVec 64) : SepProp :=
  memRegion fsp 0x208 ∗ r3a_hiGaps fsp

def r3a_restFrame (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗
    memRegion (fsp + 0x23b0#64) 48 ∗ r3a_frameGaps fsp

theorem r3a_tail_split (fsp : BitVec 64) :
    memRegion (fsp + 0x220#64) 10192 =
      memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗
        memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗ memRegion (fsp + 0x4d0#64) 120 ∗
        memRegion (fsp + 0x23b0#64) 48 ∗ r3a_hiGaps fsp := by
  have hs : ∀ (a : BitVec 64) (m n : Nat), m + n ≤ 2 ^ 64 →
      memRegion a (m + n) = memRegion a m ∗ memRegion (a + BitVec.ofNat 64 m) n :=
    fun a m n h => ProofLib.memRegion_split a m n h
  rw [show (10192 : Nat) = 32 + 10160 from rfl, hs _ _ _ (by decide),
    show (10160 : Nat) = 32 + 10128 from rfl, hs _ _ _ (by decide),
    show (10128 : Nat) = 32 + 10096 from rfl, hs _ _ _ (by decide),
    show (10096 : Nat) = 160 + 9936 from rfl, hs _ _ _ (by decide),
    show (9936 : Nat) = 48 + 9888 from rfl, hs _ _ _ (by decide),
    show (9888 : Nat) = 48 + 9840 from rfl, hs _ _ _ (by decide),
    show (9840 : Nat) = 16 + 9824 from rfl, hs _ _ _ (by decide),
    show (9824 : Nat) = 208 + 9616 from rfl, hs _ _ _ (by decide),
    show (9616 : Nat) = 112 + 9504 from rfl, hs _ _ _ (by decide),
    show (9504 : Nat) = 120 + 9384 from rfl, hs _ _ _ (by decide),
    show (9384 : Nat) = 7784 + 1600 from rfl, hs _ _ _ (by decide),
    show (1600 : Nat) = 48 + 1552 from rfl, hs _ _ _ (by decide)]
  unfold r3a_hiGaps; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl

theorem r3a_frame_eq (fsp : BitVec 64) :
    runLocals fsp [] =
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32 ∗
        memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗
        memRegion (fsp + 0x4d0#64) 120 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ r3a_frameGaps fsp := by
  rw [runLocals_empty_eq, show (runLocalBytes : Nat) = 0x208 + 10216 from rfl,
    ProofLib.memRegion_split fsp 0x208 10216 (by decide),
    show (10216 : Nat) = 24 + 10192 from rfl,
    ProofLib.memRegion_split (fsp + 0x208#64) 24 10192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [r3a_tail_split fsp]; unfold r3a_frameGaps; sep_ac_rfl

theorem r3a_frame_join_eq (A : RustAlloc) (fsp : BitVec 64) (out : Bytes) :
    runLocals fsp [(0x208, 24, vecU8 A (fsp + 0x208#64) out)] =
      vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32 ∗
        memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗
        memRegion (fsp + 0x4d0#64) 120 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ r3a_frameGaps fsp := by
  simp only [runLocals, runLocalsFrom, Nat.sub_zero, BitVec.add_zero]
  rw [show runLocalBytes - (0x208 + 24) = 10192 from rfl, r3a_tail_split fsp]
  unfold r3a_frameGaps; sep_ac_rfl

theorem r3a_frame_some_eq (fsp : BitVec 64) (meG : AddrGhost) :
    runLocals fsp [(0x1d0, 16, addrUpperAt (fsp + 0x1d0#64) meG)] =
      addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) 40 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32 ∗
        memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗
        memRegion (fsp + 0x4d0#64) 120 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ r3a_hiGaps fsp := by
  simp only [runLocals, runLocalsFrom, Nat.sub_zero, BitVec.add_zero]
  rw [show runLocalBytes - (0x1d0 + 16) = 40 + 10216 from rfl,
    ProofLib.memRegion_split (fsp + 0x1e0#64) 40 10216 (by decide),
    show (10216 : Nat) = 24 + 10192 from rfl,
    ProofLib.memRegion_split (fsp + 0x1e0#64 + 40#64) 24 10192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [r3a_tail_split fsp]; sep_ac_rfl

theorem r3a_locals_empty_rest (fsp : BitVec 64) :
    runLocals fsp [] =
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32 ∗
        memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ r3a_restFrame fsp := by
  rw [r3a_frame_eq fsp]; unfold r3a_restFrame; sep_ac_rfl

theorem r3a_locals_join_rest (A : RustAlloc) (fsp : BitVec 64) (out : Bytes) :
    runLocals fsp [(0x208, 24, vecU8 A (fsp + 0x208#64) out)] =
      vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x220#64) 32 ∗
        memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗
        memRegion (fsp + 0x4d0#64) 120 ∗ r3a_restFrame fsp := by
  rw [r3a_frame_join_eq A fsp out]; unfold r3a_restFrame; sep_ac_rfl

theorem r3a_memRegion_words : ∀ (n : Nat) (a : BitVec 64) {m : Memory} {R : SepProp},
    8 * n ≤ 2 ^ 64 → (m ⊨ memRegion a (8 * n) ∗ R) →
      ∃ ws : List (BitVec 64), ws.length = n ∧ (m ⊨ r3a_words64At a ws ∗ R)
  | 0, a, _, _, _, hm =>
    ⟨[], rfl, by simpa only [Nat.mul_zero, ProofLib.memRegion_zero, r3a_words64At] using hm⟩
  | n + 1, a, _, R, hle, hm => by
    have hsplit : memRegion a (8 * (n + 1)) = memRegion a 8 ∗ memRegion (a + 8#64) (8 * n) := by
      rw [show 8 * (n + 1) = 8 + 8 * n by omega]
      exact ProofLib.memRegion_split a 8 (8 * n) (by omega)
    rw [hsplit, ProofLib.memRegion_eight a, sepExists_sepConj_left, sepExists_sepConj_left,
      satisfies_sepExists] at hm
    obtain ⟨w, hm⟩ := hm
    obtain ⟨ws, hlen, hws⟩ := r3a_memRegion_words n (a + 8#64) (by omega)
      (Eq.mp (congrArg (_ ⊨ ·) (by sep_ac_rfl)) hm :
        _ ⊨ memRegion (a + 8#64) (8 * n) ∗ ((a ↦₆₄ w) ∗ R))
    exact ⟨w :: ws, by simp [hlen],
      by simpa only [r3a_words64At] using Eq.mp (congrArg (_ ⊨ ·) (by sep_ac_rfl)) hws⟩

theorem r3a_open_words (n : Nat) (a : BitVec 64) {m : Memory} {Q : SepProp}
    (hm : m ⊨ memRegion a (8 * n) ∗ Q) (hle : 8 * n ≤ 2 ^ 64 := by decide) :
    ∃ ws : List (BitVec 64), ws.length = n ∧ (m ⊨ r3a_words64At a ws ∗ Q) :=
  r3a_memRegion_words n a hle hm

theorem r3a_words_mem_aux : ∀ (ws : List (BitVec 64)) (a : BitVec 64),
    ws.length ≤ 1024 → r3a_words64At a ws ⊢ memRegion a (8 * ws.length)
  | [], a, _ => by
    simpa only [List.length_nil, Nat.mul_zero, ProofLib.memRegion_zero, r3a_words64At] using
      Entails.refl emp
  | w :: ws, a, hle => by
    rw [List.length_cons] at hle
    have h8 : 8 + 8 * ws.length ≤ 2 ^ 64 :=
      Nat.le_trans (by omega : 8 + 8 * ws.length ≤ 16384) (by decide : 16384 ≤ 2 ^ 64)
    have hsplit : memRegion a (8 * (w :: ws).length) =
        memRegion a 8 ∗ memRegion (a + 8#64) (8 * ws.length) := by
      rw [List.length_cons, show 8 * (ws.length + 1) = 8 + 8 * ws.length by omega]
      exact ProofLib.memRegion_split a 8 (8 * ws.length) h8
    rw [hsplit]
    exact sepConj_mono (pointsTo64_entails_memRegion a w)
      (r3a_words_mem_aux ws (a + 8#64) (by omega))

theorem r3a_words_to_memRegion (ws : List (BitVec 64)) (a : BitVec 64) (n : Nat)
    (hn : 8 * ws.length = n := by rfl) (hle : ws.length ≤ 1024 := by simp) :
    r3a_words64At a ws ⊢ memRegion a n :=
  hn ▸ r3a_words_mem_aux ws a hle

theorem r3a_rejoin_1d0 (fsp w0 w1 : BitVec 64) :
    r3a_words64At (fsp + 0x1d0#64) [w0, w1] ∗ memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) 40 ⊢
      memRegion fsp 0x208 := by
  refine Entails.trans (sepConj_mono_left (r3a_words_to_memRegion [w0, w1] (fsp + 0x1d0#64) 16)) ?_
  have h1 : memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1d0#64) 16 = memRegion fsp 0x1e0 :=
    (ProofLib.memRegion_split fsp 0x1d0 16 (by decide)).symm
  have h2 : memRegion fsp 0x1e0 ∗ memRegion (fsp + 0x1e0#64) 40 = memRegion fsp 0x208 :=
    (ProofLib.memRegion_split fsp 0x1e0 40 (by decide)).symm
  rw [← h2, ← h1]; exact Entails.of_eq (by sep_ac_rfl)

theorem r3a_word_to_devPad (a w : BitVec 64) {dev : BitVec 8} (hdev : w.setWidth 8 = dev) :
    (a ↦₆₄ w) ⊢ (a ↦₈ dev) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes]; simp only [unpack64]
  have hb0 : w.extractLsb' 0 8 = dev := by
    subst hdev; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  rw [hb0, pointsToBytes_cons]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion (a + 1#64) _)

private theorem r3a_memRegion_bytes : ∀ (n : Nat) (a : BitVec 64) {m : Memory} {R : SepProp},
    n ≤ 2 ^ 64 → (m ⊨ memRegion a n ∗ R) →
      ∃ bs : List (BitVec 8), bs.length = n ∧ (m ⊨ (a ↦ₛ bs) ∗ R)
  | 0, a, _, _, _, hm =>
    ⟨[], rfl, by simpa only [ProofLib.memRegion_zero, pointsToBytes_nil] using hm⟩
  | n + 1, a, _, R, hle, hm => by
    have hsplit : memRegion a (n + 1) = memRegion a 1 ∗ memRegion (a + 1#64) n := by
      rw [show n + 1 = 1 + n by omega]
      exact ProofLib.memRegion_split a 1 n (by omega)
    rw [hsplit, ProofLib.memRegion_one a, sepExists_sepConj_left, sepExists_sepConj_left,
      satisfies_sepExists] at hm
    obtain ⟨b, hm⟩ := hm
    obtain ⟨bs, hlen, hbs⟩ := r3a_memRegion_bytes n (a + 1#64) (by omega)
      (Eq.mp (congrArg (_ ⊨ ·) (by sep_ac_rfl)) hm : _ ⊨ memRegion (a + 1#64) n ∗ ((a ↦₈ b) ∗ R))
    exact ⟨b :: bs, by simp [hlen],
      by simpa only [pointsToBytes_cons] using Eq.mp (congrArg (_ ⊨ ·) (by sep_ac_rfl)) hbs⟩

private def r3a_pack64Bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

private theorem r3a_unpack_pack64Bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    unpack64 (r3a_pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  unfold unpack64 r3a_pack64Bytes
  simp only [List.cons.injEq, and_true]
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
    by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem r3a_addrUpper_relocate (src : BitVec 64) (g : AddrGhost) {m : Memory} {R : SepProp}
    (hm : m ⊨ addrUpperAt src g ∗ R) :
    ∃ (u1 : BitVec 64),
      (m ⊨ r3a_words64At src [BitVec.ofNat 64 g.name.bytes.length, u1] ∗ R) ∧
      (∀ dst : BitVec 64,
        r3a_words64At dst [BitVec.ofNat 64 g.name.bytes.length, u1] ⊢ addrUpperAt dst g) := by
  unfold addrUpperAt at hm
  have hm7 : m ⊨ memRegion (src + 9#64) 7 ∗
      (((src ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ ((src + 8#64) ↦₈ g.device)) ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by sep_ac_rfl)) hm
  obtain ⟨bs, hlen, hm7⟩ := r3a_memRegion_bytes 7 (src + 9#64) (by decide) hm7
  rcases bs with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hlen; done)
  let u1 := r3a_pack64Bytes g.device b1 b2 b3 b4 b5 b6 b7
  have hu1_eq : ∀ b : BitVec 64,
      ((b + 8#64) ↦₆₄ u1) = ((b + 8#64) ↦₈ g.device) ∗ ((b + 9#64) ↦ₛ [b1, b2, b3, b4, b5, b6, b7]) := by
    intro b
    rw [pointsTo64_eq_pointsToBytes, r3a_unpack_pack64Bytes, pointsToBytes_cons]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine ⟨u1, ?_, ?_⟩
  · dsimp only [r3a_words64At]; rw [sepConj_emp, hu1_eq src]
    exact Eq.mp (congrArg (m ⊨ ·) (by sep_ac_rfl)) hm7
  · intro dst
    unfold addrUpperAt
    dsimp only [r3a_words64At]; rw [sepConj_emp, hu1_eq dst]
    refine sepConj_mono_right (sepConj_mono_right ?_)
    exact pointsToBytes_entails_memRegion (dst + 9#64) [b1, b2, b3, b4, b5, b6, b7]

theorem r3a_addrNameHeap_cap_lt (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g ⊢ ⌜g.name.cap.toNat < 2 ^ 63⌝ ∗ addrNameHeap A g := by
  unfold addrNameHeap; refine Entails.pure_left fun h => ?_
  exact Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

theorem r3a_addrNameHeap_to_owned (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g ⊢ ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  unfold addrNameHeap ownedBytes; refine Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
  exact Entails.pure_right ⟨rfl, hle, hlt, hne⟩ (Entails.refl _)

theorem r3a_owned_to_addrNameHeap (A : RustAlloc) (cap ptr len : BitVec 64)
    (bs : List (BitVec 8)) (dev : BitVec 8) :
    ownedBytes A cap ptr len bs ⊢ ⌜len = BitVec.ofNat 64 bs.length⌝ ∗ addrNameHeap A ⟨⟨cap, ptr, bs⟩, dev⟩ := by
  unfold ownedBytes addrNameHeap; refine Entails.pure_left fun ⟨hlen, hle, hlt, hne⟩ => ?_
  exact Entails.pure_right hlen (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

theorem r3a_pack_peer (A : RustAlloc) (a : BitVec 64) (peerV : AddrV)
    (w1 w2 w3 w4 : BitVec 64) (hdev : w4.setWidth 8 = peerV.device) :
    r3a_words64At a [w1, w2, w3, w4] ∗ ownedBytes A w1 w2 w3 peerV.name ⊢
      protocolAddressAt A ⟨⟨w1, w2, peerV.name⟩, peerV.device⟩ a := by
  refine Entails.trans (sepConj_mono_right (r3a_owned_to_addrNameHeap A w1 w2 w3 peerV.name peerV.device)) ?_
  rw [sepConj_comm, sepConj_assoc]; apply Entails.pure_left; rintro rfl
  rw [protocolAddressAt_eq_parts A ⟨⟨w1, w2, peerV.name⟩, peerV.device⟩ a]
  have hd24 : ((a + 24#64) ↦₆₄ w4) ⊢ ((a + 24#64) ↦₈ peerV.device) ∗ memRegion (a + 25#64) 7 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r3a_word_to_devPad (a + 24#64) w4 hdev
  dsimp only [addrUpperAt, r3a_words64At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  exact Entails.trans
    (Entails.of_eq (show _ = ((a + 24#64) ↦₆₄ w4) ∗ ((a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 peerV.name.length) ∗
      addrNameHeap A ⟨⟨w1, w2, peerV.name⟩, peerV.device⟩) by sep_ac_rfl))
    (Entails.trans (sepConj_mono_left hd24) (Entails.of_eq (by sep_ac_rfl)))

theorem r3a_vecU8_open (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢ ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ V : SepProp,
      ⌜cap.toNat < 2 ^ 63 ∧
        (∀ dst : BitVec 64, r3a_words64At dst [cap, ptr, BitVec.ofNat 64 bs.length] ∗ V ⊢ vecU8 A dst bs)⌝ ∗
      r3a_words64At a [cap, ptr, BitVec.ofNat 64 bs.length] ∗ V := by
  unfold vecU8
  apply Entails.sepExists_mono; intro cap; apply Entails.sepExists_mono; intro ptr
  let V : SepProp := ⌜ptr ≠ 0 ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗
    if cap = 0 then emp
    else memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1
  have hpure : V ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ V := by
    dsimp only [V]; refine Entails.pure_left fun h => ?_
    exact Entails.pure_right h.2.2 (Entails.pure_right h (Entails.refl _))
  have hclose : ∀ dst : BitVec 64,
      r3a_words64At dst [cap, ptr, BitVec.ofNat 64 bs.length] ∗ V ⊢ vecU8 A dst bs := by
    intro dst; unfold vecU8
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    dsimp only [vecU8At, vecAt, vecHeader, V, r3a_words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]; exact Entails.of_eq (by sep_ac_rfl)
  refine Entails.sepExists_right V ?_
  have heq : vecU8At A a cap ptr bs = V ∗ r3a_words64At a [cap, ptr, BitVec.ofNat 64 bs.length] := by
    dsimp only [vecU8At, vecAt, vecHeader, V, r3a_words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]; sep_ac_rfl
  rw [heq]; refine Entails.trans (sepConj_mono_left hpure) ?_; rw [sepConj_assoc]
  exact Entails.pure_left fun hlt => Entails.pure_right ⟨hlt, hclose⟩ (Entails.of_eq (by sep_ac_rfl))

theorem r3a_callRecv_open (A : RustAlloc) (a : BitVec 64) (peerV : AddrV) :
    callAt A a (.recv peerV) ⊢ ∃∗ w : CallW, ⌜w.w4.setWidth 8 = peerV.device⌝ ∗
      r3a_words64At a [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      ownedBytes A w.w1 w.w2 w.w3 peerV.name := by
  unfold callAt callHeap addrWords; dsimp only; apply Entails.sepExists_mono; intro w
  have hp : ⌜w.w0 = 9223372036854775811#64⌝ ∗
      (ownedBytes A w.w1 w.w2 w.w3 peerV.name ∗ ⌜w.w4.setWidth 8 = peerV.device⌝) ⊢
      ⌜w.w4.setWidth 8 = peerV.device⌝ ∗ ownedBytes A w.w1 w.w2 w.w3 peerV.name := by
    refine Entails.pure_left fun _ => ?_; rw [sepConj_comm]; exact Entails.refl _
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hp))))))) ?_
  dsimp only [r3a_words64At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  exact Entails.of_eq (by sep_ac_rfl)

theorem r3a_addrSlots_to_memRegion (a cap ptr : BitVec 64) (g : AddrGhost) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ addrUpperAt (a + 16#64) g ⊢ memRegion a 32 := by
  have h1 : memRegion a 8 ∗ memRegion (a + 8#64) 8 = memRegion a 16 :=
    (ProofLib.memRegion_split a 8 8 (by decide)).symm
  have h2 : memRegion a 16 ∗ memRegion (a + 16#64) 16 = memRegion a 32 :=
    (ProofLib.memRegion_split a 16 16 (by decide)).symm
  rw [← h2, ← h1, ← sepConj_assoc]
  exact sepConj_mono
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
    (addrUpperAt_entails_memRegion _ _)

theorem r3a_protoAddr_free_peer (A : RustAlloc) (a : BitVec 64) (g : AddrGhost) :
    protocolAddressAt A g a ⊢
      (a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗ addrUpperAt (a + 16#64) g ∗
        ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  rw [protocolAddressAt_eq_parts A g a]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (r3a_addrNameHeap_to_owned A g)))

theorem r3a_protoAddr_free_me (A : RustAlloc) (a : BitVec 64) (g : AddrGhost) :
    protocolAddressAt A g a ⊢
      memRegion a 32 ∗
        ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  refine Entails.trans (r3a_protoAddr_free_peer A a g) ?_
  refine Entails.trans
    (Entails.of_eq (show _ =
      ((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗ addrUpperAt (a + 16#64) g) ∗
        ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes
      by sep_ac_rfl)) ?_
  exact sepConj_mono_left (r3a_addrSlots_to_memRegion a g.name.cap g.name.ptr g)

theorem r3a_res_split (res : BitVec 64) :
    memRegion res runResSize =
      (∃∗ w : BitVec 64, res ↦₆₄ w) ∗ memRegion (res + 8#64) (runResSize - 8) := by
  conv_lhs => rw [show runResSize = 8 + (runResSize - 8) from rfl]
  rw [ProofLib.memRegion_split res 8 (runResSize - 8) (by decide), ProofLib.memRegion_eight]

theorem r3a_sepWPp_bind {prog : Program} {ret : BitVec 64} {s : State} {A0 F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ R, (s.mem ⊨ A0 ∗ (F ∗ R)) →
      ∃ A1, (s.mem ⊨ A1 ∗ (F ∗ R)) ∧ SepWPp prog ret s (A1 ∗ F) Q Qp oom) :
    SepWPp prog ret s (A0 ∗ F) Q Qp oom := by
  intro R hm hL; rw [sepConj_assoc] at hm
  obtain ⟨_, hm1, hwp⟩ := h R hm; rw [← sepConj_assoc] at hm1; exact hwp R hm1 hL

/-! ## 3. Stack Bounds, Trace/FS Preservation, and Dealloc/Drop Call Wrappers -/

theorem r3a_bounds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {sEnvs : RunSlotEnvs}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63) :
    runFrame ≤ resStack ∧ resStack - runFrame ≤ 2 ^ 63 ∧ resStack - runFrame ≤ 2 ^ 64 ∧
      smallRootStack ≤ resStack - runFrame ∧ 32 + extHookStack ≤ resStack - runFrame ∧
      extHookStack ≤ resStack - runFrame ∧ needs.decryptSignal ≤ resStack - runFrame := by
  obtain ⟨hrf, hs63, hs64, _, _, _, _, _, _, _, _, _, hsm, _, h32, _, hext, _, hdec, _, _, _⟩ :=
    runNeed_bounds_placed hres hres64
  exact ⟨hrf, hs63, hs64, hsm, h32, hext, hdec⟩

theorem r3a_slotOut_ok {ans : SlotAns Bytes} {g' : StoresGhost} {out : Bytes} {s sf : State}
    (h : slotOut ans g' (.ok out) s sf) :
    ans = some (some (g', out)) ∧ ∀ pw ∈ g'.writes, cliWrOk pw.1 := h.2.2

theorem r3a_slotOut_err {g : RunCall} {ans : SlotAns Bytes} {g' : StoresGhost}
    {err : ApiError AddrVal Unit} {s sf : State}
    (ha : g.a = finish ans id) (h : slotOut ans g' (.error err) s sf) :
    err ≠ .store () ∧ g.a = some none :=
  ⟨slotOut_err_ne_store h, by rw [ha, h.2.2]; rfl⟩

theorem r3a_hist_of_slotTrace {i : Inputs} {s0 s sf : State}
    (htr0 : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles i)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) (hst : slotTrace s sf) :
    s0.trace <+: sf.trace ∧ RunHistOk i s0 sf :=
  ⟨htr0.trans hst.1, hst.2.1.trans hfs, hst.2.2.trans hout⟩

theorem r3a_files_eq [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {s sf : State}
    (hh : RunHooksPlaced A lim H) (hsteps : Steps (runProgPlaced H) s sf) (htr : sf.trace = s.trace) :
    sf.fs.files = s.fs.files :=
  (hh.fs (runProgPlaced H) 579).files_eq hsteps (htr.trans (List.append_nil _).symm) NoFsEv.nil

theorem r3a_hist_step [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {i : Inputs} {s0 sm sf : State}
    (hh : RunHooksPlaced A lim H) (hsteps : Steps (runProgPlaced H) sm sf)
    (htr : sf.trace = sm.trace) (hh0 : RunHistOk i s0 sm) : RunHistOk i s0 sf :=
  ⟨(r3a_files_eq hh hsteps htr).trans hh0.1, htr ▸ hh0.2⟩

theorem r3a_hist_eq {i : Inputs} {s0 s s' : State}
    (htr : s'.trace = s.trace) (hfs : s'.fs.files = s.fs.files) (h : RunHistOk i s0 s) :
    RunHistOk i s0 s' :=
  ⟨hfs.trans h.1, htr ▸ h.2⟩

theorem r3a_owned_dealloc_call [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s1 : State} {resStack retOff : Nat}
    {cap ptr len : BitVec 64} {bs : List (BitVec 8)} {Rest : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hcap : cap ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hfp1 : s1.readReg64 .fp = s0.sp - 0x60#64)
    (hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hinv1 : R1cCodeOk s1.mem)
    (hpc1 : s1.pc = lsρ lsRustDeallocSymCli)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = runFsp s0)
    (hlr1 : s1.readReg64 .lr = runPcPlaced retOff)
    (hx0 : s1.readReg64 .x0 = ptr)
    (hx1 : s1.readReg64 .x1 = cap)
    (hx2 : s1.readReg64 .x2 = 1#64)
    (hk : ∀ s2 : State, InRunPlaced R1cCodeOk s0 s2 retOff →
      CalleeSavedPreserved s1 s2 → s2.trace = s1.trace → s2.fs.files = s1.fs.files →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) s2 ∗ Rest)
        Q Qp oom)
    (hlr_ls : LsRetAddr624 (runPcPlaced retOff) := by
      first | assumption | simp (config := { decide := true })
        [_root_.CryptoVerification.SignalSession.Cli.RunCompose.runPcPlaced, wp_norm, arm64_norm,
         _root_.LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen, *]) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
      (ownedBytes A.repAlloc cap ptr len bs ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1 ∗ Rest)
      Q Qp oom := by
  refine r1c_sepWPp_weaken_pre (sepConj_mono_left (ownedBytes_dealloc A.repAlloc hcap)) ?_
  rw [sepConj_assoc]
  refine r1c_sepWPp_pure_left fun hlay => ?_
  refine r1c_call_dealloc hh hext_le hsub64 hsp0 hinv1 hpc1 hrun1 hsp1 hlr1
    hx0 (congrArg BitVec.toNat hx1) hx2 hlay
    (fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
  have hcs := r3a_cs_regs hcs2
  have hin2 : InRunPlaced R1cCodeOk s0 s2 retOff :=
    ⟨hpc2, hrun2, hsp2, hcs.2.2.2.2.2.1.trans hfp1, hinv2, hcs.2.2.2.2.2.2.trans hv1, hsp0⟩
  exact hk s2 hin2 hcs2 htr2 (congrArg FsState.files hfs2)

theorem r3a_drop_spe_call [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {k : SpeOwned} {speAddr : BitVec 64} {sub : Nat}
    {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (h32 : 32 + extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hinv : R1cCodeOk s.mem)
    (hpc : s.pc = (blkPl_553).base)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = runPcPlaced 4076)
    (hsp : s.sp = runFsp s0)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hal0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = speAddr)
    (hk : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      Steps (runProgPlaced H) s sf →
      InRunPlaced R1cCodeOk s0 sf 4076 →
      CalleeSavedPreserved s sf →
      sf.trace = s.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (memRegion speAddr 48 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt (runFsp s0) sub ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (speOwnedAt A.repAlloc speAddr k ∗ A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F)
      Q Qp oom := by
  have hd := hdrop sub h32 hsub64
  refine r1c_call_lscro (⟨speAddr, k⟩, st) hd hinv hpc hrun hsp_al hlr (F := F) ?_
    (hnext := fun sf hsteps hinv_f hpcm hrunm hspm hcsm => ?_)
  · dsimp only [dropSpeOwnedSpec]; rw [hsp]; simp only [sepConj_assoc]
    exact Entails.pure_right
      ⟨hx0, by rw [show Reg.x30 = Reg.lr from rfl, hlr]
               exact lsRetAddr624_base_add 579 4076#64 (by decide) (by decide)⟩
      (Entails.of_eq (by sep_ac_rfl))
  · dsimp only [dropSpeOwnedSpec]
    rw [sepExists_sepConj_left]
    refine r1c_sepWPp_exists_left fun evs => ?_
    simp only [sepConj_assoc]
    refine r1c_sepWPp_pure_left fun ⟨htr_f, hfree⟩ => ?_
    have hcs := r3a_cs_regs hcsm; rw [hsp]
    exact hk sf evs hfree hsteps
      ⟨hpcm, hrunm, hspm.trans hsp, hcs.2.2.2.2.2.1.trans hfp, hinv_f,
        hcs.2.2.2.2.2.2.trans hv, hal0⟩
      hcsm htr_f

/-! ## 4. Reject and Accept Epilogue Tails -/

set_option maxHeartbeats 1600000 in
theorem r3a_tail_peer_reject [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG : AddrGhost}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 4104)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' .postDispatch (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x260#64) 32 ∗
        memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗
        r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let tailF : SepProp := runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
    storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗
    memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ r3a_restFrame fsp ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
        (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
      ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
      addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tailF)
    (Entails.trans (sepConj_mono_left (r3a_protoAddr_free_peer A.repAlloc (fsp + 0x220#64) peerG))
      (by rw [hs.sp]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))) ?_
  have hpc : s.pc = runPcPlaced 4104 := hs.pc
  change s.pc = (blkPl_579).base + 4104#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have h32 : ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
      addrUpperAt (fsp + 0x230#64) peerG ⊢ memRegion (fsp + 0x220#64) 32 := by
    rw [hs.sp]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r3a_addrSlots_to_memRegion (fsp + 0x220#64) peerG.name.cap peerG.name.ptr peerG
  have hclose : ∀ (st' : M.σ) (sf : State),
      memRegion (fsp + 0x220#64) 32 ∗ A.pool lim st' sf ∗ stackAt fsp sub ∗ tailF ⊢
        rejectMem (A.atState lim st' sf) g g' .postDispatch s0 resStack := by
    intro st' sf
    dsimp +zetaDelta only [rejectMem]
    simp only [RustCliAllocBudget.atState_pool, r3a_storesAt_atState,
      r3a_runResAt_some_none_atState]
    rw [r3a_locals_empty_rest (runFsp s0)]
    exact Entails.of_eq (by sep_ac_rfl)
  by_cases hcap : peerG.name.cap = 0
  · refine r1c_sepWPp_weaken_pre
      (sepConj_mono_left (hcap ▸ ownedBytes_zero_entails_emp A.repAlloc _ _ _)) ?_
    rw [emp_sepConj]
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 0x2c7c) s
        (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores) ∧
          (P1 ⊢ ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))) := by
      rw [runPcPlaced_eq, hcap]
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
        r3a_close_post)
    refine r3a_frame_seq_vm
      (F := addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tailF)
      hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 _ hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    have hpc1_rej : s1.pc = runPcPlaced RejectKind.postDispatch.pcOff := by assumption
    have hin1 : InRunPlaced R1cCodeOk s0 s1 RejectKind.postDispatch.pcOff :=
      ⟨hpc1_rej, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
    have henv0 : EnvAt g' .postDispatch st := by
      simpa only [M.stepEvents_nil] using henv [] r3a_freeOnly_nil
    refine r1c_sepWPp_weaken_pre ?_
      (hrej s1 st g' .postDispatch
        ⟨hin1, hx19_1, (fun h => nomatch h), htr1 ▸ htr,
          r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist, hans⟩
        henv0)
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left h32) (hclose st s1))
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .lr = runPcPlaced 0x2c7c ∧
            s1.readReg64 .x0 = peerG.name.ptr ∧ s1.readReg64 .x1 = peerG.name.cap ∧
            s1.readReg64 .x2 = 1#64 ∧ s1.readReg64 (.gpr 19#5) = g.stores) ∧
          (P1 ⊢ ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))) := by
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [lsRustDeallocSymCli, lsρ, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
        r3a_close_post)
    refine r3a_frame_seq_vm
      (F := ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
          (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
        addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tailF)
      hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1
        ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (P' := ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
          (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
        stackAt fsp sub ∗ A.pool lim st s1 ∗ (memRegion (fsp + 0x220#64) 32 ∗ tailF))
      (Entails.trans
        (Entails.of_eq (show _ =
          (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            addrUpperAt (fsp + 0x230#64) peerG) ∗
          (ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
            (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
            stackAt fsp sub ∗ A.pool lim st s1 ∗ tailF) by sep_ac_rfl))
        (Entails.trans (sepConj_mono_left h32)
          (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)))) ?_
    refine r3a_owned_dealloc_call (retOff := 0x2c7c) hh hext hsub64 hcap hs.spAligned
      hfp1 hv1 hinv1 hpc1 hrun1 hsp1 hlr1 hx0_1 hx1_1 hx2_1
      fun sf hin_f hcsm htr_f hfs_f => ?_
    have hcs := r3a_cs_regs hcsm
    have htr_tot : sf.trace = s.trace := htr_f.trans htr1
    have hfs_tot : sf.fs.files = s.fs.files := hfs_f.trans (congrArg FsState.files hfs1)
    let st' := M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st
    have henv' : EnvAt g' .postDispatch st' :=
      henv (rustDeallocEvents peerG.name.cap.toNat 1) (r3a_freeOnly_dealloc peerG.name.cap.toNat 1)
    exact r1c_sepWPp_weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hclose st' sf))
      (hrej sf st' g' .postDispatch
        ⟨hin_f, hcs.1.trans hx19_1, (fun h => nomatch h), htr_tot ▸ htr,
          r3a_hist_eq htr_tot hfs_tot hhist, hans⟩
        henv')

set_option maxHeartbeats 1600000 in
theorem r3a_tail_me_reject [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 4076)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' .postDispatch (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
        memRegion (runFsp s0 + 0x4d0#64) 120 ∗ r3a_restFrame (runFsp s0) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let tailF : SepProp := memRegion (g.res + 8#64) (runResSize - 8) ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗ memRegion g.call 56 ∗
    storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗
    memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ r3a_restFrame fsp ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ w : BitVec 64, g.res ↦₆₄ w) ∗
      (ownedBytes A.repAlloc meG.name.cap meG.name.ptr
        (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
        A.pool lim st s ∗ stackAt fsp sub ∗ tailF))
    (Entails.trans (sepConj_mono_left (r3a_protoAddr_free_me A.repAlloc (fsp + 0x260#64) meG))
      (by rw [r3a_res_split g.res]; exact Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))) ?_
  refine r3a_sepWPp_exists_left fun w_res => ?_
  have hpc : s.pc = runPcPlaced 4076 := hs.pc
  change s.pc = (blkPl_579).base + 4076#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hclose : ∀ (st' : M.σ) (sf : State),
      (g.res ↦₆₄ 0xffffffffffffffff#64) ∗ A.pool lim st' sf ∗ stackAt fsp sub ∗ tailF ⊢
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
          runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗
          r3a_restFrame fsp ∗ stackAt fsp sub ∗ A.pool lim st' sf ∗ anyHeap := by
    intro st' sf
    dsimp +zetaDelta only [runResAt]; exact Entails.of_eq (by sep_ac_rfl)
  by_cases hcap : meG.name.cap = 0
  · refine r1c_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_left (hcap ▸ ownedBytes_zero_entails_emp A.repAlloc _ _ _))) ?_
    rw [emp_sepConj]
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 4104) s (g.res ↦₆₄ w_res)
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores) ∧
          (P1 ⊢ (g.res ↦₆₄ 0xffffffffffffffff#64))) := by
      rw [runPcPlaced_eq]; rw [hcap] at hx21
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
        r3a_close_post)
    refine r3a_frame_seq_vm
      (F := A.pool lim st s ∗ stackAt fsp sub ∗ tailF)
      hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    exact r1c_sepWPp_weaken_pre (hclose st s1)
      (r3a_tail_peer_reject (g' := g') (peerG := peerG) hh hext hsub64
        ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        hx19_1 (htr1 ▸ htr) (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist) hans henv hrej)
  · have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s (g.res ↦₆₄ w_res)
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .lr = runPcPlaced 4104 ∧
            s1.readReg64 .x0 = meG.name.ptr ∧ s1.readReg64 .x1 = meG.name.cap ∧
            s1.readReg64 .x2 = 1#64 ∧ s1.readReg64 (.gpr 19#5) = g.stores) ∧
          (P1 ⊢ (g.res ↦₆₄ 0xffffffffffffffff#64))) := by
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [lsRustDeallocSymCli, lsρ, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
        r3a_close_post)
    refine r3a_frame_seq_vm
      (F := ownedBytes A.repAlloc meG.name.cap meG.name.ptr
          (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
        A.pool lim st s ∗ stackAt fsp sub ∗ tailF)
      hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1
        ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (Entails.of_eq (show _ =
        ownedBytes A.repAlloc meG.name.cap meG.name.ptr
          (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
          stackAt fsp sub ∗ A.pool lim st s1 ∗ ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ tailF) by
          (try dsimp +zetaDelta only); try sep_ac_rfl)) ?_
    refine r3a_owned_dealloc_call (retOff := 4104) hh hext hsub64 hcap hs.spAligned
      hfp1 hv1 hinv1 hpc1 hrun1 hsp1 hlr1 hx0_1 hx1_1 hx2_1
      fun sf hin_f hcsm htr_f hfs_f => ?_
    have hcs := r3a_cs_regs hcsm
    have htr_tot : sf.trace = s.trace := htr_f.trans htr1
    have hfs_tot : sf.fs.files = s.fs.files := hfs_f.trans (congrArg FsState.files hfs1)
    let st_me := M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st
    have henv_me : ∀ evs_peer, FreeOnlyEvs evs_peer →
        EnvAt g' .postDispatch (M.stepEvents evs_peer st_me) := by
      intro evs_peer hfp_ev
      rw [← M.stepEvents_append]
      exact henv (rustDeallocEvents meG.name.cap.toNat 1 ++ evs_peer)
        (r3a_freeOnly_append (r3a_freeOnly_dealloc meG.name.cap.toNat 1) hfp_ev)
    exact r1c_sepWPp_weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hclose st_me sf))
      (r3a_tail_peer_reject (g' := g') (peerG := peerG) hh hext hsub64 hin_f
        (hcs.1.trans hx19_1) (htr_tot ▸ htr) (r3a_hist_eq htr_tot hfs_tot hhist)
        hans henv_me hrej)

set_option maxHeartbeats 1600000 in
theorem r3a_accept_peer [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG : AddrGhost} {out : Bytes}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 3552)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, out)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' out (M.stepEvents evs_tail st))
    (hjoin : JoinKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        A.pool lim st s ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        vecU8 A.repAlloc (runFsp s0 + 0x208#64) out ∗
        memRegion (runFsp s0 + 0x260#64) 32 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
        r3a_restFrame (runFsp s0) ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x4d0#64) 120 ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let okTail : SepProp := vecU8 A.repAlloc (fsp + 0x208#64) out ∗
    memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp ∗
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
        (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
      ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
      addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool lim st s ∗ stackAt fsp sub ∗ okTail)
    (Entails.trans (sepConj_mono_left (r3a_protoAddr_free_peer A.repAlloc (fsp + 0x220#64) peerG))
      (by rw [hs.sp]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))) ?_
  have hpc : s.pc = runPcPlaced 3552 := hs.pc
  change s.pc = (blkPl_579).base + 3552#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have h32 : ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
      addrUpperAt (fsp + 0x230#64) peerG ⊢ memRegion (fsp + 0x220#64) 32 := by
    rw [hs.sp]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r3a_addrSlots_to_memRegion (fsp + 0x220#64) peerG.name.cap peerG.name.ptr peerG
  have hclose_join : ∀ (st' : M.σ) (sf : State),
      memRegion (fsp + 0x220#64) 32 ∗ A.pool lim st' sf ∗ stackAt fsp sub ∗ okTail ⊢
        joinMem (A.atState lim st' sf) g g' out s0 resStack := by
    intro st' sf
    dsimp +zetaDelta only [joinMem]
    rw [r3a_locals_join_rest (A.atState lim st' sf) (runFsp s0) out]
    simp only [RustCliAllocBudget.atState_pool, r3a_storesAt_atState, r3a_vecU8_atState]
    exact Entails.of_eq (by sep_ac_rfl)
  by_cases hpcap : peerG.name.cap = 0
  · refine r1c_sepWPp_weaken_pre
      (sepConj_mono_left (hpcap ▸ ownedBytes_zero_entails_emp A.repAlloc _ _ _)) ?_
    rw [emp_sepConj]
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 0xf8c) s
        (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          (P1 ⊢ ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))) := by
      rw [runPcPlaced_eq, hpcap]
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
        r3a_close_post)
    refine r3a_frame_seq_vm
      (F := addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool lim st s ∗ stackAt fsp sub ∗ okTail)
      hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    have henv0 : EnvAt g' out st := by
      simpa only [M.stepEvents_nil] using henv [] r3a_freeOnly_nil
    refine r1c_sepWPp_weaken_pre ?_
      (hjoin s1 st g' out
        ⟨⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩,
          hx19_1, hx20_1, htr1 ▸ htr,
          r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist, hans, hwr⟩
        henv0)
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left h32) (hclose_join st s1))
  · have hpbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hpcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .lr = runPcPlaced 0xf8c ∧
            s1.readReg64 .x0 = peerG.name.ptr ∧ s1.readReg64 .x1 = peerG.name.cap ∧
            s1.readReg64 .x2 = 1#64 ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          (P1 ⊢ ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))) := by
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [lsRustDeallocSymCli, lsρ, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
        r3a_close_post)
    refine r3a_frame_seq_vm
      (F := ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
          (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
        addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool lim st s ∗ stackAt fsp sub ∗ okTail)
      hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1
        ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (P' := ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
          (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
        stackAt fsp sub ∗ A.pool lim st s1 ∗ (memRegion (fsp + 0x220#64) 32 ∗ okTail))
      (Entails.trans
        (Entails.of_eq (show _ =
          (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            addrUpperAt (fsp + 0x230#64) peerG) ∗
          (ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
            (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
            stackAt fsp sub ∗ A.pool lim st s1 ∗ okTail) by sep_ac_rfl))
        (Entails.trans (sepConj_mono_left h32)
          (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)))) ?_
    refine r3a_owned_dealloc_call (retOff := 0xf8c) hh hext hsub64 hpcap hs.spAligned
      hfp1 hv1 hinv1 hpc1 hrun1 hsp1 hlr1 hx0_1 hx1_1 hx2_1
      fun sf hin_f hcsm htr_f hfs_f => ?_
    have hcs := r3a_cs_regs hcsm
    have htr_tot : sf.trace = s.trace := htr_f.trans htr1
    have hfs_tot : sf.fs.files = s.fs.files := hfs_f.trans (congrArg FsState.files hfs1)
    let st' := M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st
    have henv' : EnvAt g' out st' :=
      henv (rustDeallocEvents peerG.name.cap.toNat 1) (r3a_freeOnly_dealloc peerG.name.cap.toNat 1)
    exact r1c_sepWPp_weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hclose_join st' sf))
      (hjoin sf st' g' out
        ⟨hin_f, hcs.1.trans hx19_1, hcs.2.1.trans hx20_1, htr_tot ▸ htr,
          r3a_hist_eq htr_tot hfs_tot hhist, hans, hwr⟩
        henv')

set_option maxHeartbeats 1600000 in
theorem r3a_accept_me [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost} {out : Bytes}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 3532)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, out)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' out (M.stepEvents evs_tail st))
    (hjoin : JoinKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        A.pool lim st s ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        vecU8 A.repAlloc (runFsp s0 + 0x208#64) out ∗
        memRegion (runFsp s0 + 0x320#64) 48 ∗ r3a_restFrame (runFsp s0) ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x4d0#64) 120 ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let okTail : SepProp := protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    vecU8 A.repAlloc (fsp + 0x208#64) out ∗ memRegion (fsp + 0x260#64) 32 ∗
    memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp ∗ memRegion g.res runResSize ∗
    memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    runSaved s0 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := ownedBytes A.repAlloc meG.name.cap meG.name.ptr
        (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
      A.pool lim st s ∗ stackAt fsp sub ∗ okTail)
    (Entails.trans (sepConj_mono_left (r3a_protoAddr_free_me A.repAlloc (fsp + 0x260#64) meG))
      (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))) ?_
  have hpc : s.pc = runPcPlaced 3532 := hs.pc
  change s.pc = (blkPl_579).base + 3532#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hclose_peer : ∀ (st' : M.σ) (sf : State),
      A.pool lim st' sf ∗ stackAt fsp sub ∗ okTail ⊢
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗ A.pool lim st' sf ∗ stackAt fsp sub ∗
          vecU8 A.repAlloc (fsp + 0x208#64) out ∗ memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp ∗ memRegion g.res runResSize ∗
          memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ anyHeap :=
    fun _ _ => Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)
  by_cases hmcap : meG.name.cap = 0
  · refine r1c_sepWPp_weaken_pre
      (sepConj_mono_left (hmcap ▸ ownedBytes_zero_entails_emp A.repAlloc _ _ _)) ?_
    rw [emp_sepConj]
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 3552) s emp
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          (P1 ⊢ emp)) := by
      rw [runPcPlaced_eq]; rw [hmcap] at hx21
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.refl _⟩
        r3a_close_post)
    refine r3a_frame_seq_vm
      (F := A.pool lim st s ∗ stackAt fsp sub ∗ okTail)
      hs.inv (Entails.of_eq (by rw [emp_sepConj])) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    rw [emp_sepConj, ← A.pool_transport lim st s s1 hvm1]
    exact r1c_sepWPp_weaken_pre (hclose_peer st s1)
      (r3a_accept_peer (g' := g') (peerG := peerG) (out := out) hh hext hsub64
        ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        hx19_1 hx20_1 (htr1 ▸ htr) (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist)
        hans hwr henv hjoin)
  · have hmbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hmcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s emp
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .lr = runPcPlaced 3552 ∧
            s1.readReg64 .x0 = meG.name.ptr ∧ s1.readReg64 .x1 = meG.name.cap ∧
            s1.readReg64 .x2 = 1#64 ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          (P1 ⊢ emp)) := by
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [lsRustDeallocSymCli, lsρ, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.refl _⟩
        r3a_close_post)
    refine r3a_frame_seq_vm
      (F := ownedBytes A.repAlloc meG.name.cap meG.name.ptr
          (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
        A.pool lim st s ∗ stackAt fsp sub ∗ okTail)
      hs.inv (Entails.of_eq (by rw [emp_sepConj])) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1
        ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    rw [emp_sepConj, ← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (Entails.of_eq (show _ =
        ownedBytes A.repAlloc meG.name.cap meG.name.ptr
          (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
          stackAt fsp sub ∗ A.pool lim st s1 ∗ okTail by sep_ac_rfl)) ?_
    refine r3a_owned_dealloc_call (retOff := 3552) hh hext hsub64 hmcap hs.spAligned
      hfp1 hv1 hinv1 hpc1 hrun1 hsp1 hlr1 hx0_1 hx1_1 hx2_1
      fun sf hin_f hcsm htr_f hfs_f => ?_
    have hcs := r3a_cs_regs hcsm
    have htr_tot : sf.trace = s.trace := htr_f.trans htr1
    have hfs_tot : sf.fs.files = s.fs.files := hfs_f.trans (congrArg FsState.files hfs1)
    let st_me := M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st
    have henv_me : ∀ evs_peer, FreeOnlyEvs evs_peer →
        EnvAt g' out (M.stepEvents evs_peer st_me) := by
      intro evs_peer hfp_ev
      rw [← M.stepEvents_append]
      exact henv (rustDeallocEvents meG.name.cap.toNat 1 ++ evs_peer)
        (r3a_freeOnly_append (r3a_freeOnly_dealloc meG.name.cap.toNat 1) hfp_ev)
    exact r1c_sepWPp_weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hclose_peer st_me sf))
      (r3a_accept_peer (g' := g') (peerG := peerG) (out := out) hh hext hsub64 hin_f
        (hcs.1.trans hx19_1) (hcs.2.1.trans hx20_1) (htr_tot ▸ htr)
        (r3a_hist_eq htr_tot hfs_tot hhist) hans hwr henv_me hjoin)

set_option maxHeartbeats 1600000 in
theorem r3a_accept_tail [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost} {out : Bytes}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 3476)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, out)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' out (M.stepEvents evs_tail st))
    (hjoin : JoinKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (apiDecResultAt A.repAlloc (runFsp s0 + 0x320#64) (.ok out) ∗
        protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗
        r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let joinBase : SepProp := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    memRegion (fsp + 0x460#64) 112 ∗ memRegion (fsp + 0x4d0#64) 120 ∗
    memRegion (fsp + 0x23b0#64) 48 ∗ r3a_frameGaps fsp ∗ anyHeap
  dsimp only [apiDecResultAt, vecResultAt, r3a_restFrame]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ V : SepProp,
        ⌜cap.toNat < 2 ^ 63 ∧
          (∀ dst : BitVec 64, r3a_words64At dst [cap, ptr, BitVec.ofNat 64 out.length] ∗ V ⊢
            vecU8 A.repAlloc dst out)⌝ ∗
        r3a_words64At (fsp + 0x328#64) [cap, ptr, BitVec.ofNat 64 out.length] ∗ V) ∗
      (memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x380#64) 16 ∗
        ((fsp + 0x320#64) ↦₆₄ okTagVec) ∗ memRegion (fsp + 0x340#64) 16 ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        stackAt fsp sub ∗ A.pool lim st s ∗ joinBase))
    (Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
        (r3a_vecU8_open A.repAlloc (runFsp s0 + 0x328#64) out))))
      (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))) ?_
  simp only [sepExists_sepConj_left]
  refine r1c_sepWPp_exists_left fun cap => r1c_sepWPp_exists_left fun ptr =>
    r1c_sepWPp_exists_left fun V => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine r1c_sepWPp_pure_left fun ⟨_hcap_lt, hvec_close⟩ => ?_
  let keepF : SepProp :=
    r3a_words64At (fsp + 0x328#64) [cap, ptr, BitVec.ofNat 64 out.length] ∗
      ((fsp + 0x320#64) ↦₆₄ okTagVec) ∗ V ∗ memRegion (fsp + 0x340#64) 16 ∗
      protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
      protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
      stackAt fsp sub ∗ A.pool lim st s ∗ joinBase
  refine r3a_sepWPp_bind
    (A0 := memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x380#64) 16) (F := keepF) ?_ |>
    r1c_sepWPp_weaken_pre (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
  intro R hm; rw [sepConj_assoc] at hm
  obtain ⟨ws208, hlen208, hm⟩ := r3a_open_words 3 (fsp + 0x208#64) hm
  rcases ws208 with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | _⟩⟩⟩ <;> try (simp at hlen208; done)
  obtain ⟨ws380, hlen380, hm⟩ := r3a_open_words 2 (fsp + 0x380#64)
    (Q := r3a_words64At (fsp + 0x208#64) [d0, d1, d2] ∗ (keepF ∗ R))
    (Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm)
  rcases ws380 with _ | ⟨u0, _ | ⟨u1, _ | _⟩⟩ <;> try (simp at hlen380; done)
  refine ⟨r3a_words64At (fsp + 0x208#64) [d0, d1, d2] ∗ r3a_words64At (fsp + 0x380#64) [u0, u1],
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm, ?_⟩
  have hpc : s.pc = runPcPlaced 3476 := hs.pc
  change s.pc = (blkPl_579).base + 3476#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hneq1 : (cap + 1#64 == 0#64) = false := by rw [beq_eq_false_iff_ne]; bv_omega
  have hneq2 : (cap == -1#64) = false := by rw [beq_eq_false_iff_ne]; bv_omega
  let P_step : SepProp :=
    ((s.sp + 0x320#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x328#64) ↦₆₄ cap) ∗
      ((s.sp + 0x330#64) ↦₆₄ ptr) ∗ ((s.sp + 0x338#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
      ((s.sp + 0x380#64) ↦₆₄ u0) ∗ ((s.sp + 0x388#64) ↦₆₄ u1) ∗
      ((s.sp + 0x208#64) ↦₆₄ d0) ∗ ((s.sp + 0x210#64) ↦₆₄ d1) ∗ ((s.sp + 0x218#64) ↦₆₄ d2)
  let P_after : SepProp :=
    ((s.sp + 0x320#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x328#64) ↦₆₄ cap) ∗
      ((s.sp + 0x330#64) ↦₆₄ ptr) ∗ ((s.sp + 0x338#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
      ((s.sp + 0x380#64) ↦₆₄ ptr) ∗ ((s.sp + 0x388#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
      ((s.sp + 0x208#64) ↦₆₄ cap) ∗ ((s.sp + 0x210#64) ↦₆₄ ptr) ∗
      ((s.sp + 0x218#64) ↦₆₄ BitVec.ofNat 64 out.length)
  have hstep : SepWP (runProgPlaced H) (runPcPlaced 3532) s P_step
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
          s1.readReg64 (.gpr 21#5) = meG.name.cap ∧ s1.readReg64 (.gpr 28#5) = meG.name.ptr) ∧
        (P1 ⊢ P_after)) := by
    rw [runPcPlaced_eq]
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hP_in :
      (r3a_words64At (fsp + 0x208#64) [d0, d1, d2] ∗ r3a_words64At (fsp + 0x380#64) [u0, u1]) ∗
        keepF ⊢
      P_step ∗ (V ∗ memRegion (fsp + 0x340#64) 16 ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        stackAt fsp sub ∗ A.pool lim st s ∗ joinBase) := by
    dsimp +zetaDelta only [keepF, okTagVec, r3a_words64At, P_step]
    rw [hs.sp]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
    exact Entails.of_eq (by sep_ac_rfl)
  refine r3a_frame_seq_vm hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1
      ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1, hx21_1, hx28_1⟩ => ?_
  rw [← A.pool_transport lim st s s1 hvm1]
  have hpack_slots :
      P_after ∗ (V ∗ memRegion (fsp + 0x340#64) 16 ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        stackAt fsp sub ∗ A.pool lim st s1 ∗ joinBase) ⊢
      protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        A.pool lim st s1 ∗ stackAt fsp sub ∗
        vecU8 A.repAlloc (fsp + 0x208#64) out ∗
        memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (fsp + 0x4d0#64) 120 ∗ anyHeap := by
    dsimp +zetaDelta only [P_after]; rw [hs.sp]
    have hv208 : ((fsp + 0x208#64) ↦₆₄ cap) ∗ ((fsp + 0x210#64) ↦₆₄ ptr) ∗
        ((fsp + 0x218#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗ V ⊢
        vecU8 A.repAlloc (fsp + 0x208#64) out := by
      simpa only [r3a_words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc] using
        hvec_close (fsp + 0x208#64)
    have hm320 : ((fsp + 0x320#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 0x328#64) ↦₆₄ cap) ∗
        ((fsp + 0x330#64) ↦₆₄ ptr) ∗ ((fsp + 0x338#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
        memRegion (fsp + 0x340#64) 16 ⊢ memRegion (fsp + 0x320#64) 48 := by
      have hw4 := r3a_words_to_memRegion [0xfffffffffffffffe#64, cap, ptr, BitVec.ofNat 64 out.length]
        (fsp + 0x320#64) 32
      dsimp only [r3a_words64At] at hw4
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hw4
      have hsp48 : memRegion (fsp + 0x320#64) 32 ∗ memRegion (fsp + 0x340#64) 16 =
          memRegion (fsp + 0x320#64) 48 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          (ProofLib.memRegion_split (fsp + 0x320#64) 32 16 (by decide)).symm
      rw [← hsp48]; exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_left hw4)
    have hm380 : ((fsp + 0x380#64) ↦₆₄ ptr) ∗ ((fsp + 0x388#64) ↦₆₄ BitVec.ofNat 64 out.length) ⊢
        memRegion (fsp + 0x380#64) 16 := by
      simpa only [r3a_words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] using
        r3a_words_to_memRegion [ptr, BitVec.ofNat 64 out.length] (fsp + 0x380#64) 16
    dsimp +zetaDelta only [r3a_restFrame] at hv208 hm320 hm380 ⊢
    exact Entails.trans (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
      (Entails.trans
        (sepConj_mono hv208 (sepConj_mono hm320 (sepConj_mono hm380
          (Entails.refl (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
            protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1 ∗ joinBase)))))
        (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)))
  exact r1c_sepWPp_weaken_pre hpack_slots
    (r3a_accept_me (g' := g') (peerG := peerG) (meG := meG) (out := out) hh hext hsub64
      ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
      hx19_1 hx20_1 hx21_1 hx28_1 (htr1 ▸ htr)
      (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist) hans hwr henv hjoin)


/-! ## 5. `CodeOk`-Parametric Combinators and Epilogue Tails (`[LsCodeInv CodeOk]`) -/

theorem r3a_frame_seq_vm_codeOk [LibsignalPlacement]
    {CodeOk : Memory → Prop} [hCI : CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P_in P P' F : SepProp} {post : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem) (hP : P_in ⊢ P ∗ F)
    (h : SepWP prog mid s P (fun s1 P1 => VmPreserved s s1 ∧ post s1 ∧ (P1 ⊢ P')))
    (hk : ∀ s1 : State, VmPreserved s s1 → CodeOk s1.mem → s1.pc = mid →
      s1.status = .Running → post s1 → SepWPp prog ret s1 (P' ∗ F) Q Qp oom) :
    SepWPp prog ret s P_in Q Qp oom := by
  intro R hm hL
  have hm0 : s.mem ⊨ P ∗ (F ∗ R) :=
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  rcases h.elim hm0 hL with ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hvm1, hpost1, hent1⟩ | ⟨_, hfalse⟩⟩
  · have hm1' : s1.mem ⊨ (P' ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent1) hm1
    obtain ⟨sf, hsteps2, hout⟩ :=
      hk s1 hvm1 (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) hpc1 hrun1 hpost1 R hm1'
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem r3a_call_lscro_codeOk [LibsignalPlacement]
    {CodeOk : Memory → Prop} [hCI : CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {α : Type} {prog : Program}
    {callee retAddr ret : BitVec 64} {spec : Spec α} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (x : α)
    (hcall : subroutine_ok prog callee (withLsCodeRoLoaded lsmpl spec))
    (hinv : CodeOk s.mem)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = retAddr)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sm : State,
      Steps prog s sm →
      CodeOk sm.mem →
      sm.pc = retAddr →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  have hpre :
      s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) :=
    CryptoVerification.SignalSession.Cli.Store.PlacedCommon.satisfies_lscro_pre (hCI.toRoCl hinv) hm_pre
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) hpcm hrunm hspm hcsm R hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

theorem r3a_call_dealloc_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s1 : State}
    {ptr : BitVec 64} {sz resStack retOff : Nat} {Rest : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hsp0 : s0.spAligned = true)
    (hinv1 : CodeOk s1.mem)
    (hpc1 : s1.pc = lsρ lsRustDeallocSymCli)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = runFsp s0)
    (hlr1 : s1.readReg64 .lr = runPcPlaced retOff)
    (hx0 : s1.readReg64 .x0 = ptr)
    (hx1 : (s1.readReg64 .x1).toNat = sz)
    (hx2 : s1.readReg64 .x2 = 1#64)
    (hlay : CryptoVerification.RustHeap.LayoutOk sz 1)
    (hnext : ∀ s2 : State,
      CodeOk s2.mem → s2.pc = runPcPlaced retOff → s2.status = .Running →
      s2.sp = runFsp s0 → CalleeSavedPreserved s1 s2 →
      s2.fs = s1.fs → s2.trace = s1.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents sz 1) st) s2 ∗ Rest)
        Q Qp oom)
    (hlr_ls : LsRetAddr624 (runPcPlaced retOff) := by
      first | assumption | simp (config := { decide := true })
        [_root_.CryptoVerification.SignalSession.Cli.RunCompose.runPcPlaced, wp_norm, arm64_norm,
         _root_.LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen, *]) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
      ((A.live ptr sz 1 ∗ memRegion ptr sz) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1 ∗ Rest)
      Q Qp oom := by
  refine r3a_call_lscro_codeOk
    (F := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
      (resStack - runFrame - extHookStack) ∗ Rest)
    (ptr, sz, 1, st)
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cHelpersPlacedBudget.r1c_dealloc_ok hh)
    hinv1 hpc1 hrun1
    (r1c_spAligned hsp0 hsp1) hlr1 ?_
    (hnext := fun s2 _ hinv2 hpc2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [Spec.keepsFs, LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    have hpure : s1.readReg64 .x0 = ptr ∧ (s1.readReg64 .x1).toNat = sz ∧
        (s1.readReg64 .x2).toNat = 1 ∧ LibsignalBinary.Heap.RustLayoutOk sz 1 ∧
        LsRetAddr624 (s1.readReg64 .lr) :=
      ⟨hx0, hx1, by rw [hx2]; decide, ⟨hlay, by decide⟩, hlr1 ▸ hlr_ls⟩
    rw [hsp1, CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers.r1c_stackAt_split_ge (runFsp s0) hext_le hsub64]
    conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right hpure ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · refine r1c_sepWPp_weaken_pre
      (P' := ⌜s2.fs = s1.fs ∧ s2.trace = s1.trace⌝ ∗
        (stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents sz 1) st) s2 ∗ Rest))
      (by
        dsimp only [Spec.keepsFs, LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        rw [hsp1, CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers.r1c_stackAt_split_ge (runFsp s0) hext_le hsub64]
        simp only [← sepConj_assoc, pure_sepConj_pure]
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    apply r1c_sepWPp_pure_left; rintro ⟨hfs2, htr2⟩
    exact hnext s2 hinv2 hpc2 hrun2 (hsp2.trans hsp1) hcs2 hfs2 htr2

theorem r3a_owned_dealloc_call_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s1 : State} {resStack retOff : Nat}
    {cap ptr len : BitVec 64} {bs : List (BitVec 8)} {Rest : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hcap : cap ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hfp1 : s1.readReg64 .fp = s0.sp - 0x60#64)
    (hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hinv1 : CodeOk s1.mem)
    (hpc1 : s1.pc = lsρ lsRustDeallocSymCli)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = runFsp s0)
    (hlr1 : s1.readReg64 .lr = runPcPlaced retOff)
    (hx0 : s1.readReg64 .x0 = ptr)
    (hx1 : s1.readReg64 .x1 = cap)
    (hx2 : s1.readReg64 .x2 = 1#64)
    (hk : ∀ s2 : State, InRunPlaced CodeOk s0 s2 retOff →
      CalleeSavedPreserved s1 s2 → s2.trace = s1.trace → s2.fs.files = s1.fs.files →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) s2 ∗ Rest)
        Q Qp oom)
    (hlr_ls : LsRetAddr624 (runPcPlaced retOff) := by
      first | assumption | simp (config := { decide := true })
        [_root_.CryptoVerification.SignalSession.Cli.RunCompose.runPcPlaced, wp_norm, arm64_norm,
         _root_.LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen, *]) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
      (ownedBytes A.repAlloc cap ptr len bs ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1 ∗ Rest)
      Q Qp oom := by
  refine r1c_sepWPp_weaken_pre (sepConj_mono_left (ownedBytes_dealloc A.repAlloc hcap)) ?_
  rw [sepConj_assoc]
  refine r1c_sepWPp_pure_left fun hlay => ?_
  refine r3a_call_dealloc_codeOk hh hext_le hsub64 hsp0 hinv1 hpc1 hrun1 hsp1 hlr1
    hx0 (congrArg BitVec.toNat hx1) hx2 hlay
    (fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
  have hcs := r3a_cs_regs hcs2
  have hin2 : InRunPlaced CodeOk s0 s2 retOff :=
    ⟨hpc2, hrun2, hsp2, hcs.2.2.2.2.2.1.trans hfp1, hinv2, hcs.2.2.2.2.2.2.trans hv1, hsp0⟩
  exact hk s2 hin2 hcs2 htr2 (congrArg FsState.files hfs2)

theorem r3a_drop_spe_call_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {k : SpeOwned} {speAddr : BitVec 64} {sub : Nat}
    {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (h32 : 32 + extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hinv : CodeOk s.mem)
    (hpc : s.pc = (blkPl_553).base)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = runPcPlaced 4076)
    (hsp : s.sp = runFsp s0)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hal0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = speAddr)
    (hk : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      Steps (runProgPlaced H) s sf →
      InRunPlaced CodeOk s0 sf 4076 →
      CalleeSavedPreserved s sf →
      sf.trace = s.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (memRegion speAddr 48 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt (runFsp s0) sub ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (speOwnedAt A.repAlloc speAddr k ∗ A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F)
      Q Qp oom := by
  have hd := hdrop sub h32 hsub64
  refine r3a_call_lscro_codeOk (⟨speAddr, k⟩, st) hd hinv hpc hrun hsp_al hlr (F := F) ?_
    (hnext := fun sf hsteps hinv_f hpcm hrunm hspm hcsm => ?_)
  · dsimp only [dropSpeOwnedSpec]; rw [hsp]; simp only [sepConj_assoc]
    exact Entails.pure_right
      ⟨hx0, by rw [show Reg.x30 = Reg.lr from rfl, hlr]
               exact lsRetAddr624_base_add 579 4076#64 (by decide) (by decide)⟩
      (Entails.of_eq (by sep_ac_rfl))
  · dsimp only [dropSpeOwnedSpec]
    rw [sepExists_sepConj_left]
    refine r1c_sepWPp_exists_left fun evs => ?_
    simp only [sepConj_assoc]
    refine r1c_sepWPp_pure_left fun ⟨htr_f, hfree⟩ => ?_
    have hcs := r3a_cs_regs hcsm; rw [hsp]
    exact hk sf evs hfree hsteps
      ⟨hpcm, hrunm, hspm.trans hsp, hcs.2.2.2.2.2.1.trans hfp, hinv_f,
        hcs.2.2.2.2.2.2.trans hv, hal0⟩
      hcsm htr_f

/-! ## 6. `CodeOk`-Parametric Reject and Accept Epilogue Tails -/

set_option maxHeartbeats 1600000 in
theorem r3a_tail_peer_reject_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG : AddrGhost}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 4104)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' .postDispatch (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x260#64) 32 ∗
        memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗
        r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let tailF : SepProp := runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
    storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗
    memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ r3a_restFrame fsp ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
        (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
      ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
      addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tailF)
    (Entails.trans (sepConj_mono_left (r3a_protoAddr_free_peer A.repAlloc (fsp + 0x220#64) peerG))
      (by rw [hs.sp]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))) ?_
  have hpc : s.pc = runPcPlaced 4104 := hs.pc
  change s.pc = (blkPl_579).base + 4104#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have h32 : ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
      addrUpperAt (fsp + 0x230#64) peerG ⊢ memRegion (fsp + 0x220#64) 32 := by
    rw [hs.sp]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r3a_addrSlots_to_memRegion (fsp + 0x220#64) peerG.name.cap peerG.name.ptr peerG
  have hclose : ∀ (st' : M.σ) (sf : State),
      memRegion (fsp + 0x220#64) 32 ∗ A.pool lim st' sf ∗ stackAt fsp sub ∗ tailF ⊢
        rejectMem (A.atState lim st' sf) g g' .postDispatch s0 resStack := by
    intro st' sf
    dsimp +zetaDelta only [rejectMem]
    simp only [RustCliAllocBudget.atState_pool, r3a_storesAt_atState,
      r3a_runResAt_some_none_atState]
    rw [r3a_locals_empty_rest (runFsp s0)]
    exact Entails.of_eq (by sep_ac_rfl)
  by_cases hcap : peerG.name.cap = 0
  · refine r1c_sepWPp_weaken_pre
      (sepConj_mono_left (hcap ▸ ownedBytes_zero_entails_emp A.repAlloc _ _ _)) ?_
    rw [emp_sepConj]
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 0x2c7c) s
        (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores) ∧
          (P1 ⊢ ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))) := by
      rw [runPcPlaced_eq, hcap]
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
        r3a_close_post)
    refine r3a_frame_seq_vm_codeOk
      (F := addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tailF)
      hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 _ hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    have hpc1_rej : s1.pc = runPcPlaced RejectKind.postDispatch.pcOff := by assumption
    have hin1 : InRunPlaced CodeOk s0 s1 RejectKind.postDispatch.pcOff :=
      ⟨hpc1_rej, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
    have henv0 : EnvAt g' .postDispatch st := by
      simpa only [M.stepEvents_nil] using henv [] r3a_freeOnly_nil
    refine r1c_sepWPp_weaken_pre ?_
      (hrej s1 st g' .postDispatch
        ⟨hin1, hx19_1, (fun h => nomatch h), htr1 ▸ htr,
          r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist, hans⟩
        henv0)
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left h32) (hclose st s1))
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .lr = runPcPlaced 0x2c7c ∧
            s1.readReg64 .x0 = peerG.name.ptr ∧ s1.readReg64 .x1 = peerG.name.cap ∧
            s1.readReg64 .x2 = 1#64 ∧ s1.readReg64 (.gpr 19#5) = g.stores) ∧
          (P1 ⊢ ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))) := by
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [lsRustDeallocSymCli, lsρ, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
        r3a_close_post)
    refine r3a_frame_seq_vm_codeOk
      (F := ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
          (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
        addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tailF)
      hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1
        ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (P' := ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
          (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
        stackAt fsp sub ∗ A.pool lim st s1 ∗ (memRegion (fsp + 0x220#64) 32 ∗ tailF))
      (Entails.trans
        (Entails.of_eq (show _ =
          (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            addrUpperAt (fsp + 0x230#64) peerG) ∗
          (ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
            (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
            stackAt fsp sub ∗ A.pool lim st s1 ∗ tailF) by sep_ac_rfl))
        (Entails.trans (sepConj_mono_left h32)
          (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)))) ?_
    refine r3a_owned_dealloc_call_codeOk (retOff := 0x2c7c) hh hext hsub64 hcap hs.spAligned
      hfp1 hv1 hinv1 hpc1 hrun1 hsp1 hlr1 hx0_1 hx1_1 hx2_1
      fun sf hin_f hcsm htr_f hfs_f => ?_
    have hcs := r3a_cs_regs hcsm
    have htr_tot : sf.trace = s.trace := htr_f.trans htr1
    have hfs_tot : sf.fs.files = s.fs.files := hfs_f.trans (congrArg FsState.files hfs1)
    let st' := M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st
    have henv' : EnvAt g' .postDispatch st' :=
      henv (rustDeallocEvents peerG.name.cap.toNat 1) (r3a_freeOnly_dealloc peerG.name.cap.toNat 1)
    exact r1c_sepWPp_weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hclose st' sf))
      (hrej sf st' g' .postDispatch
        ⟨hin_f, hcs.1.trans hx19_1, (fun h => nomatch h), htr_tot ▸ htr,
          r3a_hist_eq htr_tot hfs_tot hhist, hans⟩
        henv')

set_option maxHeartbeats 1600000 in
theorem r3a_tail_me_reject_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 4076)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' .postDispatch (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
        memRegion (runFsp s0 + 0x4d0#64) 120 ∗ r3a_restFrame (runFsp s0) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let tailF : SepProp := memRegion (g.res + 8#64) (runResSize - 8) ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗ memRegion g.call 56 ∗
    storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗
    memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ r3a_restFrame fsp ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ w : BitVec 64, g.res ↦₆₄ w) ∗
      (ownedBytes A.repAlloc meG.name.cap meG.name.ptr
        (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
        A.pool lim st s ∗ stackAt fsp sub ∗ tailF))
    (Entails.trans (sepConj_mono_left (r3a_protoAddr_free_me A.repAlloc (fsp + 0x260#64) meG))
      (by rw [r3a_res_split g.res]; exact Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))) ?_
  refine r3a_sepWPp_exists_left fun w_res => ?_
  have hpc : s.pc = runPcPlaced 4076 := hs.pc
  change s.pc = (blkPl_579).base + 4076#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hclose : ∀ (st' : M.σ) (sf : State),
      (g.res ↦₆₄ 0xffffffffffffffff#64) ∗ A.pool lim st' sf ∗ stackAt fsp sub ∗ tailF ⊢
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
          runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗
          r3a_restFrame fsp ∗ stackAt fsp sub ∗ A.pool lim st' sf ∗ anyHeap := by
    intro st' sf
    dsimp +zetaDelta only [runResAt]; exact Entails.of_eq (by sep_ac_rfl)
  by_cases hcap : meG.name.cap = 0
  · refine r1c_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_left (hcap ▸ ownedBytes_zero_entails_emp A.repAlloc _ _ _))) ?_
    rw [emp_sepConj]
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 4104) s (g.res ↦₆₄ w_res)
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores) ∧
          (P1 ⊢ (g.res ↦₆₄ 0xffffffffffffffff#64))) := by
      rw [runPcPlaced_eq]; rw [hcap] at hx21
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
        r3a_close_post)
    refine r3a_frame_seq_vm_codeOk
      (F := A.pool lim st s ∗ stackAt fsp sub ∗ tailF)
      hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    exact r1c_sepWPp_weaken_pre (hclose st s1)
      (r3a_tail_peer_reject_codeOk (g' := g') (peerG := peerG) hh hext hsub64
        ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        hx19_1 (htr1 ▸ htr) (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist) hans henv hrej)
  · have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s (g.res ↦₆₄ w_res)
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .lr = runPcPlaced 4104 ∧
            s1.readReg64 .x0 = meG.name.ptr ∧ s1.readReg64 .x1 = meG.name.cap ∧
            s1.readReg64 .x2 = 1#64 ∧ s1.readReg64 (.gpr 19#5) = g.stores) ∧
          (P1 ⊢ (g.res ↦₆₄ 0xffffffffffffffff#64))) := by
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [lsRustDeallocSymCli, lsρ, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
        r3a_close_post)
    refine r3a_frame_seq_vm_codeOk
      (F := ownedBytes A.repAlloc meG.name.cap meG.name.ptr
          (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
        A.pool lim st s ∗ stackAt fsp sub ∗ tailF)
      hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1
        ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (Entails.of_eq (show _ =
        ownedBytes A.repAlloc meG.name.cap meG.name.ptr
          (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
          stackAt fsp sub ∗ A.pool lim st s1 ∗ ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ tailF) by
          (try dsimp +zetaDelta only); try sep_ac_rfl)) ?_
    refine r3a_owned_dealloc_call_codeOk (retOff := 4104) hh hext hsub64 hcap hs.spAligned
      hfp1 hv1 hinv1 hpc1 hrun1 hsp1 hlr1 hx0_1 hx1_1 hx2_1
      fun sf hin_f hcsm htr_f hfs_f => ?_
    have hcs := r3a_cs_regs hcsm
    have htr_tot : sf.trace = s.trace := htr_f.trans htr1
    have hfs_tot : sf.fs.files = s.fs.files := hfs_f.trans (congrArg FsState.files hfs1)
    let st_me := M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st
    have henv_me : ∀ evs_peer, FreeOnlyEvs evs_peer →
        EnvAt g' .postDispatch (M.stepEvents evs_peer st_me) := by
      intro evs_peer hfp_ev
      rw [← M.stepEvents_append]
      exact henv (rustDeallocEvents meG.name.cap.toNat 1 ++ evs_peer)
        (r3a_freeOnly_append (r3a_freeOnly_dealloc meG.name.cap.toNat 1) hfp_ev)
    exact r1c_sepWPp_weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hclose st_me sf))
      (r3a_tail_peer_reject_codeOk (g' := g') (peerG := peerG) hh hext hsub64 hin_f
        (hcs.1.trans hx19_1) (htr_tot ▸ htr) (r3a_hist_eq htr_tot hfs_tot hhist)
        hans henv_me hrej)

set_option maxHeartbeats 1600000 in
theorem r3a_accept_peer_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG : AddrGhost} {out : Bytes}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 3552)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, out)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' out (M.stepEvents evs_tail st))
    (hjoin : JoinKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        A.pool lim st s ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        vecU8 A.repAlloc (runFsp s0 + 0x208#64) out ∗
        memRegion (runFsp s0 + 0x260#64) 32 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
        r3a_restFrame (runFsp s0) ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x4d0#64) 120 ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let okTail : SepProp := vecU8 A.repAlloc (fsp + 0x208#64) out ∗
    memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp ∗
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
        (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
      ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
      addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool lim st s ∗ stackAt fsp sub ∗ okTail)
    (Entails.trans (sepConj_mono_left (r3a_protoAddr_free_peer A.repAlloc (fsp + 0x220#64) peerG))
      (by rw [hs.sp]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))) ?_
  have hpc : s.pc = runPcPlaced 3552 := hs.pc
  change s.pc = (blkPl_579).base + 3552#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have h32 : ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
      addrUpperAt (fsp + 0x230#64) peerG ⊢ memRegion (fsp + 0x220#64) 32 := by
    rw [hs.sp]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r3a_addrSlots_to_memRegion (fsp + 0x220#64) peerG.name.cap peerG.name.ptr peerG
  have hclose_join : ∀ (st' : M.σ) (sf : State),
      memRegion (fsp + 0x220#64) 32 ∗ A.pool lim st' sf ∗ stackAt fsp sub ∗ okTail ⊢
        joinMem (A.atState lim st' sf) g g' out s0 resStack := by
    intro st' sf
    dsimp +zetaDelta only [joinMem]
    rw [r3a_locals_join_rest (A.atState lim st' sf) (runFsp s0) out]
    simp only [RustCliAllocBudget.atState_pool, r3a_storesAt_atState, r3a_vecU8_atState]
    exact Entails.of_eq (by sep_ac_rfl)
  by_cases hpcap : peerG.name.cap = 0
  · refine r1c_sepWPp_weaken_pre
      (sepConj_mono_left (hpcap ▸ ownedBytes_zero_entails_emp A.repAlloc _ _ _)) ?_
    rw [emp_sepConj]
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 0xf8c) s
        (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          (P1 ⊢ ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))) := by
      rw [runPcPlaced_eq, hpcap]
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
        r3a_close_post)
    refine r3a_frame_seq_vm_codeOk
      (F := addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool lim st s ∗ stackAt fsp sub ∗ okTail)
      hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    have henv0 : EnvAt g' out st := by
      simpa only [M.stepEvents_nil] using henv [] r3a_freeOnly_nil
    refine r1c_sepWPp_weaken_pre ?_
      (hjoin s1 st g' out
        ⟨⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩,
          hx19_1, hx20_1, htr1 ▸ htr,
          r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist, hans, hwr⟩
        henv0)
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left h32) (hclose_join st s1))
  · have hpbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hpcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .lr = runPcPlaced 0xf8c ∧
            s1.readReg64 .x0 = peerG.name.ptr ∧ s1.readReg64 .x1 = peerG.name.cap ∧
            s1.readReg64 .x2 = 1#64 ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          (P1 ⊢ ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr))) := by
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [lsRustDeallocSymCli, lsρ, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
        r3a_close_post)
    refine r3a_frame_seq_vm_codeOk
      (F := ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
          (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
        addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool lim st s ∗ stackAt fsp sub ∗ okTail)
      hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1
        ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (P' := ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
          (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
        stackAt fsp sub ∗ A.pool lim st s1 ∗ (memRegion (fsp + 0x220#64) 32 ∗ okTail))
      (Entails.trans
        (Entails.of_eq (show _ =
          (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            addrUpperAt (fsp + 0x230#64) peerG) ∗
          (ownedBytes A.repAlloc peerG.name.cap peerG.name.ptr
            (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗
            stackAt fsp sub ∗ A.pool lim st s1 ∗ okTail) by sep_ac_rfl))
        (Entails.trans (sepConj_mono_left h32)
          (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)))) ?_
    refine r3a_owned_dealloc_call_codeOk (retOff := 0xf8c) hh hext hsub64 hpcap hs.spAligned
      hfp1 hv1 hinv1 hpc1 hrun1 hsp1 hlr1 hx0_1 hx1_1 hx2_1
      fun sf hin_f hcsm htr_f hfs_f => ?_
    have hcs := r3a_cs_regs hcsm
    have htr_tot : sf.trace = s.trace := htr_f.trans htr1
    have hfs_tot : sf.fs.files = s.fs.files := hfs_f.trans (congrArg FsState.files hfs1)
    let st' := M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st
    have henv' : EnvAt g' out st' :=
      henv (rustDeallocEvents peerG.name.cap.toNat 1) (r3a_freeOnly_dealloc peerG.name.cap.toNat 1)
    exact r1c_sepWPp_weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hclose_join st' sf))
      (hjoin sf st' g' out
        ⟨hin_f, hcs.1.trans hx19_1, hcs.2.1.trans hx20_1, htr_tot ▸ htr,
          r3a_hist_eq htr_tot hfs_tot hhist, hans, hwr⟩
        henv')

set_option maxHeartbeats 1600000 in
theorem r3a_accept_me_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost} {out : Bytes}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 3532)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, out)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' out (M.stepEvents evs_tail st))
    (hjoin : JoinKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        A.pool lim st s ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        vecU8 A.repAlloc (runFsp s0 + 0x208#64) out ∗
        memRegion (runFsp s0 + 0x320#64) 48 ∗ r3a_restFrame (runFsp s0) ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x4d0#64) 120 ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let okTail : SepProp := protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    vecU8 A.repAlloc (fsp + 0x208#64) out ∗ memRegion (fsp + 0x260#64) 32 ∗
    memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp ∗ memRegion g.res runResSize ∗
    memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    runSaved s0 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := ownedBytes A.repAlloc meG.name.cap meG.name.ptr
        (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
      A.pool lim st s ∗ stackAt fsp sub ∗ okTail)
    (Entails.trans (sepConj_mono_left (r3a_protoAddr_free_me A.repAlloc (fsp + 0x260#64) meG))
      (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))) ?_
  have hpc : s.pc = runPcPlaced 3532 := hs.pc
  change s.pc = (blkPl_579).base + 3532#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hclose_peer : ∀ (st' : M.σ) (sf : State),
      A.pool lim st' sf ∗ stackAt fsp sub ∗ okTail ⊢
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗ A.pool lim st' sf ∗ stackAt fsp sub ∗
          vecU8 A.repAlloc (fsp + 0x208#64) out ∗ memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp ∗ memRegion g.res runResSize ∗
          memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ anyHeap :=
    fun _ _ => Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)
  by_cases hmcap : meG.name.cap = 0
  · refine r1c_sepWPp_weaken_pre
      (sepConj_mono_left (hmcap ▸ ownedBytes_zero_entails_emp A.repAlloc _ _ _)) ?_
    rw [emp_sepConj]
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 3552) s emp
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          (P1 ⊢ emp)) := by
      rw [runPcPlaced_eq]; rw [hmcap] at hx21
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.refl _⟩
        r3a_close_post)
    refine r3a_frame_seq_vm_codeOk
      (F := A.pool lim st s ∗ stackAt fsp sub ∗ okTail)
      hs.inv (Entails.of_eq (by rw [emp_sepConj])) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    rw [emp_sepConj, ← A.pool_transport lim st s s1 hvm1]
    exact r1c_sepWPp_weaken_pre (hclose_peer st s1)
      (r3a_accept_peer_codeOk (g' := g') (peerG := peerG) (out := out) hh hext hsub64
        ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        hx19_1 hx20_1 (htr1 ▸ htr) (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist)
        hans hwr henv hjoin)
  · have hmbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hmcap
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s emp
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .lr = runPcPlaced 3552 ∧
            s1.readReg64 .x0 = meG.name.ptr ∧ s1.readReg64 .x1 = meG.name.cap ∧
            s1.readReg64 .x2 = 1#64 ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          (P1 ⊢ emp)) := by
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [lsRustDeallocSymCli, lsρ, wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.refl _⟩
        r3a_close_post)
    refine r3a_frame_seq_vm_codeOk
      (F := ownedBytes A.repAlloc meG.name.cap meG.name.ptr
          (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
        A.pool lim st s ∗ stackAt fsp sub ∗ okTail)
      hs.inv (Entails.of_eq (by rw [emp_sepConj])) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1
        ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    rw [emp_sepConj, ← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (Entails.of_eq (show _ =
        ownedBytes A.repAlloc meG.name.cap meG.name.ptr
          (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗
          stackAt fsp sub ∗ A.pool lim st s1 ∗ okTail by sep_ac_rfl)) ?_
    refine r3a_owned_dealloc_call_codeOk (retOff := 3552) hh hext hsub64 hmcap hs.spAligned
      hfp1 hv1 hinv1 hpc1 hrun1 hsp1 hlr1 hx0_1 hx1_1 hx2_1
      fun sf hin_f hcsm htr_f hfs_f => ?_
    have hcs := r3a_cs_regs hcsm
    have htr_tot : sf.trace = s.trace := htr_f.trans htr1
    have hfs_tot : sf.fs.files = s.fs.files := hfs_f.trans (congrArg FsState.files hfs1)
    let st_me := M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st
    have henv_me : ∀ evs_peer, FreeOnlyEvs evs_peer →
        EnvAt g' out (M.stepEvents evs_peer st_me) := by
      intro evs_peer hfp_ev
      rw [← M.stepEvents_append]
      exact henv (rustDeallocEvents meG.name.cap.toNat 1 ++ evs_peer)
        (r3a_freeOnly_append (r3a_freeOnly_dealloc meG.name.cap.toNat 1) hfp_ev)
    exact r1c_sepWPp_weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hclose_peer st_me sf))
      (r3a_accept_peer_codeOk (g' := g') (peerG := peerG) (out := out) hh hext hsub64 hin_f
        (hcs.1.trans hx19_1) (hcs.2.1.trans hx20_1) (htr_tot ▸ htr)
        (r3a_hist_eq htr_tot hfs_tot hhist) hans hwr henv_me hjoin)

set_option maxHeartbeats 1600000 in
theorem r3a_accept_tail_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost} {out : Bytes}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 3476)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, out)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' out (M.stepEvents evs_tail st))
    (hjoin : JoinKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (apiDecResultAt A.repAlloc (runFsp s0 + 0x320#64) (.ok out) ∗
        protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗
        r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let joinBase : SepProp := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    memRegion (fsp + 0x460#64) 112 ∗ memRegion (fsp + 0x4d0#64) 120 ∗
    memRegion (fsp + 0x23b0#64) 48 ∗ r3a_frameGaps fsp ∗ anyHeap
  dsimp only [apiDecResultAt, vecResultAt, r3a_restFrame]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ V : SepProp,
        ⌜cap.toNat < 2 ^ 63 ∧
          (∀ dst : BitVec 64, r3a_words64At dst [cap, ptr, BitVec.ofNat 64 out.length] ∗ V ⊢
            vecU8 A.repAlloc dst out)⌝ ∗
        r3a_words64At (fsp + 0x328#64) [cap, ptr, BitVec.ofNat 64 out.length] ∗ V) ∗
      (memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x380#64) 16 ∗
        ((fsp + 0x320#64) ↦₆₄ okTagVec) ∗ memRegion (fsp + 0x340#64) 16 ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        stackAt fsp sub ∗ A.pool lim st s ∗ joinBase))
    (Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
        (r3a_vecU8_open A.repAlloc (runFsp s0 + 0x328#64) out))))
      (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))) ?_
  simp only [sepExists_sepConj_left]
  refine r1c_sepWPp_exists_left fun cap => r1c_sepWPp_exists_left fun ptr =>
    r1c_sepWPp_exists_left fun V => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine r1c_sepWPp_pure_left fun ⟨_hcap_lt, hvec_close⟩ => ?_
  let keepF : SepProp :=
    r3a_words64At (fsp + 0x328#64) [cap, ptr, BitVec.ofNat 64 out.length] ∗
      ((fsp + 0x320#64) ↦₆₄ okTagVec) ∗ V ∗ memRegion (fsp + 0x340#64) 16 ∗
      protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
      protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
      stackAt fsp sub ∗ A.pool lim st s ∗ joinBase
  refine r3a_sepWPp_bind
    (A0 := memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x380#64) 16) (F := keepF) ?_ |>
    r1c_sepWPp_weaken_pre (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
  intro R hm; rw [sepConj_assoc] at hm
  obtain ⟨ws208, hlen208, hm⟩ := r3a_open_words 3 (fsp + 0x208#64) hm
  rcases ws208 with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | _⟩⟩⟩ <;> try (simp at hlen208; done)
  obtain ⟨ws380, hlen380, hm⟩ := r3a_open_words 2 (fsp + 0x380#64)
    (Q := r3a_words64At (fsp + 0x208#64) [d0, d1, d2] ∗ (keepF ∗ R))
    (Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm)
  rcases ws380 with _ | ⟨u0, _ | ⟨u1, _ | _⟩⟩ <;> try (simp at hlen380; done)
  refine ⟨r3a_words64At (fsp + 0x208#64) [d0, d1, d2] ∗ r3a_words64At (fsp + 0x380#64) [u0, u1],
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm, ?_⟩
  have hpc : s.pc = runPcPlaced 3476 := hs.pc
  change s.pc = (blkPl_579).base + 3476#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hneq1 : (cap + 1#64 == 0#64) = false := by rw [beq_eq_false_iff_ne]; bv_omega
  have hneq2 : (cap == -1#64) = false := by rw [beq_eq_false_iff_ne]; bv_omega
  let P_step : SepProp :=
    ((s.sp + 0x320#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x328#64) ↦₆₄ cap) ∗
      ((s.sp + 0x330#64) ↦₆₄ ptr) ∗ ((s.sp + 0x338#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
      ((s.sp + 0x380#64) ↦₆₄ u0) ∗ ((s.sp + 0x388#64) ↦₆₄ u1) ∗
      ((s.sp + 0x208#64) ↦₆₄ d0) ∗ ((s.sp + 0x210#64) ↦₆₄ d1) ∗ ((s.sp + 0x218#64) ↦₆₄ d2)
  let P_after : SepProp :=
    ((s.sp + 0x320#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x328#64) ↦₆₄ cap) ∗
      ((s.sp + 0x330#64) ↦₆₄ ptr) ∗ ((s.sp + 0x338#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
      ((s.sp + 0x380#64) ↦₆₄ ptr) ∗ ((s.sp + 0x388#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
      ((s.sp + 0x208#64) ↦₆₄ cap) ∗ ((s.sp + 0x210#64) ↦₆₄ ptr) ∗
      ((s.sp + 0x218#64) ↦₆₄ BitVec.ofNat 64 out.length)
  have hstep : SepWP (runProgPlaced H) (runPcPlaced 3532) s P_step
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
          s1.readReg64 (.gpr 21#5) = meG.name.cap ∧ s1.readReg64 (.gpr 28#5) = meG.name.ptr) ∧
        (P1 ⊢ P_after)) := by
    rw [runPcPlaced_eq]
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hP_in :
      (r3a_words64At (fsp + 0x208#64) [d0, d1, d2] ∗ r3a_words64At (fsp + 0x380#64) [u0, u1]) ∗
        keepF ⊢
      P_step ∗ (V ∗ memRegion (fsp + 0x340#64) 16 ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        stackAt fsp sub ∗ A.pool lim st s ∗ joinBase) := by
    dsimp +zetaDelta only [keepF, okTagVec, r3a_words64At, P_step]
    rw [hs.sp]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
    exact Entails.of_eq (by sep_ac_rfl)
  refine r3a_frame_seq_vm_codeOk hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1
      ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1, hx21_1, hx28_1⟩ => ?_
  rw [← A.pool_transport lim st s s1 hvm1]
  have hpack_slots :
      P_after ∗ (V ∗ memRegion (fsp + 0x340#64) 16 ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        stackAt fsp sub ∗ A.pool lim st s1 ∗ joinBase) ⊢
      protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        A.pool lim st s1 ∗ stackAt fsp sub ∗
        vecU8 A.repAlloc (fsp + 0x208#64) out ∗
        memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (fsp + 0x4d0#64) 120 ∗ anyHeap := by
    dsimp +zetaDelta only [P_after]; rw [hs.sp]
    have hv208 : ((fsp + 0x208#64) ↦₆₄ cap) ∗ ((fsp + 0x210#64) ↦₆₄ ptr) ∗
        ((fsp + 0x218#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗ V ⊢
        vecU8 A.repAlloc (fsp + 0x208#64) out := by
      simpa only [r3a_words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc] using
        hvec_close (fsp + 0x208#64)
    have hm320 : ((fsp + 0x320#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 0x328#64) ↦₆₄ cap) ∗
        ((fsp + 0x330#64) ↦₆₄ ptr) ∗ ((fsp + 0x338#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
        memRegion (fsp + 0x340#64) 16 ⊢ memRegion (fsp + 0x320#64) 48 := by
      have hw4 := r3a_words_to_memRegion [0xfffffffffffffffe#64, cap, ptr, BitVec.ofNat 64 out.length]
        (fsp + 0x320#64) 32
      dsimp only [r3a_words64At] at hw4
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hw4
      have hsp48 : memRegion (fsp + 0x320#64) 32 ∗ memRegion (fsp + 0x340#64) 16 =
          memRegion (fsp + 0x320#64) 48 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          (ProofLib.memRegion_split (fsp + 0x320#64) 32 16 (by decide)).symm
      rw [← hsp48]; exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_left hw4)
    have hm380 : ((fsp + 0x380#64) ↦₆₄ ptr) ∗ ((fsp + 0x388#64) ↦₆₄ BitVec.ofNat 64 out.length) ⊢
        memRegion (fsp + 0x380#64) 16 := by
      simpa only [r3a_words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] using
        r3a_words_to_memRegion [ptr, BitVec.ofNat 64 out.length] (fsp + 0x380#64) 16
    dsimp +zetaDelta only [r3a_restFrame] at hv208 hm320 hm380 ⊢
    exact Entails.trans (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
      (Entails.trans
        (sepConj_mono hv208 (sepConj_mono hm320 (sepConj_mono hm380
          (Entails.refl (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
            protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1 ∗ joinBase)))))
        (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)))
  exact r1c_sepWPp_weaken_pre hpack_slots
    (r3a_accept_me_codeOk (g' := g') (peerG := peerG) (meG := meG) (out := out) hh hext hsub64
      ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
      hx19_1 hx20_1 hx21_1 hx28_1 (htr1 ▸ htr)
      (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist) hans hwr henv hjoin)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux
