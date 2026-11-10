/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAuxFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailBuildMessage
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# `FdsGe3Closed`-Threaded `signal_session::run` Placed Arm `R3a`: Whisper Arm Proof

Proves `run_hop_recvW_of_codeOk_placed_ok_fd`, `run_hop_recvW_placed_ok_of_env_fd`,
`run_hop_recvW_placed_ok_fd`, and `run_hop_recvW_frozen_placed_ok_fd` on Block `579`
(`runProgPlaced H`), transporting `FdsGe3Closed` from `AtDispatchPlacedFd` across
`tryFromPlacedSpecOkFs` (`Ok`-path `fs` preservation) into `hc.decryptSignal`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetFd

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError)
open CryptoVerification (LibsignalFrozen LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey (signalMessageAt_relocate)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet (extHookStack logOff smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Wire (logOff_tryFromPlacedImg tryFromPlacedImg)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SignalMessageGhost protocolAddressAt signalMessageAt signalMessageResultAt)
open CryptoVerification.SignalSession.Cli (StoresGhost cliIdentityVtSym cliSessionVtSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV CallW LsCodeInv RunCall callAt coinsInstalledPlaced coinsOf inputOf
   ownedBytes runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRunEntryPlaced Bytes DecSigGhost InRunPlaced MeAtDispatch PanicK RejectKind
   RunNeeds RunSem addrNameHeap addrUpperAt addrValOf dispatchCells dispatchMeHeap finish
   idVtPlaced mkSlot runFiles runFsp runPcPlaced runPcPlaced_eq runProgPlaced runSaved
   sessVtPlaced withCodeOk)
open CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers
  (r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
   r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setPState
   r1c_calleeSavedVRegs_writeReg64 r1c_extractLsb_append_hi r1c_extractLsb_append_lo
   r1c_fs_setMem r1c_fs_setPC r1c_fs_setPState r1c_fs_writeReg64 r1c_fs_writeVReg128
   r1c_mem_setPState r1c_readReg64_setPState r1c_sepWPp_exists_left r1c_sepWPp_pure_left
   r1c_sepWPp_weaken_pre r1c_spAligned r1c_sp_setPState r1c_stackAt_split_ge
   r1c_status_setPState r1c_symtab_setPState r1c_trace_setPState)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame runNeed)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   VmPreserved fitsEvents_append)
open LibsignalBinary.Proofs.Placed.Bridge (lsρ)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (RunHopRecvWPlacedFd RunHopRecvWPlacedFdOf fs_eq_of_sigTryFrom_eq_ok tryFromPlacedSpecOkFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (R3aRecvWEnv r3aDecSigGhost r3aDecSigGhost0 r3aMsgGhost0 r3aPeerGhost r3aPeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux
  (r3a_addrNameHeap_atState r3a_addrNameHeap_cap_lt r3a_addrUpper_relocate r3a_bounds
   r3a_callRecv_open r3a_call_lscro_codeOk r3a_cs_regs r3a_files_eq r3a_frameGaps
   r3a_frame_seq_vm_codeOk r3a_frame_some_eq r3a_hiGaps r3a_hist_of_slotTrace r3a_open_words
   r3a_pack_peer r3a_rejoin_1d0 r3a_restFrame r3a_sepWPp_bind r3a_sepWPp_exists_left
   r3a_storesAt_atState r3a_tw r3a_words64At r3a_words_to_memRegion tryFromEnv_iff_bytes)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAuxFd
  (r3a_after_decrypt_drop_codeOk_fd r3a_call_codeOk_fd r3a_readVReg128_setMem_fd
   r3a_readVReg128_setPC_fd r3a_readVReg128_setPState_fd r3a_readVReg128_writeReg64_fd
   r3a_recvW_none_codeOk_fd r3a_recvW_try_err_codeOk_fd r3a_sepWP_seq_vm_fd
   r3a_some_pre_try_fd r3a_vreg_01_fd r3a_vreg_02_fd r3a_vreg_10_fd r3a_vreg_12_fd
   r3a_vreg_20_fd r3a_vreg_21_fd r3a_vreg_same_fd subroutine_ok_withCodeOk_preFds_of_outer)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlacedEnv RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decSigSlotSpecBasePlaced decSigSlotSpecPlaced decSigSlotSpecPlacedOf
   slotFramePlaced slotsOfPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (callAt_atState dispatchMemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
  (AtDispatchPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (RunCalleesPlacedFd slotWithPreFdsGe3Closed withPreFdsGe3Closed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux (tryFromPlacedSpecGen)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
  (TryFromEnv tryFromPlacedSpec)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (R3aRecvWEnv r3aDecSigGhost r3aDecSigGhost0 r3aMsgGhost0 r3aPeerGhost r3aPeerGhost0)

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
  r3a_readVReg128_writeReg64_fd r3a_readVReg128_setPC_fd r3a_readVReg128_setMem_fd
  r3a_readVReg128_setPState_fd
  r3a_vreg_same_fd r3a_vreg_01_fd r3a_vreg_02_fd r3a_vreg_10_fd r3a_vreg_12_fd
  r3a_vreg_20_fd r3a_vreg_21_fd

local macro "r3a_close_post" : tactic =>
  `(tactic| (repeat' apply And.intro; all_goals ((try simp (config := { zetaDelta := true }) only [runPcPlaced_eq, RejectKind.pcOff, sessVtPlaced, idVtPlaced, cliSessionVtSym, cliIdentityVtSym, lsρ, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, runFsp, wp_norm, arm64_norm, *]); try rfl; try bv_omega)))

/-! ## 1. `wrap_decrypt_signal` Call (`R+0x7f0`) and `me = .some` Entry Path -/

set_option maxHeartbeats 1600000 in
private theorem r3a_after_try_ok_codeOk_fd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {EnvRej : StoresGhost → RejectKind → M.σ → Prop}
    {EnvJoin : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : RunSlots}
    {g : RunCall} {peerG meG : AddrGhost} {msgG : SignalMessageGhost} {m : SignalMessage}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B slots)
    (hslot_ds : RunCalleesPlacedFd A lim cEnvs H B slots →
      ∀ stk : Nat, needs.decryptSignal ≤ stk → stk ≤ 2 ^ 63 →
        subroutine_ok (runProgPlaced H) (lsmpl.base 463)
          (withPreFdsGe3Closed (decSigSlotSpecPlacedOf CodeOk A lim sEnvs.decryptSignal S stk)))
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hrf : runFrame ≤ resStack)
    (hdec : needs.decryptSignal ≤ resStack - runFrame)
    (hsub63 : resStack - runFrame ≤ 2 ^ 63)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hspb : resStack ≤ s0.sp.toNat)
    (h32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext : extHookStack ≤ resStack - runFrame)
    (hs : InRunPlaced CodeOk s0 s 2032)
    (hfd : FdsGe3Closed s.fs)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (hcoins : (coinsOf g.i).length < 2 ^ 63)
    (hfs : s.fs.files = runFiles g.i)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = [])
    (hfok : S.filesOk (runFiles g.i) peerG.val meG.val)
    (hga : g.a = finish (S.decryptSignal (runFiles g.i) peerG.val meG.val m (coinsOf g.i)) id)
    (htr : s0.trace <+: s.trace)
    (hfit_dec : FitsEnv M lim st (sEnvs.decryptSignal (r3aDecSigGhost g (runFsp s0) peerG meG msgG m)))
    (henv_rej : ∀ evs_dec evs_tail,
      sEnvs.decryptSignal (r3aDecSigGhost g (runFsp s0) peerG meG msgG m) evs_dec →
      FreeOnlyEvs evs_tail →
      ∀ g', EnvRej g' .postDispatch (M.stepEvents (evs_dec ++ evs_tail) st))
    (henv_join : ∀ evs_dec evs_tail,
      sEnvs.decryptSignal (r3aDecSigGhost g (runFsp s0) peerG meG msgG m) evs_dec →
      FreeOnlyEvs evs_tail →
      ∀ g' out, EnvJoin g' out (M.stepEvents (evs_dec ++ evs_tail) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvRej g s0 resStack Q Qp)
    (hjoin : JoinKPlacedEnv CodeOk H A lim EnvJoin g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (signalMessageAt A.repAlloc msgG (runFsp s0 + 0x4d0#64) m ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff ∗
        A.pool lim st s ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        memRegion (runFsp s0 + 0x320#64) 48 ∗ r3a_restFrame (runFsp s0) ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24))
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let callKeep : SepProp := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24
  let decCtx : DecSigGhost := r3aDecSigGhost g fsp peerG meG msgG m
  let preF : SepProp := storesAt A.repAlloc g.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
    coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff ∗
    A.pool lim st s ∗ stackAt fsp sub ∗
    memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x380#64) 16 ∗ r3a_frameGaps fsp ∗ callKeep
  dsimp only [r3a_restFrame]
  refine r3a_sepWPp_bind
    (A0 := signalMessageAt A.repAlloc msgG (fsp + 0x4d0#64) m ∗
      memRegion (fsp + 0x460#64) 112 ∗ memRegion (fsp + 0x23b0#64) 48)
    (F := preF) ?_ |>
    r1c_sepWPp_weaken_pre (by dsimp +zetaDelta only; exact Entails.of_eq (by sep_ac_rfl))
  intro R hm; rw [sepConj_assoc, sepConj_assoc] at hm
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, H_sm, hw0, _, hm, hsm_close⟩ :=
    signalMessageAt_relocate A.repAlloc msgG (fsp + 0x4d0#64) m hm
  rw [r3a_tw] at hm; simp only [r3a_tw] at hsm_close
  obtain ⟨ws460, hlen460, hm⟩ := r3a_open_words 14 (fsp + 0x460#64)
    (Q := r3a_words64At (fsp + 0x4d0#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
      (H_sm ∗ (memRegion (fsp + 0x23b0#64) 48 ∗ (preF ∗ R))))
    (Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm)
  rcases ws460 with _ | ⟨g0, _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, _ | ⟨g5, _ | ⟨g6, _ | ⟨g7, _ | ⟨g8, _ |
    ⟨g9, _ | ⟨g10, _ | ⟨g11, _ | ⟨g12, _ | ⟨g13, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hlen460; done)
  obtain ⟨ws23b0, hlen23b0, hm⟩ := r3a_open_words 6 (fsp + 0x23b0#64)
    (Q := r3a_words64At (fsp + 0x4d0#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
      (r3a_words64At (fsp + 0x460#64) [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] ∗
        (H_sm ∗ (preF ∗ R))))
    (Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm)
  rcases ws23b0 with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | _⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hlen23b0; done)
  refine ⟨r3a_words64At (fsp + 0x4d0#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
    r3a_words64At (fsp + 0x460#64) [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] ∗
    r3a_words64At (fsp + 0x23b0#64) [v0, v1, v2, v3, v4, v5] ∗ H_sm,
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm, ?_⟩
  have hpc : s.pc = runPcPlaced 2032 := hs.pc
  change s.pc = (blkPl_579).base + 2032#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  rw [← hs.sp] at hx26
  have hb0 : (w0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0
  let P_step : SepProp :=
    r3a_words64At (s.sp + 0x4d0#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
      r3a_words64At (s.sp + 0x460#64) [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] ∗
      r3a_words64At (s.sp + 0x23b0#64) [v0, v1, v2, v3, v4, v5]
  let P_after_at (sp : BitVec 64) : SepProp :=
    r3a_words64At (sp + 0x4d0#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
      r3a_words64At (sp + 0x460#64) [w7, w8, w9, w10, w11, w12, w13, w14, w1, w2, w3, w4, w5, w6] ∗
      r3a_words64At (sp + 0x23b0#64) [w1, w2, w3, w4, w5, w6]
  let P_after : SepProp := P_after_at s.sp
  let midPost1 (st1 : State) : Prop :=
    st1.sp = s.sp ∧ st1.readReg64 .fp = s0.sp - 0x60#64 ∧
      calleeSavedVRegs st1 = calleeSavedVRegs s0 ∧ st1.trace = s.trace ∧ st1.fs = s.fs ∧
      st1.readReg64 .x8 = w0 ∧ st1.readReg64 .x9 = -1#64 ∧
      st1.readVReg128 0#5 = w2 ++ w1 ∧ st1.readVReg128 1#5 = w4 ++ w3 ∧
      st1.readVReg128 2#5 = w6 ++ w5 ∧
      st1.readReg64 (.gpr 19#5) = g.stores ∧ st1.readReg64 (.gpr 20#5) = g.res ∧
      st1.readReg64 (.gpr 21#5) = meG.name.cap ∧
      st1.readReg64 (.gpr 26#5) = s.sp + 0x4d0#64 ∧
      st1.readReg64 (.gpr 28#5) = meG.name.ptr
  let midPost2 (st1 : State) : Prop :=
    st1.readReg64 .x4 = sessVtPlaced ∧ midPost1 st1
  let midPost3 (st1 : State) : Prop :=
    st1.sp = s.sp ∧ st1.readReg64 .fp = s0.sp - 0x60#64 ∧
      calleeSavedVRegs st1 = calleeSavedVRegs s0 ∧ st1.trace = s.trace ∧ st1.fs = s.fs ∧
      st1.readReg64 .x4 = sessVtPlaced ∧
      st1.readReg64 .x8 = w0 ∧ st1.readReg64 .x9 = -1#64 ∧
      st1.readVReg128 0#5 = w8 ++ w7 ∧ st1.readVReg128 1#5 = w4 ++ w3 ∧
      st1.readVReg128 2#5 = w6 ++ w5 ∧
      st1.readReg64 (.gpr 19#5) = g.stores ∧ st1.readReg64 (.gpr 20#5) = g.res ∧
      st1.readReg64 (.gpr 21#5) = meG.name.cap ∧
      st1.readReg64 (.gpr 26#5) = s.sp + 0x4d0#64 ∧
      st1.readReg64 (.gpr 28#5) = meG.name.ptr
  let midPost4 (st1 : State) : Prop :=
    st1.readReg64 .x6 = idVtPlaced ∧ midPost3 st1
  let finalPost (s1 : State) : Prop :=
    s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
      s1.readReg64 .lr = runPcPlaced 3468 ∧
      s1.readReg64 .x0 = fsp + 0x4d0#64 ∧ s1.readReg64 .x1 = fsp + 0x220#64 ∧
      s1.readReg64 .x2 = fsp + 0x260#64 ∧ s1.readReg64 .x3 = g.stores + 0xf0#64 ∧
      s1.readReg64 .x4 = sessVtPlaced ∧ s1.readReg64 .x5 = g.stores ∧
      s1.readReg64 .x6 = idVtPlaced ∧ s1.readReg64 .x8 = fsp + 0x320#64 ∧
      s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
      s1.readReg64 (.gpr 21#5) = meG.name.cap ∧
      s1.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 ∧
      s1.readReg64 (.gpr 28#5) = meG.name.ptr
  have hstep1 : SepWP (runProgPlaced H) ((blkPl_579).base + 3372#64) s P_step
      (fun s1a P1 => VmPreserved s s1a ∧ midPost1 s1a ∧ (P1 ⊢ P_after)) := by
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after, P_after_at, midPost1, r3a_words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hstep : SepWP (runProgPlaced H) (lsmpl.base 463) s P_step
      (fun s1 P1 => VmPreserved s s1 ∧ finalPost s1 ∧ (P1 ⊢ P_after)) := by
    refine r3a_sepWP_seq_vm_fd hstep1 fun s1a _ hpc1a hrun1a
      ⟨hsp1a, hfp1a, hv1a, htr1a, hfs1a, hx8_1a, hx9_1a, hv0_1a, hv1_1a, hv2_1a,
        hx19_1a, hx20_1a, hx21_1a, hx26_1a, hx28_1a⟩ => ?_
    refine r3a_sepWP_seq_vm_fd (mid := (blkPl_579).base + 3380#64) (P' := P_after) (post1 := midPost2)
      (by
        dsimp only [runProgPlaced, lsProg_579, midPost2, midPost1]
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.refl _⟩
        r3a_close_post)
      fun s1b _ hpc1b hrun1b
        ⟨hx4_1b, hsp1b, hfp1b, hv1b, htr1b, hfs1b, hx8_1b, hx9_1b, hv0_1b, hv1_1b, hv2_1b,
          hx19_1b, hx20_1b, hx21_1b, hx26_1b, hx28_1b⟩ => ?_
    refine r3a_sepWP_seq_vm_fd (mid := (blkPl_579).base + 3396#64) (P' := P_after) (post1 := midPost3)
      (by
        have hal1b : s1b.spAligned = true := r1c_spAligned hs.spAligned (hsp1b.trans hsp)
        dsimp only [P_after, P_after_at, midPost3]
        rw [← hsp1b] at hx26_1b ⊢
        dsimp only [runProgPlaced, lsProg_579, r3a_words64At]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
        by_vm_steps (
          wp_steps
          apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
            (by simp only [wp_norm, arm64_norm, *])
          refine ⟨by simp only [wp_norm, arm64_norm], ?_,
            Entails.of_eq (by
              simp only [hv0_1b, hv1_1b, hv2_1b, hx8_1b, hx9_1b,
                r1c_extractLsb_append_lo, r1c_extractLsb_append_hi, wp_norm, arm64_norm])⟩
          r3a_close_post))
      fun s1c _ hpc1c hrun1c
        ⟨hsp1c, hfp1c, hv1c, htr1c, hfs1c, hx4_1c, hx8_1c, hx9_1c, hv0_1c, hv1_1c, hv2_1c,
          hx19_1c, hx20_1c, hx21_1c, hx26_1c, hx28_1c⟩ => ?_
    refine r3a_sepWP_seq_vm_fd (mid := (blkPl_579).base + 3404#64) (P' := P_after) (post1 := midPost4)
      (by
        dsimp only [runProgPlaced, lsProg_579, midPost4, midPost3]
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.refl _⟩
        r3a_close_post)
      fun s1d _ hpc1d hrun1d
        ⟨hx6_1d, hsp1d, hfp1d, hv1d, htr1d, hfs1d, hx4_1d, hx8_1d, hx9_1d,
          hv0_1d, hv1_1d, hv2_1d, hx19_1d, hx20_1d, hx21_1d, hx26_1d, hx28_1d⟩ => ?_
    have hal1d : s1d.spAligned = true := r1c_spAligned hs.spAligned (hsp1d.trans hsp)
    dsimp only [P_after, P_after_at, finalPost]
    rw [← hsp1d] at hx26_1d ⊢
    dsimp only [runProgPlaced, lsProg_579, r3a_words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_,
        Entails.of_eq (by
          simp only [hv0_1d, hv1_1d, hv2_1d, hx8_1d, hx9_1d,
            r1c_extractLsb_append_lo, r1c_extractLsb_append_hi, wp_norm, arm64_norm])⟩
      r3a_close_post)
  have hP_in :
      (r3a_words64At (fsp + 0x4d0#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        r3a_words64At (fsp + 0x460#64) [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] ∗
        r3a_words64At (fsp + 0x23b0#64) [v0, v1, v2, v3, v4, v5] ∗ H_sm) ∗ preF ⊢
      P_step ∗ (H_sm ∗ preF) := by
    dsimp +zetaDelta only [P_step]; rw [hs.sp]; exact Entails.of_eq (by sep_ac_rfl)
  refine r3a_frame_seq_vm_codeOk hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1
      ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1,
        hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx8_1,
        hx19_1, hx20_1, hx21_1, hx26_1, hx28_1⟩ => ?_
  have hal1 : s1.spAligned = true := r1c_spAligned hs.spAligned hsp1
  dsimp only [preF]
  rw [← A.pool_transport lim st s s1 hvm1]
  have htr_s1 : s0.trace <+: s1.trace := htr1 ▸ htr
  have hdec_ok : subroutine_ok (runProgPlaced H) (lsmpl.base 463)
      (withCodeOk CodeOk (withPreFdsGe3Closed
        (decSigSlotSpecBasePlaced A lim sEnvs.decryptSignal S sub))) :=
    subroutine_ok_withCodeOk_preFds_of_outer (hslot_ds hc sub hdec hsub63)
  refine r1c_sepWPp_weaken_pre
    (P' := signalMessageAt A.repAlloc msgG (fsp + 0x4d0#64) m ∗
      (r3a_restFrame fsp ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff ∗
        A.pool lim st s1 ∗ stackAt fsp sub ∗ memRegion (fsp + 0x320#64) 48 ∗ callKeep))
    (by
      dsimp only [P_after, P_after_at]; rw [hs.sp]
      have hsm := hsm_close (fsp + 0x4d0#64)
      have hm460 := r3a_words_to_memRegion
        [w7, w8, w9, w10, w11, w12, w13, w14, w1, w2, w3, w4, w5, w6] (fsp + 0x460#64) 112
      have hm23b0 := r3a_words_to_memRegion [w1, w2, w3, w4, w5, w6] (fsp + 0x23b0#64) 48
      dsimp +zetaDelta only [r3a_restFrame] at hsm hm460 hm23b0 ⊢
      exact Entails.trans (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
        (Entails.trans
          (sepConj_mono hsm (sepConj_mono hm460 (sepConj_mono hm23b0
            (Entails.refl (memRegion (runFsp s0 + 0x380#64) 16 ∗ r3a_frameGaps (runFsp s0) ∗
              storesAt A.repAlloc g.stores StoresGhost.opened ∗
              protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
              protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff ∗
              A.pool lim st s1 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
              memRegion (runFsp s0 + 0x320#64) 48 ∗ callKeep)))))
          (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)))) ?_
  refine r3a_call_codeOk_fd (decCtx, st) hdec_ok hinv1 hpc1 hrun1 hal1 hlr1
    (F := r3a_restFrame fsp ∗ callKeep) ?_
    (hpanic := fun sf _ _ hp => by
      dsimp only [withPreFdsGe3Closed, decSigSlotSpecBasePlaced, decCtx, r3aDecSigGhost] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hpanic sf _ (Or.inl (by rw [hga, hp.1]; rfl)))
    (hnext := fun s2 _ hinv2 hpcm2 hrun2 hsp2 hcsm2 => ?_)
  · dsimp only [withPreFdsGe3Closed]
    rw [sepConj_assoc]
    refine Entails.pure_right (by rw [hfs1]; exact hfd) ?_
    dsimp only [decSigSlotSpecBasePlaced, slotFramePlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
      CryptoVerification.SignalSession.Cli.RunCompose.slotFramePlaced,
      decCtx, r3aDecSigGhost]
    simp only [RustCliAllocBudget.atState_pool, sepConj_assoc]
    have hsp_sub : sub ≤ s1.sp.toNat := by
      rw [hsp1]
      change resStack - 0x2a50 ≤ (s0.sp - 0x2a50#64).toNat
      rw [BitVec.toNat_sub_of_le
        (by change 0x2a50 ≤ s0.sp.toNat; change 0x2a50 ≤ resStack at hrf; omega)]
      change resStack - 0x2a50 ≤ s0.sp.toNat - 0x2a50; omega
    have hfs_s1 : s1.fs.files = runFiles g.i := (congrArg FsState.files hfs1).trans hfs
    refine Entails.pure_right
      ⟨hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx8_1, hfs_s1, hfok, hsp_sub, hfit_dec⟩ ?_
    refine Entails.pure_right hcoins ?_
    rw [hsp1]
    exact Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)
  · have hcs2 := r3a_cs_regs hcsm2
    have hin2 : InRunPlaced CodeOk s0 s2 3468 :=
      ⟨hpcm2, hrun2, hsp2.trans hsp1, hcs2.2.2.2.2.2.1.trans hfp1, hinv2,
        hcs2.2.2.2.2.2.2.trans hv1, hs.spAligned⟩
    dsimp only [withPreFdsGe3Closed, decSigSlotSpecBasePlaced, decCtx, r3aDecSigGhost]
    simp only [sepExists_sepConj_left]
    refine r1c_sepWPp_exists_left fun evs_dec =>
      r1c_sepWPp_exists_left fun g' =>
      r1c_sepWPp_exists_left fun res => ?_
    simp only [sepConj_assoc]
    refine r1c_sepWPp_pure_left fun ⟨hdec_ev, hstr2, hslot2⟩ => ?_
    have hfs_s1 : s1.fs.files = runFiles g.i := (congrArg FsState.files hfs1).trans hfs
    have ⟨htr2_tot, hhist2⟩ := r3a_hist_of_slotTrace htr_s1 hfs_s1 (htr1 ▸ hout) hstr2
    rw [hsp1]
    let st_dec := M.stepEvents evs_dec st
    have henv_rej2 : ∀ evs_tail, FreeOnlyEvs evs_tail →
        EnvRej g' .postDispatch (M.stepEvents evs_tail st_dec) := by
      intro evs_tail hf
      rw [← M.stepEvents_append]
      exact henv_rej evs_dec evs_tail hdec_ev hf g'
    have henv_join2 : ∀ out, res = .ok out → ∀ evs_tail, FreeOnlyEvs evs_tail →
        EnvJoin g' out (M.stepEvents evs_tail st_dec) := by
      intro out _ evs_tail hf
      rw [← M.stepEvents_append]
      exact henv_join evs_dec evs_tail hdec_ev hf g' out
    exact r1c_sepWPp_weaken_pre (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
      (r3a_after_decrypt_drop_codeOk_fd (g' := g') (peerG := peerG) (meG := meG) (msgG := msgG) (m := m)
        hh hdrop h32 hext hsub64 hin2
        (hcs2.1.trans hx19_1) (hcs2.2.1.trans hx20_1) (hcs2.2.2.1.trans hx21_1)
        (hcs2.2.2.2.1.trans hx26_1) (hcs2.2.2.2.2.1.trans hx28_1)
        htr_s1 hga hslot2 htr2_tot hhist2 henv_rej2 henv_join2 hrej hjoin)

set_option maxHeartbeats 1600000 in
private theorem r3a_recvW_some_codeOk_fd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {RecvWEnv : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : RunSlots}
    {g : RunCall} {peerV : AddrV} {rest : Bytes} {meV : AddrV} {meG : AddrGhost}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (h_try_fit : ∀ evs_try, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try →
      RecvWEnv g (.some meV meG) peerV rest evs_try)
    (h_try_err : ∀ e, SignalMessage.tryFrom protoSignalCodec rest = .error e →
      ∀ evs_try evs_tail, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try → FreeOnlyEvs evs_tail →
        RecvWEnv g (.some meV meG) peerV rest (evs_try ++ evs_tail))
    (h_dec_fit : ∀ w msgG m, SignalMessage.tryFrom protoSignalCodec rest = .ok m →
      ∀ evs_try evs_dec, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try →
        sEnvs.decryptSignal (r3aDecSigGhost g (runFsp s0) (r3aPeerGhost w peerV) meG msgG m) evs_dec →
        RecvWEnv g (.some meV meG) peerV rest (evs_try ++ evs_dec))
    (h_dec_end : ∀ w msgG m, SignalMessage.tryFrom protoSignalCodec rest = .ok m →
      ∀ evs_try evs_dec evs_tail, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try →
        sEnvs.decryptSignal (r3aDecSigGhost g (runFsp s0) (r3aPeerGhost w peerV) meG msgG m) evs_dec →
        FreeOnlyEvs evs_tail →
        RecvWEnv g (.some meV meG) peerV rest (evs_try ++ (evs_dec ++ evs_tail)))
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B slots)
    (htry : subroutine_ok (runProgPlaced H) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hslot_ds : RunCalleesPlacedFd A lim cEnvs H B slots →
      ∀ stk : Nat, needs.decryptSignal ≤ stk → stk ≤ 2 ^ 63 →
        subroutine_ok (runProgPlaced H) (lsmpl.base 463)
          (withPreFdsGe3Closed (decSigSlotSpecPlacedOf CodeOk A lim sEnvs.decryptSignal S stk)))
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hspb : resStack ≤ s0.sp.toNat)
    (he : AtRunEntryPlaced CodeOk S g s0)
    (hd_fd : AtDispatchPlacedFd CodeOk g (.some meV meG) s0 s)
    (hcall : g.c = .recv peerV)
    (hstdin : g.i.stdin = 2#8 :: rest)
    (hfit : FitsEnv M lim st (RecvWEnv g (.some meV meG) peerV rest))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, RecvWEnv g (.some meV meG) peerV rest evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp)
    (hjoin : JoinKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, RecvWEnv g (.some meV meG) peerV rest evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g (.some meV meG) s0 s resStack)
      Q Qp (fun _ => ⌜False⌝) := by
  obtain ⟨hd, hfd0⟩ := hd_fd
  have hlog : logOff tryFromPlacedImg = lsLogOff := logOff_tryFromPlacedImg
  obtain ⟨hrf, hsub63, hsub64, hsm, h32, hext, hdec⟩ := r3a_bounds hres hres64
  let fsp := runFsp s0; let sub := resStack - runFrame
  have hs : InRunPlaced CodeOk s0 s 532 := hd.base
  have hpc : s.pc = runPcPlaced 532 := hs.pc
  change s.pc = (blkPl_579).base + 532#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa only [hcall, CallV.tag] using hd.x8
  have hx19 := hd.x19; have hx20 := hd.x20; have hx23 := hd.x23
  have hx25 := hd.x25; have hx26 := hd.x26
  have hinp_eq : inputOf g.i g.c = 2#8 :: rest := by rw [hcall]; exact hstdin
  have hinp_merge : (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) = (g.inp ↦ₛ inputOf g.i g.c) := by
    rw [hinp_eq, pointsToBytes_cons]
  have hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (rest.length + 1) := by
    rw [hd.x24, hinp_eq]; rfl
  obtain ⟨hx21, hx28, hme_bytes, _, hme_dev⟩ := hd.meRegs
  obtain ⟨hrest32, hcoins, hfs, hfok, hga⟩ := hd.recvW_facts he hcall hstdin
  have hnz24 : (BitVec.ofNat 64 (rest.length + 1) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; bv_omega
  have hme_val : meG.val = addrValOf meV := by
    unfold AddrGhost.val addrValOf; rw [hme_bytes, hme_dev]
  have hx1_bv : BitVec.ofNat 64 (rest.length + 1) - 1#64 = BitVec.ofNat 64 rest.length := by
    rw [BitVec.ofNat_add]; bv_omega
  let someTail : SepProp := memRegion g.res runResSize ∗
    storesAt A.repAlloc g.stores StoresGhost.opened ∗
    coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff ∗
    runSaved s0 ∗ memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) 40 ∗
    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x320#64) 48 ∗
    memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗
    memRegion (fsp + 0x4d0#64) 120 ∗ memRegion (fsp + 0x23b0#64) 48 ∗
    r3a_hiGaps fsp ∗ stackAt fsp sub ∗ A.pool lim st s
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ w : CallW, ⌜w.w4.setWidth 8 = peerV.device⌝ ∗
        r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
        ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name) ∗
      (⌜meG.name.cap.toNat < 2 ^ 63⌝ ∗ addrNameHeap A.repAlloc meG ∗
        (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
        addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion (fsp + 0x220#64) 32 ∗
        memRegion (fsp + 0x260#64) 32 ∗ someTail)) ?_ ?_
  · dsimp +zetaDelta only [dispatchMemPlaced,
      CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced,
      dispatchMeHeap, dispatchCells]
    simp only [RustCliAllocBudget.atState_pool, callAt_atState, r3a_storesAt_atState,
      r3a_addrNameHeap_atState]
    rw [hinp_eq, pointsToBytes_cons, hcall, r3a_frame_some_eq (runFsp s0) meG]
    refine Entails.trans
      (Entails.of_eq (show _ =
        callAt A.repAlloc g.call (.recv peerV) ∗ addrNameHeap A.repAlloc meG ∗
        ((g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
          addrUpperAt (runFsp s0 + 0x1d0#64) meG ∗
          memRegion (runFsp s0 + 0x220#64) 32 ∗ memRegion (runFsp s0 + 0x260#64) 32 ∗
          (memRegion g.res runResSize ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
            coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff ∗
            runSaved s0 ∗ memRegion (runFsp s0) 0x1d0 ∗ memRegion (runFsp s0 + 0x1e0#64) 40 ∗
            memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
            memRegion (runFsp s0 + 0x380#64) 16 ∗ memRegion (runFsp s0 + 0x460#64) 112 ∗
            memRegion (runFsp s0 + 0x4d0#64) 120 ∗ memRegion (runFsp s0 + 0x23b0#64) 48 ∗
            r3a_hiGaps (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
            A.pool lim st s)) by sep_ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono (r3a_callRecv_open A.repAlloc g.call peerV)
        (sepConj_mono_left (r3a_addrNameHeap_cap_lt A.repAlloc meG)))
      (Entails.of_eq (by sep_ac_rfl))
  refine r3a_sepWPp_exists_left fun w => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine r1c_sepWPp_pure_left fun hw4 => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := ⌜meG.name.cap.toNat < 2 ^ 63⌝ ∗
      (r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
        ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗ addrNameHeap A.repAlloc meG ∗
        (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
        addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion (fsp + 0x220#64) 32 ∗
        memRegion (fsp + 0x260#64) 32 ∗ someTail))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
    (r1c_sepWPp_pure_left fun _hme_lt => ?_)
  have hme_ne : (meG.name.cap + 1#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; bv_omega
  let peerG : AddrGhost := r3aPeerGhost w peerV
  let someKeep : SepProp :=
    r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗ addrNameHeap A.repAlloc meG ∗
      (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗ someTail
  refine r3a_sepWPp_bind
    (A0 := addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion (fsp + 0x220#64) 32 ∗
      memRegion (fsp + 0x260#64) 32)
    (F := someKeep) ?_ |>
    r1c_sepWPp_weaken_pre (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
  intro R hm; rw [sepConj_assoc, sepConj_assoc] at hm
  obtain ⟨u1, hm, hme_close⟩ := r3a_addrUpper_relocate (fsp + 0x1d0#64) meG hm
  obtain ⟨ws220, hlen220, hm⟩ := r3a_open_words 4 (fsp + 0x220#64)
    (Q := r3a_words64At (fsp + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗
      (memRegion (fsp + 0x260#64) 32 ∗ (someKeep ∗ R)))
    (Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm)
  rcases ws220 with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen220; done)
  obtain ⟨ws260, hlen260, hm⟩ := r3a_open_words 4 (fsp + 0x260#64)
    (Q := r3a_words64At (fsp + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗
      (r3a_words64At (fsp + 0x220#64) [p0, p1, p2, p3] ∗ (someKeep ∗ R)))
    (Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm)
  rcases ws260 with _ | ⟨q0, _ | ⟨q1, _ | ⟨q2, _ | ⟨q3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen260; done)
  refine ⟨r3a_words64At (fsp + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗
    r3a_words64At (fsp + 0x220#64) [p0, p1, p2, p3] ∗
    r3a_words64At (fsp + 0x260#64) [q0, q1, q2, q3],
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm, ?_⟩
  let P_step : SepProp :=
    r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      r3a_words64At (s.sp + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗
      r3a_words64At (s.sp + 0x220#64) [p0, p1, p2, p3] ∗
      r3a_words64At (s.sp + 0x260#64) [q0, q1, q2, q3] ∗ (g.inp ↦₈ 2#8)
  let P_after : SepProp :=
    r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      r3a_words64At (s.sp + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗
      r3a_words64At (s.sp + 0x220#64) [w.w1, w.w2, w.w3, w.w4] ∗
      r3a_words64At (s.sp + 0x260#64)
        [meG.name.cap, meG.name.ptr, BitVec.ofNat 64 meV.name.length, u1] ∗
      (g.inp ↦₈ 2#8)
  have hstep : SepWP (runProgPlaced H) (lsmpl.base 85) s P_step
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .lr = runPcPlaced 2032 ∧
          s1.readReg64 .x0 = g.inp + 1#64 ∧
          s1.readReg64 .x1 = BitVec.ofNat 64 rest.length ∧
          s1.readReg64 .x8 = fsp + 0x4d0#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
          s1.readReg64 (.gpr 21#5) = meG.name.cap ∧
          s1.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 ∧
          s1.readReg64 (.gpr 28#5) = meG.name.ptr) ∧
        (P1 ⊢ P_after)) := by
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after, r3a_words64At]
    rw [hme_bytes]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hP_in :
      (r3a_words64At (fsp + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗
        r3a_words64At (fsp + 0x220#64) [p0, p1, p2, p3] ∗
        r3a_words64At (fsp + 0x260#64) [q0, q1, q2, q3]) ∗ someKeep ⊢
      P_step ∗ (ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗ addrNameHeap A.repAlloc meG ∗
        ((g.inp + 1#64) ↦ₛ rest) ∗ someTail) := by
    dsimp +zetaDelta only [P_step, someKeep]; rw [hs.sp]; exact Entails.of_eq (by sep_ac_rfl)
  refine r3a_frame_seq_vm_codeOk hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1
      ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1,
        hx0_1, hx1_1, hx8_1, hx19_1, hx20_1, hx21_1, hx26_1, hx28_1⟩ => ?_
  have hal1 : s1.spAligned = true := r1c_spAligned hs.spAligned hsp1
  dsimp only [someTail]
  rw [← A.pool_transport lim st s s1 hvm1]
  have hsp_sm := r1c_stackAt_split_ge fsp hsm hsub64
  let tryKeep : SepProp := (g.inp ↦₈ 2#8) ∗
    protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    storesAt A.repAlloc g.stores StoresGhost.opened ∗
    coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp
  refine r1c_sepWPp_weaken_pre
    (P' := ((g.inp + 1#64) ↦ₛ rest) ∗ memRegion (fsp + 0x4d0#64) 120 ∗ lsLogOff ∗
      stackAt fsp smallRootStack ∗ A.pool lim st s1 ∗
      (memRegion (fsp - BitVec.ofNat 64 sub) (sub - smallRootStack) ∗ tryKeep))
    (by
      dsimp +zetaDelta only [P_after]; rw [hs.sp]
      exact r3a_some_pre_try_fd A.repAlloc (A.pool lim st s1) g peerV rest s0 resStack meV meG w u1
        hme_bytes hsm hsub64
        (r3a_words_to_memRegion [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] g.call 56)
        (r3a_pack_peer A.repAlloc (runFsp s0 + 0x220#64) peerV w.w1 w.w2 w.w3 w.w4 hw4)
        hme_close
        (r3a_rejoin_1d0 (runFsp s0) (BitVec.ofNat 64 meG.name.bytes.length) u1)) ?_
  have hfit_try : FitsEnv M lim st (TryFromEnv ⟨g.inp + 1#64, rest, fsp + 0x4d0#64⟩) :=
    fun evs hevs => hfit evs (h_try_fit evs (tryFromEnv_iff_bytes.mp hevs))
  refine r3a_call_lscro_codeOk (⟨g.inp + 1#64, rest, fsp + 0x4d0#64⟩, st) htry hinv1 hpc1 hrun1 hal1 hlr1
    (F := memRegion (fsp - BitVec.ofNat 64 sub) (sub - smallRootStack) ∗ tryKeep) ?_
    (hnext := fun s2 hsteps2 hinv2 hpcm2 hrun2 hsp2 hcsm2 => ?_)
  · dsimp only [tryFromPlacedSpecOkFs, tryFromPlacedSpec, tryFromPlacedSpecGen]
    rw [hlog]; simp only [sepConj_assoc]
    have hx1_nat : (s1.readReg64 .x1).toNat = rest.length := by
      rw [hx1_1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rest.length < 2 ^ 64)]
    refine Entails.pure_right ⟨hx0_1, hx1_nat, hrest32, hx8_1, hfit_try⟩ ?_
    exact Entails.of_eq (by rw [hsp1]; (try dsimp +zetaDelta only); try sep_ac_rfl)
  · have hcs2 := r3a_cs_regs hcsm2
    have hsp2_fsp : s2.sp = fsp := hsp2.trans hsp1
    have hin2 : InRunPlaced CodeOk s0 s2 2032 :=
      ⟨hpcm2, hrun2, hsp2_fsp, hcs2.2.2.2.2.2.1.trans hfp1, hinv2,
        hcs2.2.2.2.2.2.2.trans hv1, hs.spAligned⟩
    have hx19_2 := hcs2.1.trans hx19_1; have hx20_2 := hcs2.2.1.trans hx20_1
    have hx21_2 := hcs2.2.2.1.trans hx21_1; have hx26_2 := hcs2.2.2.2.1.trans hx26_1
    have hx28_2 := hcs2.2.2.2.2.1.trans hx28_1
    dsimp only [tryFromPlacedSpecOkFs, tryFromPlacedSpec, tryFromPlacedSpecGen]
    rw [hlog]; simp only [sepConj_assoc]
    refine r1c_sepWPp_pure_left fun hfs_try_ok => ?_
    refine r1c_sepWPp_pure_left fun htr2 => ?_
    rw [sepExists_sepConj_left]
    refine r1c_sepWPp_exists_left fun evs_try => ?_
    simp only [sepConj_assoc]
    refine r1c_sepWPp_pure_left fun htry_ev_raw => ?_
    have htry_ev : TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try :=
      tryFromEnv_iff_bytes.mp htry_ev_raw
    rw [hsp1]
    have htr2_tot : s0.trace <+: s2.trace := (htr2.trans htr1) ▸ hd.trace
    have hfs2 : s2.fs.files = runFiles g.i :=
      (r3a_files_eq hh hsteps2 htr2).trans ((congrArg FsState.files hfs1).trans hfs)
    have hout2 : ProcessOutcome.traceStreamBytes .stdout s2.trace = [] :=
      (htr2.trans htr1) ▸ hd.stdout
    let st_try := M.stepEvents evs_try st
    rcases hm_res : SignalMessage.tryFrom protoSignalCodec rest with e | m
    · have hans2 : g.a = some none := by rw [hga, hm_res]
      have henv_err : ∀ evs_tail, FreeOnlyEvs evs_tail →
          ∃ evs, RecvWEnv g (.some meV meG) peerV rest evs ∧
            M.stepEvents evs_tail st_try = M.stepEvents evs st := by
        intro evs_tail hf
        exact ⟨evs_try ++ evs_tail,
          h_try_err e hm_res evs_try evs_tail htry_ev hf,
          (M.stepEvents_append evs_try evs_tail st).symm⟩
      refine r1c_sepWPp_weaken_pre ?_
        (r3a_recvW_try_err_codeOk_fd (peerG := peerG) (meG := meG) (e := e)
          hh hdrop hext h32 hsub64 hin2 hx19_2 hx20_2 hx21_2 hx26_2 hx28_2
          htr2_tot ⟨hfs2, hout2⟩ hans2 henv_err hrej)
      dsimp +zetaDelta only at hsp_sm ⊢
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest)) ∗
          (memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
              (resStack - runFrame - smallRootStack) ∗
            stackAt (runFsp s0) smallRootStack) ∗
          (coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff) ∗
          (signalMessageResultAt A.repAlloc [] (runFsp s0 + 0x4d0#64) (.error e) ∗
            A.pool lim st_try s2 ∗
            protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
            protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗ runSaved s0 ∗
            memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
            r3a_restFrame (runFsp s0)) by sep_ac_rfl)) ?_
      rw [hinp_merge, hsp_sm.symm]
      exact Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (entails_anyHeap _))))
        (Entails.of_eq (by sep_ac_rfl))
    · have hfd2 : FdsGe3Closed s2.fs := by
        rw [fs_eq_of_sigTryFrom_eq_ok hfs_try_ok hm_res, hfs1]
        exact hfd0
      dsimp only [signalMessageResultAt]
      rw [sepExists_sepConj_left]
      refine r1c_sepWPp_exists_left fun msgG => ?_
      rw [hm_res] at hga
      have hfok' : S.filesOk (runFiles g.i) peerG.val meG.val := by rw [hme_val]; exact hfok
      have hga' : g.a = finish (S.decryptSignal (runFiles g.i) peerG.val meG.val m (coinsOf g.i)) id := by
        rw [hme_val]; exact hga
      have hfit_dec : FitsEnv M lim st_try
          (sEnvs.decryptSignal (r3aDecSigGhost g fsp peerG meG msgG m)) := by
        intro evs_dec hdec_ev
        have htot := hfit (evs_try ++ evs_dec)
          (h_dec_fit w msgG m hm_res evs_try evs_dec htry_ev hdec_ev)
        exact ((fitsEvents_append M lim evs_try evs_dec st).mp htot).2
      have henv_rej_dec : ∀ evs_dec evs_tail,
          sEnvs.decryptSignal (r3aDecSigGhost g fsp peerG meG msgG m) evs_dec →
          FreeOnlyEvs evs_tail →
          ∀ (g' : StoresGhost), ∃ evs, RecvWEnv g (.some meV meG) peerV rest evs ∧
            M.stepEvents (evs_dec ++ evs_tail) st_try = M.stepEvents evs st := by
        intro evs_dec evs_tail hd_ev hf _
        exact ⟨evs_try ++ (evs_dec ++ evs_tail),
          h_dec_end w msgG m hm_res evs_try evs_dec evs_tail htry_ev hd_ev hf,
          (M.stepEvents_append evs_try (evs_dec ++ evs_tail) st).symm⟩
      have henv_join_dec : ∀ evs_dec evs_tail,
          sEnvs.decryptSignal (r3aDecSigGhost g fsp peerG meG msgG m) evs_dec →
          FreeOnlyEvs evs_tail →
          ∀ (g' : StoresGhost) (_out : Bytes), ∃ evs, RecvWEnv g (.some meV meG) peerV rest evs ∧
            M.stepEvents (evs_dec ++ evs_tail) st_try = M.stepEvents evs st := by
        intro evs_dec evs_tail hd_ev hf _ _
        exact ⟨evs_try ++ (evs_dec ++ evs_tail),
          h_dec_end w msgG m hm_res evs_try evs_dec evs_tail htry_ev hd_ev hf,
          (M.stepEvents_append evs_try (evs_dec ++ evs_tail) st).symm⟩
      refine r1c_sepWPp_weaken_pre ?_
        (r3a_after_try_ok_codeOk_fd (peerG := peerG) (meG := meG) (msgG := msgG) (m := m)
          hh hc hslot_ds hdrop hrf hdec hsub63 hsub64 hspb h32 hext hin2 hfd2
          hx19_2 hx20_2 hx21_2 hx26_2 hx28_2 hcoins hfs2 hout2 hfok' hga' htr2_tot
          hfit_dec henv_rej_dec henv_join_dec hpanic hrej hjoin)
      dsimp +zetaDelta only at hsp_sm ⊢
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest)) ∗
          (memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
              (resStack - runFrame - smallRootStack) ∗
            stackAt (runFsp s0) smallRootStack) ∗
          (signalMessageAt A.repAlloc msgG (runFsp s0 + 0x4d0#64) m ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗
            protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
            protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
            coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff ∗
            A.pool lim st_try s2 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
            r3a_restFrame (runFsp s0) ∗ memRegion g.res runResSize ∗
            memRegion g.call 56 ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24) by sep_ac_rfl)) ?_
      rw [hinp_merge, hsp_sm.symm]; exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. Public Top-Level `RunHopRecvWPlacedFd{,Of}` Theorems -/

private theorem run_hop_recvW_of_codeOk_core_fd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {RecvWEnv : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A lim sEnvs S needs))
    (hslot_ds : RunCalleesPlacedFd A lim cEnvs H B slots →
      ∀ stk : Nat, needs.decryptSignal ≤ stk → stk ≤ 2 ^ 63 →
        subroutine_ok (runProgPlaced H) (lsmpl.base 463)
          (withPreFdsGe3Closed (decSigSlotSpecPlacedOf CodeOk A lim sEnvs.decryptSignal S stk)))
    (h_none : ∀ g peerV rest evs, FreeOnlyEvs evs → RecvWEnv g .none peerV rest evs)
    (h_try_fit : ∀ g meV meG peerV rest evs_try, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try →
      RecvWEnv g (.some meV meG) peerV rest evs_try)
    (h_try_err : ∀ g meV meG peerV rest e, SignalMessage.tryFrom protoSignalCodec rest = .error e →
      ∀ evs_try evs_tail, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try → FreeOnlyEvs evs_tail →
        RecvWEnv g (.some meV meG) peerV rest (evs_try ++ evs_tail))
    (h_dec_fit : ∀ g s0 meV meG w peerV rest msgG m,
      SignalMessage.tryFrom protoSignalCodec rest = .ok m →
      ∀ evs_try evs_dec, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try →
        sEnvs.decryptSignal (r3aDecSigGhost g (runFsp s0) (r3aPeerGhost w peerV) meG msgG m) evs_dec →
        RecvWEnv g (.some meV meG) peerV rest (evs_try ++ evs_dec))
    (h_dec_end : ∀ g s0 meV meG w peerV rest msgG m,
      SignalMessage.tryFrom protoSignalCodec rest = .ok m →
      ∀ evs_try evs_dec evs_tail, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try →
        sEnvs.decryptSignal (r3aDecSigGhost g (runFsp s0) (r3aPeerGhost w peerV) meG msgG m) evs_dec →
        FreeOnlyEvs evs_tail →
        RecvWEnv g (.some meV meG) peerV rest (evs_try ++ (evs_dec ++ evs_tail))) :
    RunHopRecvWPlacedFdOf CodeOk A lim cEnvs RecvWEnv H B S slots resStack := by
  intro g st s0 s me peerV rest Q Qp hh hc htry hdrop hres hres64 hspb he hd_fd hcall hstdin hfit
    hpanic hrej hjoin
  rw [hneed_eq] at hres
  cases me with
  | none =>
    exact r3a_recvW_none_codeOk_fd hh hres hres64 he hd_fd.1 hcall hstdin
      (fun evs hf => ⟨evs, h_none g peerV rest evs hf, rfl⟩) hrej
  | some meV meG =>
    exact r3a_recvW_some_codeOk_fd
      (h_try_fit g meV meG peerV rest)
      (h_try_err g meV meG peerV rest)
      (h_dec_fit g s0 meV meG · peerV rest)
      (h_dec_end g s0 meV meG · peerV rest)
      hh hc htry hslot_ds hdrop hres hres64 hspb he hd_fd hcall hstdin hfit hpanic hrej hjoin

/-- `CodeOk`- and `RunSlots`-parametric Whisper hop proof with `FdsGe3Closed` threading. -/
theorem run_hop_recvW_of_codeOk_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A lim sEnvs S needs))
    (hslot_eq : slots.decryptSignal =
      mkSlot (decSigSlotSpecPlacedOf CodeOk A lim sEnvs.decryptSignal S) needs.decryptSignal)
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) := by
      intros; rfl) :
    RunHopRecvWPlacedFdOf CodeOk A lim cEnvs (R3aRecvWEnv sEnvs) H B S slots resStack :=
  run_hop_recvW_of_codeOk_core_fd (sEnvs := sEnvs) (needs := needs) hneed_eq
    (fun hc stk hlo hhi => by
      have hlo' : (slotWithPreFdsGe3Closed slots.decryptSignal).need ≤ stk := by
        change slots.decryptSignal.need ≤ stk
        rw [hslot_eq]; exact hlo
      have h := hc.decryptSignal stk hlo' hhi
      dsimp only [slotWithPreFdsGe3Closed] at h
      rwa [hslot_eq] at h)
    (fun _ _ _ _ hf => hf)
    (fun _ _ _ _ _ _ ht => SeqEnv.inl ht)
    (fun _ _ _ _ _ _ hm _ _ ht hf => by
      dsimp only [R3aRecvWEnv]; rw [hm]
      exact SeqEnv.append ht hf)
    (fun _ _ _ _ w _ _ msgG m hm _ _ ht hd_ev => by
      dsimp only [R3aRecvWEnv]; rw [hm]; rw [hdec_ghost] at hd_ev
      exact SeqEnv.append ht (SeqEnv.inl hd_ev))
    (fun _ _ _ _ w _ _ msgG m hm _ _ _ ht hd_ev hf => by
      dsimp only [R3aRecvWEnv]; rw [hm]; rw [hdec_ghost] at hd_ev
      exact SeqEnv.append ht (SeqEnv.append hd_ev hf))

/-- Envelope-parametric `LibsignalCodeRoLoaded lsmpl` Whisper hop proof at `slotsOfPlaced`. -/
theorem run_hop_recvW_placed_ok_of_env_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {RecvWEnv : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (h_none : ∀ g peerV rest evs, FreeOnlyEvs evs → RecvWEnv g .none peerV rest evs)
    (h_try_fit : ∀ g meV meG peerV rest evs_try, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try →
      RecvWEnv g (.some meV meG) peerV rest evs_try)
    (h_try_err : ∀ g meV meG peerV rest e, SignalMessage.tryFrom protoSignalCodec rest = .error e →
      ∀ evs_try evs_tail, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try → FreeOnlyEvs evs_tail →
        RecvWEnv g (.some meV meG) peerV rest (evs_try ++ evs_tail))
    (h_dec_fit : ∀ g s0 meV meG w peerV rest msgG m,
      SignalMessage.tryFrom protoSignalCodec rest = .ok m →
      ∀ evs_try evs_dec, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try →
        sEnvs.decryptSignal (r3aDecSigGhost g (runFsp s0) (r3aPeerGhost w peerV) meG msgG m) evs_dec →
        RecvWEnv g (.some meV meG) peerV rest (evs_try ++ evs_dec))
    (h_dec_end : ∀ g s0 meV meG w peerV rest msgG m,
      SignalMessage.tryFrom protoSignalCodec rest = .ok m →
      ∀ evs_try evs_dec evs_tail, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try →
        sEnvs.decryptSignal (r3aDecSigGhost g (runFsp s0) (r3aPeerGhost w peerV) meG msgG m) evs_dec →
        FreeOnlyEvs evs_tail →
        RecvWEnv g (.some meV meG) peerV rest (evs_try ++ (evs_dec ++ evs_tail))) :
    RunHopRecvWPlacedFd (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs RecvWEnv
      H B S needs resStack :=
  run_hop_recvW_of_codeOk_core_fd
    (CodeOk := LibsignalCodeRoLoaded lsmpl)
    (slots := slotsOfPlaced A lim sEnvs S needs)
    (sEnvs := sEnvs) (needs := needs) rfl
    (fun hc stk hlo hhi => by
      have h := hc.decryptSignal stk hlo hhi
      refine subroutine_ok_mono h (fun _ _ _ hpre => ?_) (fun _ _ _ _ hpost => hpost)
      dsimp only [slotWithPreFdsGe3Closed, slotsOfPlaced, mkSlot, withPreFdsGe3Closed,
        decSigSlotSpecPlacedOf, decSigSlotSpecPlaced, withCodeOk, withLsCodeRoLoaded] at hpre ⊢
      exact hpre)
    h_none h_try_fit h_try_err h_dec_fit h_dec_end

/-- Whisper hop proof at `LibsignalCodeRoLoaded lsmpl`, `slotsOfPlaced`, and `R3aRecvWEnv sEnvs`. -/
theorem run_hop_recvW_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) := by
      intros; rfl) :
    RunHopRecvWPlacedFd (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs (R3aRecvWEnv sEnvs)
      H B S needs resStack :=
  run_hop_recvW_placed_ok_of_env_fd
    (fun _ _ _ _ hf => hf)
    (fun _ _ _ _ _ _ ht => SeqEnv.inl ht)
    (fun _ _ _ _ _ _ hm _ _ ht hf => by
      dsimp only [R3aRecvWEnv]; rw [hm]
      exact SeqEnv.append ht hf)
    (fun _ _ _ _ w _ _ msgG m hm _ _ ht hd_ev => by
      dsimp only [R3aRecvWEnv]; rw [hm]; rw [hdec_ghost] at hd_ev
      exact SeqEnv.append ht (SeqEnv.inl hd_ev))
    (fun _ _ _ _ w _ _ msgG m hm _ _ _ ht hd_ev hf => by
      dsimp only [R3aRecvWEnv]; rw [hm]; rw [hdec_ghost] at hd_ev
      exact SeqEnv.append ht (SeqEnv.append hd_ev hf))

/-- `LibsignalFrozen lsmpl` specialization of `run_hop_recvW_of_codeOk_placed_ok_fd` at
`slotsOfSigPkFrozenPlaced`. -/
theorem run_hop_recvW_frozen_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) := by
      intros; rfl) :
    RunHopRecvWPlacedFdOf (LibsignalFrozen lsmpl) A lim cEnvs (R3aRecvWEnv sEnvs) H B S
      (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) resStack :=
  run_hop_recvW_of_codeOk_placed_ok_fd
    (CodeOk := LibsignalFrozen lsmpl)
    (slots := slotsOfSigPkFrozenPlaced A lim sEnvs S needs)
    (sEnvs := sEnvs) (needs := needs) rfl rfl hdec_ghost

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetFd
