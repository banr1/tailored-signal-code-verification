/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded `signal_session::run` Placed Arm `R3b`: PreKey Arm Proof

Defines the `Recv`-PreKey allocation-event envelope `R3bRecvPEnv` and proves
`run_hop_recvP_placed_ok`, `run_hop_recvP_of_codeOk_placed_ok`, and `run_hop_recvP_frozen_placed_ok`
on Block `579` (`runProgPlaced H`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111 lsmpl lsρ)
open CryptoVerification.E2E.Pqxdh.ResponderWire (preKeyTryFromStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (PreKeyMsgGhost preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.SignalSession.Cli
  (StoresGhost cliKyberPreKeyVtSym cliPreKeyVtSym cliSignedPreKeyVtSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV RunCall cliWrOk coinsInstalledPlaced coinsOf inputOf namedWrites runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_555)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Bytes DecPkGhost InRunPlaced MeAtDispatch PksmGhost R3bCodeOk RunHistOk RunNeeds RunSem
   addrNameHeap decResAt mkSlot pksmResAt r3b_W30 r3b_W5 r3b_addr_pack r3b_calleeSavedVRegs_q0
   r3b_calleeSavedVRegs_q1 r3b_calleeSavedVRegs_q2 r3b_calleeSavedVRegs_setMem
   r3b_calleeSavedVRegs_setPC r3b_calleeSavedVRegs_setPState r3b_calleeSavedVRegs_writeReg64
   r3b_extractLsb_append_hi r3b_extractLsb_append_lo r3b_files_of_trace_eq r3b_fs_setMem
   r3b_fs_setPC r3b_fs_setPState r3b_fs_writeReg64 r3b_fs_writeVReg128 r3b_hist_of_eq
   r3b_inRun_step r3b_mem240_to_slot30 r3b_mem40_to_slot5 r3b_mem_setPState r3b_perm
   r3b_perm_post r3b_pkm_to_words r3b_readReg64_setPState r3b_sepWPp_exists_left
   r3b_sepWPp_pure_left r3b_sepWPp_weaken_pre r3b_slot30 r3b_slot5 r3b_slot5_to_mem40
   r3b_sp_setPState r3b_split_at r3b_stOf r3b_stackAt_split_ge r3b_status_setPState
   r3b_symtab_setPState r3b_trace_setPState runFiles runFsp runLocalBytes runPcPlaced
   runPcPlaced_eq runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget
  (r3bFreeCapEvs r3bFreeCapEvs_freeOnly r3bFreeMePeerEvs r3bFreeMePeerEvs_freeOnly
   r3b_me_none_placed r3b_recv_head_some_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget
  (r3b_call_lscro r3b_call_raw)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget
  (RunHopRecvPPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudgetAux
  (r3b_recvP_dec_ok_placed r3b_recvP_dec_ok_placed_any r3b_recvP_from_dcc_placed
   r3b_recvP_from_dcc_placed_any)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudget
  (r3b_recvP_dec_err_placed r3b_recvP_parse_err_placed r3b_recvP_shuf1_placed
   r3b_recvP_shuf2_placed r3b_sepWP_with_vm_oom r3b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decPkSlotSpecPlaced slotFramePlaced slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (runNeed_bounds_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgBudget
  (dropPreKeyMsgSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (pksmSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs dropPreKeyMsg_placed_ok)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudgetAux
  (r3b_recvP_from_dcc_placed r3b_recvP_from_dcc_placed_any
   r3b_recvP_dec_ok_placed r3b_recvP_dec_ok_placed_any)

scoped syntax "by_vm_open " tacticSeq : tactic
scoped elab_rules : tactic
  | `(tactic| by_vm_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply r3b_sepWP_with_vm_oom))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_open: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm]
  runPcPlaced_eq BitVec.ofNat_eq_ofNat
  r3b_extractLsb_append_lo r3b_extractLsb_append_hi
  r3b_calleeSavedVRegs_q0 r3b_calleeSavedVRegs_q1 r3b_calleeSavedVRegs_q2
  r3b_calleeSavedVRegs_writeReg64
  r3b_calleeSavedVRegs_setPC r3b_calleeSavedVRegs_setMem r3b_calleeSavedVRegs_setPState
  r3b_readReg64_setPState r3b_sp_setPState r3b_mem_setPState r3b_status_setPState
  r3b_trace_setPState r3b_symtab_setPState r3b_fs_setPState
  r3b_fs_writeReg64 r3b_fs_writeVReg128 r3b_fs_setPC r3b_fs_setMem

/-! ## 1. Canonical Ghost Carriers & `R3bRecvPEnv` -/

def r3bCanonicalAddrGhost (v : AddrV) : AddrGhost :=
  { name := { cap := 0#64, ptr := 0#64, bytes := v.name }, device := v.device }

def r3bCanonicalPmGhost : PreKeyMsgGhost :=
  { msg := { pqCap := 0#64, pqPtr := 0#64, ctPtr := 0#64, addrPtr := 0#64, serPtr := 0#64 }
    serPtr := 0#64
    kyberPtr := 0#64 }

def r3bPksmGhost (rest : Bytes) : PksmGhost :=
  { ptr := 0#64, bytes := rest, ret := 0#64 }

def r3bDecPkGhost (g : RunCall) (meV peerV : AddrV) (pm : PreKeySignalMessage) : DecPkGhost :=
  { peer := r3bCanonicalAddrGhost peerV
    peerA := 0#64
    me := r3bCanonicalAddrGhost meV
    meA := 0#64
    stores := g.stores
    ret := 0#64
    coinsP := g.coins
    F := runFiles g.i
    coins := coinsOf g.i
    msgA := 0#64
    msgG := r3bCanonicalPmGhost
    msg := pm }

/-- Allocation-event envelope for `signal_session::run` Arm `R3b` (`g.c = .recv peerV`,
`g.i.stdin = 3#8 :: rest`):
- `me = .none`: deallocation-only (`FreeOnlyEvs`);
- `me = .some meV _`, `S.pksmParse rest = none`: `PksmTryFromEnv` followed by `FreeOnlyEvs`;
- `me = .some meV _`, `S.pksmParse rest = some pm`: `PksmTryFromEnv`, then `sEnvs.decryptPrekey`,
  then `FreeOnlyEvs`. -/
def R3bRecvPEnv (S : RunSem) (sEnvs : RunSlotEnvs)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop)
    (g : RunCall) (me : MeAtDispatch) (peerV : AddrV) (rest : Bytes) :
    List AllocEvent → Prop :=
  match me with
  | .none => FreeOnlyEvs
  | .some meV _ =>
    match S.pksmParse rest with
    | none => SeqEnv (PksmTryFromEnv (r3bPksmGhost rest)) FreeOnlyEvs
    | some pm =>
      SeqEnv (PksmTryFromEnv (r3bPksmGhost rest))
        (SeqEnv (sEnvs.decryptPrekey (r3bDecPkGhost g meV peerV pm)) FreeOnlyEvs)

/-! ## 2. Main Hop Theorem: `run_hop_recvP_placed_ok` -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded relocatable (`[LibsignalPlacement]`) Arm `R3b` PreKey hop theorem
(`run_hop_recvP_placed_ok`). -/
theorem run_hop_recvP_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmTryFromEnv x = PksmTryFromEnv y := by
      intros; rfl)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y := by intros; rfl) :
    RunHopRecvPPlaced (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs PksmTryFromEnv
      (R3bRecvPEnv S sEnvs PksmTryFromEnv) H B S needs resStack := by
  unfold RunHopRecvPPlaced
  intro g st s0 s me peerV rest Q Qp hh hc hpksm hdrop hres hres64 hspb he hd hcall hstdin hfit
    hpanic hrej hjoin
  cases me with
  | none =>
    exact r3b_me_none_placed hh hres hres64 he hd hcall
      (fun cap => ⟨r3bFreeCapEvs cap, r3bFreeCapEvs_freeOnly cap, rfl⟩) hrej
  | some meV meG =>
    have hbnds := runNeed_bounds_placed hres hres64
    rcases hbnds with ⟨hrf_le, hsub63, hsub64, _, _, _, _, _, _, _, _, _, _,
      hpk_stk, hstk32, _, hext_le, _, _, _, hdp_stk, _⟩
    obtain ⟨hrest32, hcoins63, _, hfilesOk, hdecPkOk, hga⟩ :=
      hd.recvP_facts he hcall hstdin
    refine r3b_recv_head_some_placed hd hcall ?_
    intro s1 peerG cw4 hiMe hs1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1
      htr1 hfs1 hpeer_val hme_val hdev_cw4 hhi
    let fsp := runFsp s0
    have hfsp_sub : resStack - runFrame ≤ fsp.toNat := by
      dsimp only [fsp, runFsp, runFrame] at hrf_le ⊢
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 10832 ≤ s0.sp.toNat; omega))]
      change resStack - 10832 ≤ s0.sp.toNat - 10832
      omega
    have hinp_c : inputOf g.i g.c = 3#8 :: rest := by simp [hcall, inputOf, CallV.tag, hstdin]
    have hlen_ne : BitVec.ofNat 64 (3#8 :: rest).length ≠ 0#64 := by
      rw [List.length_cons]
      intro h0
      have hv := congrArg BitVec.toNat h0
      have hzero : (0#64).toNat = 0 := rfl
      rw [BitVec.toNat_ofNat, hzero] at hv
      have hmod : (rest.length + 1) % 2 ^ 64 = rest.length + 1 := Nat.mod_eq_of_lt (by omega)
      omega
    have hbeq_len : (BitVec.ofNat 64 (3#8 :: rest).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hlen_ne
    have hsub1_nat : (BitVec.ofNat 64 (3#8 :: rest).length - 1#64).toNat = rest.length := by
      rw [List.length_cons]
      have h1 : BitVec.ofNat 64 (rest.length + 1) - 1#64 = BitVec.ofNat 64 rest.length := by
        rw [BitVec.ofNat_add]; bv_omega
      rw [h1, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have h280_pkm : memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) =
        memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
          memRegion (fsp + 0x4d0#64) 248 ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) := by
      rw [r3b_split_at fsp 0x280 (0x4d0 - 0x280) runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x4d0 248 runLocalBytes (by decide) (by decide)]
    let pkX : PksmGhost := { ptr := g.inp + 1#64, bytes := rest, ret := fsp + 0x4d0#64 }
    have hpk_eq : PksmTryFromEnv pkX = PksmTryFromEnv (r3bPksmGhost rest) :=
      hpksm_addr pkX (r3bPksmGhost rest) rfl
    have hfit_pk0 : FitsEnv M lim st (PksmTryFromEnv (r3bPksmGhost rest)) := by
      dsimp only [R3bRecvPEnv] at hfit
      rcases hp0 : S.pksmParse rest with _ | _ <;>
        (rw [hp0] at hfit; exact hfit.seq_left)
    have hfit_pk : FitsEnv M lim st (PksmTryFromEnv pkX) := by
      rw [hpk_eq]; exact hfit_pk0
    rw [hinp_c] at hx24_1
    rw [hinp_c, pointsToBytes_cons, h280_pkm]
    have hpc1 : s1.pc = runPcPlaced 0x7c8 := hs1.pc
    rw [runPcPlaced_eq] at hpc1
    have hrun1 : s1.status = .Running := hs1.run
    have hsp1 : s1.sp = fsp := hs1.sp
    have hsp1_al : s1.spAligned = true := hs1.spAligned_cur
    apply r3b_seq_lscro_oom (mid := blkPl_111.base) hs1.inv
    rw [← hsp1]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm]; rfl)
        (by simp only [wp_norm, arm64_norm, hrun1])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_pk hinv_pk => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s1 (r3b_stOf hinv_pk) hvm_pk]
      have hstk_pk := r3b_stackAt_split_ge s1.sp hpk_stk hsub64
      refine r3b_call_raw
        (F := memRegion g.res runResSize ∗
          memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗
          (g.inp ↦₈ 3#8) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗
          tokenInitPlacedAt ∗
          addrNameHeap A.repAlloc meG ∗
          addrNameHeap A.repAlloc peerG ∗
          runSaved s0 ∗
          memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗
            ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
          memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - preKeyTryFromStack))
        (pkX, st)
        hpksm hinv_pk
        (by simp only [r3b_stOf, wp_norm, arm64_norm]; rfl)
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun1])
        (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp1_al)
        (retAddr := runPcPlaced 0x994)
        (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        ?_
        (hpanic := fun _ _ _ hp => by
          dsimp only [pksmSlotSpecPlaced, withLsCodeRoLoaded] at hp
          exact (not_satisfies_false_sepConj hp).elim)
        (hoom := fun _ _ _ ho => by
          dsimp only [pksmSlotSpecPlaced, withLsCodeRoLoaded] at ho
          exact (not_satisfies_false_sepConj ho).elim)
        (hnext := fun s2 hsteps_pk hinv2 hpcm2 hrun2 hsp2 hcsm2 => ?_)
      · dsimp only [pksmSlotSpecPlaced, withLsCodeRoLoaded, pkX, r3b_stOf]
        simp only [sepConj_assoc]
        apply Entails.pure_right
        · exact ⟨by simp only [wp_norm, arm64_norm]; try rw [hx23_1],
            by simp only [wp_norm, arm64_norm]; exact hsub1_nat,
            hrest32,
            by simp only [wp_norm, arm64_norm]; try rw [hsp1],
            by
              have hpk_spb : preKeyTryFromStack ≤ fsp.toNat :=
                Nat.le_trans hpk_stk hfsp_sub
              simpa only [wp_norm, arm64_norm, hsp1] using hpk_spb,
            hfit_pk⟩
        rw [hsp1] at hstk_pk
        rw [hstk_pk]
        simp only [wp_norm, arm64_norm]
        try rw [hsp1]
        exact r3b_perm_post
          (Entails.pure_right hinv_pk (Entails.refl _))
          (by dsimp only [fsp, r3b_stOf]; simp only [wp_norm, arm64_norm]; sep_ac_rfl)
      · dsimp only [pksmSlotSpecPlaced, withLsCodeRoLoaded, pkX]
        simp only [sepExists_sepConj_left]
        apply r3b_sepWPp_exists_left; intro evs_pk
        simp only [sepConj_assoc]
        apply r3b_sepWPp_pure_left; rintro ⟨htr_pk, hpk_ev⟩
        let st_pk := M.stepEvents evs_pk st
        have hpk_ev0 : PksmTryFromEnv (r3bPksmGhost rest) evs_pk := by
          rw [← hpk_eq]; exact hpk_ev
        have hs2 : InRunPlaced R3bCodeOk s0 s2 0x994 :=
          r3b_inRun_step hs1 hpcm2 hrun2 (hsp2.trans (by simp only [r3b_stOf, wp_norm, arm64_norm]))
            (hcsm2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])) hinv2
            (hcsm2.2.2.2.2.2.2.2.2.2.2.2.trans
              (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm]))
        have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores :=
          hcsm2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19_1])
        have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res :=
          hcsm2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20_1])
        have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap :=
          hcsm2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21_1])
        have hx26_2 : s2.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 :=
          hcsm2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm]; exact hx26_1)
        have hx27_2 : s2.readReg64 (.gpr 27#5) = fsp + 0x1750#64 :=
          hcsm2.2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm]; exact hx27_1)
        have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr :=
          hcsm2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm]; exact hx28_1)
        have htr2_eq : s2.trace = s.trace :=
          (htr_pk.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])).trans htr1
        have hfs2_files : s2.fs.files = runFiles g.i :=
          ((r3b_files_of_trace_eq (hh.fs (runProgPlaced H) 579) hsteps_pk htr_pk).trans
            (by simp only [r3b_stOf, wp_norm, arm64_norm])).trans
            ((congrArg FsState.files hfs1).trans hd.fs)
        have htr2 : s0.trace <+: s2.trace := htr2_eq ▸ hd.trace
        have hhist2 : RunHistOk g.i s0 s2 :=
          ⟨hfs2_files, htr2_eq ▸ hd.stdout⟩
        rw [← hsp2, hs2.sp]
        rw [hsp1] at hstk_pk
        apply r3b_sepWPp_weaken_pre
          (r3b_perm
            (sepConj_mono_left
              (Q := pksmResAt A.repAlloc (fsp + 0x4d0#64) (S.pksmParse rest) ∗
                ((g.inp + 1#64) ↦ₛ rest) ∗ lsLogOff ∗ A.pool lim st_pk s2 ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦₈ 3#8) ∗
                coinsInstalledPlaced g.coins (coinsOf g.i) ∗
                tokenInitPlacedAt ∗
                addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
                memRegion fsp 0x220 ∗
                (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                  ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                  ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
                memRegion (fsp + 0x240#64) 0x20 ∗
                (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                  ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                  ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
                memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
                memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8))
              (Entails.of_eq hstk_pk.symm))
            (by dsimp only [fsp, st_pk]; sep_ac_rfl))
        rcases _hparse : S.pksmParse rest with _ | pm
        · (try rw [_hparse] at hga); dsimp only at hga
          have henv_parse_err : ∀ evs_drop, FreeOnlyEvs evs_drop →
              ∃ evs, R3bRecvPEnv S sEnvs PksmTryFromEnv g (.some meV meG) peerV rest evs ∧
                M.stepEvents (evs_drop ++ r3bFreeMePeerEvs meG peerG) st_pk =
                  M.stepEvents evs st := by
            intro evs_drop hfree_drop
            refine ⟨evs_pk ++ (evs_drop ++ r3bFreeMePeerEvs meG peerG), ?_, ?_⟩
            · simp only [R3bRecvPEnv, _hparse]
              exact SeqEnv.append hpk_ev0
                (FreeOnlyEvs.append hfree_drop (r3bFreeMePeerEvs_freeOnly meG peerG))
            · dsimp only [st_pk]
              exact (M.stepEvents_append evs_pk _ st).symm
          refine r3b_sepWPp_weaken_pre ?_
            (r3b_recvP_parse_err_placed meG peerG cw4 hiMe hh hdrop hstk32 hext_le hsub64 hs2
              hx19_2 hx20_2 hx21_2 hx26_2 hx28_2 htr2 hhist2 hga henv_parse_err hrej)
          rw [hinp_c, pointsToBytes_cons]
          have hany :
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗
                tokenInitPlacedAt ∗ lsLogOff ⊢ anyHeap :=
            entails_anyHeap _
          exact r3b_perm
            (r3b_perm_post
              (sepConj_mono hany
                (Entails.refl (pksmResAt A.repAlloc (fsp + 0x4d0#64) none ∗
                  (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                  stackAt fsp (resStack - runFrame) ∗ A.pool lim st_pk s2 ∗
                  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                  storesAt A.repAlloc g.stores StoresGhost.opened ∗
                  addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
                  memRegion fsp 0x220 ∗
                  (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                    ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                    ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
                  memRegion (fsp + 0x240#64) 0x20 ∗
                  (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                    ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                    ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
                  memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
                  memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8))))
              (by dsimp only [fsp]; sep_ac_rfl))
            (by dsimp only [fsp, pksmResAt]; sep_ac_rfl)
        · (try rw [_hparse] at hga); dsimp only at hga
          have hdp_ok := hdecPkOk pm (by first | exact rfl | exact _hparse)
          have hfit_pm : FitsEnv M lim st
              (SeqEnv (PksmTryFromEnv (r3bPksmGhost rest))
                (SeqEnv (sEnvs.decryptPrekey (r3bDecPkGhost g meV peerV pm)) FreeOnlyEvs)) := by
            simpa only [R3bRecvPEnv, _hparse] using hfit
          have hfit_dp0 :
              FitsEnv M lim st_pk (sEnvs.decryptPrekey (r3bDecPkGhost g meV peerV pm)) :=
            (hfit_pm.seq_right hpk_ev0).seq_left
          have hloc_shuf :
              pksmResAt A.repAlloc (fsp + 0x4d0#64) (some pm) ∗
                (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                  ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                  ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
                (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                  ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                  ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
                addrNameHeap A.repAlloc peerG ∗ addrNameHeap A.repAlloc meG ∗
                memRegion fsp 0x220 ∗
                memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
                memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ⊢
              ∃∗ pmG : PreKeyMsgGhost, ∃∗ w : r3b_W30,
                ∃∗ t0 : r3b_W5, ∃∗ t : r3b_W5, ∃∗ z : r3b_W30, ∃∗ m : r3b_W30,
                  ⌜pmG.msg.pqCap.toNat < 2 ^ 63⌝ ∗
                  ((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗
                  r3b_slot30 (fsp + 0x4d8#64) w ∗
                  r3b_slot5 (fsp + 0x2a0#64) t ∗
                  r3b_slot30 (fsp + 0x3e0#64) z ∗
                  r3b_slot30 (fsp + 0x1750#64) m ∗
                  r3b_slot5 fsp t0 ∗
                  ((((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (fsp + 0x4d8#64) w) -∗
                    preKeyMsgAt A.repAlloc pmG (fsp + 0x4d0#64) pm) ∗
                  protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
                  protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
                  memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                  memRegion (fsp + 0x280#64) 0x20 ∗
                  memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                  memRegion (fsp + 0x320#64) 48 ∗
                  memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                  memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                  memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                  anyHeap := by
            dsimp only [pksmResAt]
            have hf0 : memRegion fsp 0x220 =
                memRegion fsp 40 ∗ memRegion (fsp + 0x28#64) (0x220 - 0x28) :=
              ProofLib.memRegion_split' (b := fsp) (n := 40) (k := 504)
                (b' := fsp + 0x28#64) rfl (by bv_omega) (by decide)
            have hf280 : memRegion (fsp + 0x280#64) (0x4d0 - 0x280) =
                memRegion (fsp + 0x280#64) 0x20 ∗
                  memRegion (fsp + 0x2a0#64) 40 ∗
                  memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                  memRegion (fsp + 0x320#64) 48 ∗
                  memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                  memRegion (fsp + 0x3e0#64) 240 := by
              rw [r3b_split_at fsp 0x280 0x20 0x4d0 (by decide) (by decide),
                  r3b_split_at fsp 0x2a0 40 0x4d0 (by decide) (by decide),
                  r3b_split_at fsp 0x2c8 (0x320 - 0x2c8) 0x4d0 (by decide) (by decide),
                  r3b_split_at fsp 0x320 48 0x4d0 (by decide) (by decide),
                  r3b_split_at fsp 0x350 (0x3e0 - 0x350) 0x4d0 (by decide) (by decide)]
            have hf5c8 : memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) =
                memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                  memRegion (fsp + 0x1750#64) 240 ∗
                  memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) := by
              rw [r3b_split_at fsp 0x5c8 (0x1750 - 0x5c8) runLocalBytes (by decide) (by decide),
                  r3b_split_at fsp 0x1750 240 runLocalBytes (by decide) (by decide)]
            rw [hf0, hf280, hf5c8]
            have hp_pack := r3b_addr_pack A.repAlloc peerG (fsp + 0x220#64) (fsp + 0x228#64)
              (fsp + 0x230#64) (fsp + 0x238#64) cw4 (by bv_omega) (by bv_omega) (by bv_omega)
              hdev_cw4
            have hm_pack := r3b_addr_pack A.repAlloc meG (fsp + 0x260#64) (fsp + 0x268#64)
              (fsp + 0x270#64) (fsp + 0x278#64) hiMe (by bv_omega) (by bv_omega) (by bv_omega) hhi
            simp only [sepExists_sepConj_left]
            apply Entails.sepExists_elim; intro pmG
            refine Entails.trans
              (r3b_perm
                (sepConj_mono (r3b_pkm_to_words A.repAlloc pmG (fsp + 0x4d0#64) pm)
                  (sepConj_mono (r3b_mem40_to_slot5 fsp)
                    (sepConj_mono (r3b_mem40_to_slot5 (fsp + 0x2a0#64))
                      (sepConj_mono (r3b_mem240_to_slot30 (fsp + 0x3e0#64))
                        (sepConj_mono (r3b_mem240_to_slot30 (fsp + 0x1750#64))
                          (sepConj_mono hp_pack (sepConj_mono hm_pack
                            (Entails.refl (memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                              memRegion (fsp + 0x280#64) 0x20 ∗
                              memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                              memRegion (fsp + 0x320#64) 48 ∗
                              memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                              memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                              memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                              anyHeap)))))))))
                (by ac_rfl)) ?_
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply Entails.sepExists_elim; intro m
            apply Entails.sepExists_elim; intro z
            apply Entails.sepExists_elim; intro t
            apply Entails.sepExists_elim; intro t0
            apply Entails.sepExists_elim; intro w
            simp only [sepConj_assoc]
            apply Entails.pure_left; intro hcap_pm
            have ha4d8 : fsp + 0x4d0#64 + 8#64 = fsp + 0x4d8#64 := by bv_omega
            rw [ha4d8]
            exact Entails.sepExists_right pmG (Entails.sepExists_right w
              (Entails.sepExists_right t0 (Entails.sepExists_right t
                (Entails.sepExists_right z (Entails.sepExists_right m
                  (Entails.pure_right hcap_pm (Entails.of_eq (by ac_rfl))))))))
          apply r3b_sepWPp_weaken_pre
            (r3b_perm
              (sepConj_mono_left
                (Q := (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                  stackAt fsp (resStack - runFrame) ∗ A.pool lim st_pk s2 ∗
                  coinsInstalledPlaced g.coins (coinsOf g.i) ∗
                  tokenInitPlacedAt ∗ lsLogOff ∗
                  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                  storesAt A.repAlloc g.stores StoresGhost.opened ∗
                  runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)
                hloc_shuf)
              (by dsimp only [fsp]; sep_ac_rfl))
          simp only [sepExists_sepConj_left]
          apply r3b_sepWPp_exists_left; intro pmG
          apply r3b_sepWPp_exists_left; intro w
          apply r3b_sepWPp_exists_left; intro t0
          apply r3b_sepWPp_exists_left; intro t
          apply r3b_sepWPp_exists_left; intro z
          apply r3b_sepWPp_exists_left; intro m
          simp only [sepConj_assoc]
          apply r3b_sepWPp_pure_left; intro hcap_pm
          refine r3b_sepWPp_weaken_pre (Entails.of_eq (by dsimp only [fsp]))
            (r3b_recvP_shuf1_placed pmG.msg.pqCap w t z m _ hs2 hcap_pm hx26_2 hx27_2 ?_)
          intro s3 hvm3 hs3 hx8_3 hx9_3 hx19_3 hx20_3 hx21_3 hx26_3 hx28_3 htr3 hfs3
          rw [hx19_2] at hx19_3
          rw [hx20_2] at hx20_3
          rw [hx21_2] at hx21_3
          rw [hx26_2] at hx26_3
          rw [hx28_2] at hx28_3
          let shuf2F : SepProp :=
            (((runFsp s0 + 1232#64) ↦₆₄ pmG.msg.pqCap ∗ r3b_slot30 (runFsp s0 + 1240#64) w) -∗
              preKeyMsgAt A.repAlloc pmG (runFsp s0 + 1232#64) pm) ∗
            memRegion (runFsp s0 + 672#64) 40 ∗
            memRegion (runFsp s0 + 5968#64) 240 ∗
            protocolAddressAt A.repAlloc peerG (runFsp s0 + 544#64) ∗
            protocolAddressAt A.repAlloc meG (runFsp s0 + 608#64) ∗
            memRegion (runFsp s0 + 40#64) (544 - 40) ∗
            memRegion (runFsp s0 + 640#64) 32 ∗
            memRegion (runFsp s0 + 712#64) (800 - 712) ∗
            memRegion (runFsp s0 + 800#64) 48 ∗
            memRegion (runFsp s0 + 848#64) (992 - 848) ∗
            memRegion (runFsp s0 + 1480#64) (5968 - 1480) ∗
            memRegion (runFsp s0 + 6208#64) (runLocalBytes - 6208) ∗
            anyHeap ∗
            (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗
            A.pool lim st_pk s2 ∗
            coinsInstalledPlaced g.coins (coinsOf g.i) ∗
            tokenInitPlacedAt ∗
            lsLogOff ∗
            memRegion g.res runResSize ∗
            memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗
            runSaved s0 ∗
            memRegion (runFsp s0 + 576#64) 32
          refine r3b_sepWPp_weaken_pre (Entails.of_eq (by dsimp only [fsp, shuf2F]; sep_ac_rfl))
            (r3b_recvP_shuf2_placed g.stores pmG.msg.pqCap t0 w z shuf2F hs3 hx8_3 hx9_3 hx19_3 ?_)
          intro sc hvm_c hinv_c hpc_c hrun_c hsp_c hsp_al_c hlr_c
            hx0_c hx1_c hx2_c hx3_c hx4_c hx5_c hx6_c hx7_c hx8_c
            hx19_c hx20_c hx21_c hx26_c hx28_c hfp_c hvregs_c htr_c hfs_c
          rw [hx20_3] at hx20_c
          rw [hx21_3] at hx21_c
          rw [hx26_3] at hx26_c
          rw [hx28_3] at hx28_c
          have htr_sc_eq : sc.trace = s2.trace := htr_c.trans htr3
          have hfs_sc_files : sc.fs.files = runFiles g.i :=
            (congrArg FsState.files (hfs_c.trans hfs3)).trans hfs2_files
          have htr_sc : s0.trace <+: sc.trace := htr_sc_eq ▸ htr2
          have hpool_sc : A.pool lim st_pk s2 = A.pool lim st_pk sc :=
            ((A.pool_transport lim st_pk s3 sc hvm_c).trans
              (A.pool_transport lim st_pk s2 s3 hvm3)).symm
          let dpX : DecPkGhost :=
            { peer := peerG
              peerA := fsp + 0x220#64
              me := meG
              meA := fsp + 0x260#64
              stores := g.stores
              ret := fsp + 0x320#64
              coinsP := g.coins
              F := runFiles g.i
              coins := coinsOf g.i
              msgA := fsp + 0x4d0#64
              msgG := pmG
              msg := pm }
          have hdp_eq :
              sEnvs.decryptPrekey dpX = sEnvs.decryptPrekey (r3bDecPkGhost g meV peerV pm) :=
            hdp_ghost dpX (r3bDecPkGhost g meV peerV pm) hpeer_val hme_val rfl rfl rfl rfl rfl
          have hfit_dp : FitsEnv M lim st_pk (sEnvs.decryptPrekey dpX) := by
            rw [hdp_eq]; exact hfit_dp0
          refine r3b_call_raw
            (F := memRegion (fsp + 0x3e0#64) 240 ∗
              memRegion (fsp + 0x2a0#64) 40 ∗
              memRegion (fsp + 0x1750#64) 240 ∗
              memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
              memRegion (fsp + 0x280#64) 0x20 ∗
              memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
              memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
              memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
              memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
              anyHeap ∗
              (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)
            (dpX, st_pk)
            (hc.decryptPrekey (resStack - runFrame) hdp_stk hsub63) hinv_c
            hpc_c hrun_c hsp_al_c (retAddr := runPcPlaced 0xb78) hlr_c
            ?_
            (hpanic := fun sf R' _ hp => by
              dsimp only [slotsOfPlaced, mkSlot, decPkSlotSpecPlaced,
                LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlaced,
                withLsCodeRoLoaded, dpX] at hp
              rw [sepConj_assoc, satisfies_pure_sepConj] at hp
              have hnone := hp.1
              rw [hpeer_val, hme_val] at hnone
              apply hpanic sf _ (Or.inl ?_)
              rw [hga, hnone]; rfl)
            (hoom := fun _ _ _ ho => by
              dsimp only [slotsOfPlaced, mkSlot, decPkSlotSpecPlaced,
                LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlaced,
                withLsCodeRoLoaded, dpX] at ho
              exact (not_satisfies_false_sepConj ho).elim)
            (hnext := fun s4 _ hinv4 hpcm4 hrun4 hsp4 hcsm4 => ?_)
          · dsimp only [slotsOfPlaced, mkSlot, decPkSlotSpecPlaced,
              LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlaced,
              slotFramePlaced,
              LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
              withLsCodeRoLoaded, dpX, shuf2F]
            rw [hpool_sc]
            simp only [sepConj_assoc]
            apply Entails.pure_right
            · exact ⟨hx0_c, hx1_c, hx2_c, hx3_c, hx4_c, hx5_c, hx6_c, hx7_c, hx8_c, hfs_sc_files,
                by rw [hpeer_val, hme_val]; exact hfilesOk,
                by rw [hpeer_val, hme_val]; exact hdp_ok,
                hsp_c ▸ hfsp_sub,
                hfit_dp⟩
            apply Entails.pure_right
            · exact hcoins63
            rw [hsp_c]
            have hpkm_restore :
                ((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (fsp + 0x4d8#64) w ∗
                  ((((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (fsp + 0x4d8#64) w) -∗
                    preKeyMsgAt A.repAlloc pmG (fsp + 0x4d0#64) pm) ⊢
                preKeyMsgAt A.repAlloc pmG (fsp + 0x4d0#64) pm := by
              rw [← sepConj_assoc]
              exact Entails.wand_elim _ _
            exact r3b_perm
              (r3b_perm_post
                (Entails.pure_right hinv_c
                  (sepConj_mono hpkm_restore
                    (Entails.refl ((fsp ↦₆₄ lsρ cliPreKeyVtSym) ∗
                      ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                      ((fsp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
                      ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                      ((fsp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
                      memRegion (fsp + 0x3e0#64) 240 ∗
                      memRegion (fsp + 0x2a0#64) 40 ∗ memRegion (fsp + 0x1750#64) 240 ∗
                      protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
                      protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
                      memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                      memRegion (fsp + 0x280#64) 0x20 ∗
                      memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                      memRegion (fsp + 0x320#64) 48 ∗
                      memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                      memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                      memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                      anyHeap ∗
                      (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                      stackAt fsp (resStack - runFrame) ∗ A.pool lim st_pk sc ∗
                      coinsInstalledPlaced g.coins (coinsOf g.i) ∗
                      tokenInitPlacedAt ∗ lsLogOff ∗
                      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                      storesAt A.repAlloc g.stores StoresGhost.opened ∗
                      runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20))))
                (by dsimp only [fsp]; sep_ac_rfl))
              (by dsimp only [fsp]; sep_ac_rfl)
          · dsimp only [slotsOfPlaced, mkSlot, decPkSlotSpecPlaced,
              LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlaced,
              withLsCodeRoLoaded, dpX]
            simp only [sepExists_sepConj_left]
            apply r3b_sepWPp_exists_left; intro evs_dp
            apply r3b_sepWPp_exists_left; intro g'
            apply r3b_sepWPp_exists_left; intro e
            simp only [sepConj_assoc]
            apply r3b_sepWPp_pure_left; rintro ⟨hdp_ev, ⟨htr_dp, hfs_dp, hout_str_dp⟩, hout_dp⟩
            let st_dp := M.stepEvents evs_dp st_pk
            have hdp_ev0 : sEnvs.decryptPrekey (r3bDecPkGhost g meV peerV pm) evs_dp := by
              rw [← hdp_eq]; exact hdp_ev
            have hs4 : InRunPlaced R3bCodeOk s0 s4 0xb78 :=
              r3b_inRun_step hs3 hpcm4 hrun4 (hsp4.trans (hsp_c.trans hs3.sp.symm))
                (hcsm4.2.2.2.2.2.2.2.2.2.2.1.trans hfp_c) hinv4
                (hcsm4.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_c)
            have htr4 : s0.trace <+: s4.trace := htr_sc.trans htr_dp
            have hhist4 : RunHistOk g.i s0 s4 :=
              ⟨hfs_dp.trans hfs_sc_files, hout_str_dp.trans (htr_sc_eq ▸ htr2_eq ▸ hd.stdout)⟩
            have hx19_4 : s4.readReg64 (.gpr 19#5) = g.stores := hcsm4.1.trans hx19_c
            have hx20_4 : s4.readReg64 (.gpr 20#5) = g.res := hcsm4.2.1.trans hx20_c
            have hx21_4 : s4.readReg64 (.gpr 21#5) = meG.name.cap := hcsm4.2.2.1.trans hx21_c
            have hx26_4 : s4.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 :=
              hcsm4.2.2.2.2.2.2.2.1.trans hx26_c
            have hx28_4 : s4.readReg64 (.gpr 28#5) = meG.name.ptr :=
              hcsm4.2.2.2.2.2.2.2.2.2.1.trans hx28_c
            rw [hsp_c]
            have hpc4 : s4.pc = runPcPlaced 0xb78 := hs4.pc
            rw [runPcPlaced_eq] at hpc4
            have hrun4' : s4.status = .Running := hs4.run
            have hsp4' : s4.sp = fsp := hs4.sp
            have hsp4_al : s4.spAligned = true := hs4.spAligned_cur
            apply r3b_seq_lscro_oom (mid := blkPl_555.base) hs4.inv
            dsimp only [runProgPlaced, lsProg_579]
            by_vm_open (
              wp_steps
              refine SepWP.done
                (by simp only [wp_norm, arm64_norm]; rfl)
                (by simp only [wp_norm, arm64_norm, hrun4'])
                ⟨by simp only [wp_norm, arm64_norm], fun hvm_dm hinv_dm => ?_⟩
              change SepWPp (runProgPlaced H) _ _ _ _ _ _
              rw [← A.pool_transport lim st_dp s4 (r3b_stOf hinv_dm) hvm_dm]
              refine r3b_call_lscro
                (F := storesAt A.repAlloc g.stores g' ∗
                  decResAt A.repAlloc (fsp + 0x320#64) e ∗
                  protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
                  protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
                  (fsp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                  ((fsp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
                  ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                  ((fsp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
                  lsLogOff ∗ anyHeap ∗
                  memRegion (fsp + 0x3e0#64) 240 ∗
                  memRegion (fsp + 0x2a0#64) 40 ∗
                  memRegion (fsp + 0x1750#64) 240 ∗
                  memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                  memRegion (fsp + 0x280#64) 0x20 ∗
                  memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                  memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                  memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                  memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                  anyHeap ∗
                  (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                  runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)
                (⟨fsp + 0x4d0#64, pmG, pm⟩, st_dp)
                (dropPreKeyMsg_placed_ok (callerProg := runProgPlaced H) (i := 579) hh (resStack - runFrame) hstk32 hsub64) hinv_dm
                (by simp only [r3b_stOf, wp_norm, arm64_norm]; rfl)
                (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun4'])
                (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp4_al)
                (retAddr := runPcPlaced 0xb80)
                (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
                ?_
                (hnext := fun s5 hsteps_dm hinv5 hpcm5 hrun5 hsp5 hcsm5 => ?_)
              · dsimp only [dropPreKeyMsgSpec, r3b_stOf]
                simp only [sepConj_assoc]
                apply Entails.pure_right
                · refine ⟨by dsimp only [fsp]; simp only [wp_norm, arm64_norm]; try rw [hx26_4],
                    by simp (config := { decide := true }) only [wp_norm, arm64_norm, runPcPlaced_eq]⟩
                simp only [wp_norm, arm64_norm]
                try rw [hsp4']
                exact Entails.of_eq (by dsimp only [fsp, st_dp]; simp only [wp_norm, arm64_norm]; sep_ac_rfl)
              · dsimp only [dropPreKeyMsgSpec]
                simp only [sepExists_sepConj_left]
                apply r3b_sepWPp_exists_left; intro evs_dm
                simp only [sepConj_assoc]
                apply r3b_sepWPp_pure_left; rintro ⟨htr_dm, hdm_free⟩
                let st_dm := M.stepEvents evs_dm st_dp
                have htr5_eq : s5.trace = s4.trace :=
                  htr_dm.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
                have hfs5_eq : s5.fs.files = s4.fs.files :=
                  (r3b_files_of_trace_eq (hh.fs (runProgPlaced H) 579) hsteps_dm htr_dm).trans
                    (by simp only [r3b_stOf, wp_norm, arm64_norm])
                have hs5_pre : InRunPlaced R3bCodeOk s0 s5 0xb80 :=
                  r3b_inRun_step hs4 hpcm5 hrun5
                    (hsp5.trans (by simp only [r3b_stOf, wp_norm, arm64_norm]))
                    (hcsm5.2.2.2.2.2.2.2.2.2.2.1.trans
                      (by simp only [r3b_stOf, wp_norm, arm64_norm]))
                    hinv5
                    (hcsm5.2.2.2.2.2.2.2.2.2.2.2.trans
                      (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm]))
                have hx19_5 : s5.readReg64 (.gpr 19#5) = g.stores :=
                  hcsm5.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19_4])
                have hx20_5 : s5.readReg64 (.gpr 20#5) = g.res :=
                  hcsm5.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20_4])
                have hx21_5 : s5.readReg64 (.gpr 21#5) = meG.name.cap :=
                  hcsm5.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21_4])
                have hx26_5 : s5.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 :=
                  hcsm5.2.2.2.2.2.2.2.1.trans
                    (by simp only [r3b_stOf, wp_norm, arm64_norm]; exact hx26_4)
                have hx28_5 : s5.readReg64 (.gpr 28#5) = meG.name.ptr :=
                  hcsm5.2.2.2.2.2.2.2.2.2.1.trans
                    (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28_4])
                rw [← hsp5, hs5_pre.sp]
                have hpc5 : s5.pc = runPcPlaced 0xb80 := hs5_pre.pc
                rw [runPcPlaced_eq] at hpc5
                have hrun5' : s5.status = .Running := hs5_pre.run
                apply r3b_seq_lscro_oom (mid := runPcPlaced 0xd94) hs5_pre.inv
                rw [runPcPlaced_eq]
                dsimp only [runProgPlaced, lsProg_579]
                by_vm_open (
                  wp_steps
                  refine SepWP.done
                    (by simp only [wp_norm, arm64_norm])
                    (by simp only [wp_norm, arm64_norm, hrun5'])
                    ⟨by simp only [wp_norm, arm64_norm], fun hvm6 hinv6 => ?_⟩
                  change SepWPp (runProgPlaced H) _ _ _ _ _ _
                  rw [← A.pool_transport lim st_dm s5 (r3b_stOf hinv6) hvm6]
                  have hs6 : InRunPlaced R3bCodeOk s0 (r3b_stOf hinv6) 0xd94 :=
                    r3b_inRun_step hs5_pre
                      (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
                      (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun5'])
                      (by simp only [r3b_stOf, wp_norm, arm64_norm])
                      (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv6
                      (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
                  have htr6_eq : (r3b_stOf hinv6).trace = s4.trace :=
                    (by simp only [r3b_stOf, wp_norm, arm64_norm] :
                      (r3b_stOf hinv6).trace = s5.trace).trans htr5_eq
                  have hfs6_eq : (r3b_stOf hinv6).fs.files = s4.fs.files :=
                    (by simp only [r3b_stOf, wp_norm, arm64_norm] :
                      (r3b_stOf hinv6).fs.files = s5.fs.files).trans hfs5_eq
                  have htr6 : s0.trace <+: (r3b_stOf hinv6).trace := htr6_eq ▸ htr4
                  have hhist6 : RunHistOk g.i s0 (r3b_stOf hinv6) :=
                    r3b_hist_of_eq htr6_eq hfs6_eq hhist4
                  have hclean6 :
                      (memRegion (fsp + 0x4d0#64) 248 ∗
                        (fsp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                        ((fsp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
                        ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                        ((fsp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
                        memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                        memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2a0#64) 40 ∗
                        memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                        memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                        memRegion (fsp + 0x3e0#64) 240 ∗
                        memRegion (fsp + 0x1750#64) 240 ∗
                        memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                        memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840)) ∗
                      (lsLogOff ∗ anyHeap ∗ anyHeap) ⊢
                      memRegion fsp 0x220 ∗
                        memRegion (fsp + 0x280#64) 0xa0 ∗
                        memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) ∗
                        anyHeap := by
                    have h0_220 :
                        (fsp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                          ((fsp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
                          ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                          ((fsp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
                          memRegion (fsp + 0x28#64) (0x220 - 0x28) ⊢
                        memRegion fsp 0x220 := by
                      have h40 := r3b_slot5_to_mem40 fsp
                        ⟨lsρ cliPreKeyVtSym, g.stores + 0x50#64, lsρ cliSignedPreKeyVtSym,
                          g.stores + 0x78#64, lsρ cliKyberPreKeyVtSym⟩
                      dsimp only [r3b_slot5] at h40
                      rw [ProofLib.memRegion_split' (b := fsp) (n := 40) (k := 504)
                            (b' := fsp + 0x28#64) rfl (by bv_omega) (by decide)]
                      exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left h40)
                    have h280_a0 :
                        memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2a0#64) 40 ∗
                          memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) =
                        memRegion (fsp + 0x280#64) 0xa0 := by
                      rw [r3b_split_at fsp 0x280 0x20 0x320 (by decide) (by decide),
                          r3b_split_at fsp 0x2a0 40 0x320 (by decide) (by decide)]
                    have h350_all :
                        memRegion (fsp + 0x4d0#64) 248 ∗
                          memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                          memRegion (fsp + 0x3e0#64) 240 ∗
                          memRegion (fsp + 0x1750#64) 240 ∗
                          memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                          memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) =
                        memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) := by
                      rw [r3b_split_at fsp 0x350 (0x3e0 - 0x350) runLocalBytes (by decide) (by decide),
                          r3b_split_at fsp 0x3e0 240 runLocalBytes (by decide) (by decide),
                          r3b_split_at fsp 0x4d0 248 runLocalBytes (by decide) (by decide),
                          r3b_split_at fsp 0x5c8 (0x1750 - 0x5c8) runLocalBytes (by decide) (by decide),
                          r3b_split_at fsp 0x1750 240 runLocalBytes (by decide) (by decide)]
                      ac_rfl
                    exact r3b_perm
                      (sepConj_mono h0_220
                        (sepConj_mono (Entails.of_eq h280_a0)
                          (sepConj_mono (Entails.of_eq h350_all)
                            (entails_anyHeap (lsLogOff ∗ anyHeap ∗ anyHeap)))))
                      (by ac_rfl)
                  have hinp_back :
                      (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) = (g.inp ↦ₛ inputOf g.i g.c) := by
                    rw [hinp_c, pointsToBytes_cons]
                  cases e with
                  | error err =>
                    have hans_err : g.a = some none := by
                      have hnone := hout_dp.2.2
                      rw [hpeer_val, hme_val] at hnone
                      rw [hga, hnone]; rfl
                    have henv_dec_err : ∀ evs_drop, FreeOnlyEvs evs_drop →
                        ∃ evs,
                          R3bRecvPEnv S sEnvs PksmTryFromEnv g (.some meV meG) peerV rest evs ∧
                          M.stepEvents (evs_drop ++ r3bFreeMePeerEvs meG peerG) st_dm =
                            M.stepEvents evs st := by
                      intro evs_drop hfree_drop
                      refine ⟨evs_pk ++
                        (evs_dp ++ (evs_dm ++ (evs_drop ++ r3bFreeMePeerEvs meG peerG))), ?_, ?_⟩
                      · simp only [R3bRecvPEnv, _hparse]
                        exact SeqEnv.append hpk_ev0
                          (SeqEnv.append hdp_ev0
                            (FreeOnlyEvs.append hdm_free
                              (FreeOnlyEvs.append hfree_drop
                                (r3bFreeMePeerEvs_freeOnly meG peerG))))
                      · dsimp only [st_dm, st_dp, st_pk]
                        rw [M.stepEvents_append evs_pk, M.stepEvents_append evs_dp,
                            M.stepEvents_append evs_dm]
                    refine r3b_sepWPp_weaken_pre ?_
                      (r3b_recvP_dec_err_placed g' err peerG meG hh hdrop hstk32 hext_le hsub64 hs6
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19_5])
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20_5])
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21_5])
                        (by dsimp only [fsp] at hx26_5; simp only [r3b_stOf, wp_norm, arm64_norm, hx26_5])
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28_5])
                        htr6 hhist6 hans_err henv_dec_err hrej)
                    exact r3b_perm
                      (r3b_perm_post
                        (sepConj_mono hclean6
                          (sepConj_mono (Entails.of_eq hinp_back)
                            (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                              storesAt A.repAlloc g.stores g' ∗
                              protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
                              protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
                              runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20 ∗
                              decResAt A.repAlloc (fsp + 0x320#64) (.error err) ∗
                              stackAt fsp (resStack - runFrame) ∗
                              A.pool lim st_dm (r3b_stOf hinv6)))))
                        (by dsimp only [fsp, st_dm]; sep_ac_rfl))
                      (by dsimp only [fsp, st_dm]; sep_ac_rfl)
                  | ok pt =>
                    have hout_ok : g.a = some (some (namedWrites g'.writes, pt)) ∧
                        ∀ pw ∈ g'.writes, cliWrOk pw.1 := by
                      rcases hout_dp.2.2 with ⟨hsome, hwrok⟩
                      rw [hpeer_val, hme_val] at hsome
                      exact ⟨by rw [hga, hsome]; rfl, hwrok⟩
                    have henv_dec_ok :
                        ∃ evs,
                          R3bRecvPEnv S sEnvs PksmTryFromEnv g (.some meV meG) peerV rest evs ∧
                          M.stepEvents (r3bFreeMePeerEvs meG peerG) st_dm =
                            M.stepEvents evs st := by
                      refine ⟨evs_pk ++ (evs_dp ++ (evs_dm ++ r3bFreeMePeerEvs meG peerG)), ?_, ?_⟩
                      · simp only [R3bRecvPEnv, _hparse]
                        exact SeqEnv.append hpk_ev0
                          (SeqEnv.append hdp_ev0
                            (FreeOnlyEvs.append hdm_free (r3bFreeMePeerEvs_freeOnly meG peerG)))
                      · dsimp only [st_dm, st_dp, st_pk]
                        rw [M.stepEvents_append evs_pk, M.stepEvents_append evs_dp,
                            M.stepEvents_append evs_dm]
                    refine r3b_sepWPp_weaken_pre ?_
                      (r3b_recvP_dec_ok_placed g' pt peerG meG hh hext_le hsub64 hs6
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19_5])
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20_5])
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21_5])
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28_5])
                        htr6 hhist6 hout_ok.1 hout_ok.2 henv_dec_ok hjoin)
                    exact r3b_perm
                      (r3b_perm_post
                        (sepConj_mono hclean6
                          (sepConj_mono (Entails.of_eq hinp_back)
                            (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                              storesAt A.repAlloc g.stores g' ∗
                              protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
                              protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
                              runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20 ∗
                              decResAt A.repAlloc (fsp + 0x320#64) (.ok pt) ∗
                              stackAt fsp (resStack - runFrame) ∗
                              A.pool lim st_dm (r3b_stOf hinv6)))))
                        (by dsimp only [fsp, st_dm]; sep_ac_rfl))
                      (by dsimp only [fsp, st_dm]; sep_ac_rfl))))


set_option maxHeartbeats 1200000

theorem run_hop_recvP_of_codeOk_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : CryptoVerification.SignalSession.Cli.RunSkeleton.RunSlots} {resStack : Nat}
    (hneed_eq : CryptoVerification.SignalSession.Cli.RunSkeleton.runNeed B slots =
      CryptoVerification.SignalSession.Cli.RunSkeleton.runNeed B (slotsOfPlaced A lim sEnvs S needs))
    (hslot_eq : slots.decryptPrekey =
      mkSlot
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf
          CodeOk A lim sEnvs.decryptPrekey S)
        needs.decryptPrekey)
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmTryFromEnv x = PksmTryFromEnv y := by
      intros; rfl)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y := by intros; rfl) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget.RunHopRecvPPlacedOf
      CodeOk A lim cEnvs PksmTryFromEnv (R3bRecvPEnv S sEnvs PksmTryFromEnv)
      H B S slots resStack := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget.RunHopRecvPPlacedOf
  intro g st s0 s me peerV rest Q Qp hh hc hpksm hdrop hres hres64 hspb he hd hcall hstdin hfit
    hpanic hrej hjoin
  rw [hneed_eq] at hres
  cases me with
  | none =>
    exact LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget.r3b_me_none_placed_codeOk hh hres hres64 he hd hcall
      (fun cap => ⟨r3bFreeCapEvs cap, r3bFreeCapEvs_freeOnly cap, rfl⟩) hrej
  | some meV meG =>
    have hbnds := runNeed_bounds_placed hres hres64
    rcases hbnds with ⟨hrf_le, hsub63, hsub64, _, _, _, _, _, _, _, _, _, _,
      hpk_stk, hstk32, _, hext_le, _, _, _, hdp_stk, _⟩
    obtain ⟨hrest32, hcoins63, _, hfilesOk, hdecPkOk, hga⟩ :=
      hd.recvP_facts he hcall hstdin
    refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget.r3b_recv_head_some_placed_codeOk hd hcall ?_
    intro s1 peerG cw4 hiMe hs1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1
      htr1 hfs1 hpeer_val hme_val hdev_cw4 hhi
    let fsp := runFsp s0
    have hfsp_sub : resStack - runFrame ≤ fsp.toNat := by
      dsimp only [fsp, runFsp, runFrame] at hrf_le ⊢
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 10832 ≤ s0.sp.toNat; omega))]
      change resStack - 10832 ≤ s0.sp.toNat - 10832
      omega
    have hinp_c : inputOf g.i g.c = 3#8 :: rest := by simp [hcall, inputOf, CallV.tag, hstdin]
    have hlen_ne : BitVec.ofNat 64 (3#8 :: rest).length ≠ 0#64 := by
      rw [List.length_cons]
      intro h0
      have hv := congrArg BitVec.toNat h0
      have hzero : (0#64).toNat = 0 := rfl
      rw [BitVec.toNat_ofNat, hzero] at hv
      have hmod : (rest.length + 1) % 2 ^ 64 = rest.length + 1 := Nat.mod_eq_of_lt (by omega)
      omega
    have hbeq_len : (BitVec.ofNat 64 (3#8 :: rest).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hlen_ne
    have hsub1_nat : (BitVec.ofNat 64 (3#8 :: rest).length - 1#64).toNat = rest.length := by
      rw [List.length_cons]
      have h1 : BitVec.ofNat 64 (rest.length + 1) - 1#64 = BitVec.ofNat 64 rest.length := by
        rw [BitVec.ofNat_add]; bv_omega
      rw [h1, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have h280_pkm : memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) =
        memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
          memRegion (fsp + 0x4d0#64) 248 ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) := by
      rw [r3b_split_at fsp 0x280 (0x4d0 - 0x280) runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x4d0 248 runLocalBytes (by decide) (by decide)]
    let pkX : PksmGhost := { ptr := g.inp + 1#64, bytes := rest, ret := fsp + 0x4d0#64 }
    have hpk_eq : PksmTryFromEnv pkX = PksmTryFromEnv (r3bPksmGhost rest) :=
      hpksm_addr pkX (r3bPksmGhost rest) rfl
    have hfit_pk0 : FitsEnv M lim st (PksmTryFromEnv (r3bPksmGhost rest)) := by
      dsimp only [R3bRecvPEnv] at hfit
      rcases hp0 : S.pksmParse rest with _ | _ <;>
        (rw [hp0] at hfit; exact hfit.seq_left)
    have hfit_pk : FitsEnv M lim st (PksmTryFromEnv pkX) := by
      rw [hpk_eq]; exact hfit_pk0
    rw [hinp_c] at hx24_1
    rw [hinp_c, pointsToBytes_cons, h280_pkm]
    have hpc1 : s1.pc = runPcPlaced 0x7c8 := hs1.pc
    rw [runPcPlaced_eq] at hpc1
    have hrun1 : s1.status = .Running := hs1.run
    have hsp1 : s1.sp = fsp := hs1.sp
    have hsp1_al : s1.spAligned = true := hs1.spAligned_cur
    apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := blkPl_111.base) hs1.inv
    rw [← hsp1]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm]; rfl)
        (by simp only [wp_norm, arm64_norm, hrun1])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_pk hinv_pk => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s1 (r3b_stOf hinv_pk) hvm_pk]
      have hstk_pk := r3b_stackAt_split_ge s1.sp hpk_stk hsub64
      refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget.r3b_call_raw_codeOk
        (F := memRegion g.res runResSize ∗
          memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗
          (g.inp ↦₈ 3#8) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗
          tokenInitPlacedAt ∗
          addrNameHeap A.repAlloc meG ∗
          addrNameHeap A.repAlloc peerG ∗
          runSaved s0 ∗
          memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗
            ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
          memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - preKeyTryFromStack))
        (pkX, st)
        hpksm hinv_pk
        (by simp only [r3b_stOf, wp_norm, arm64_norm]; rfl)
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun1])
        (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp1_al)
        (retAddr := runPcPlaced 0x994)
        (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        ?_
        (hpanic := fun _ _ _ hp => by
          dsimp only [pksmSlotSpecPlaced, withLsCodeRoLoaded] at hp
          exact (not_satisfies_false_sepConj hp).elim)
        (hoom := fun _ _ _ ho => by
          dsimp only [pksmSlotSpecPlaced, withLsCodeRoLoaded] at ho
          exact (not_satisfies_false_sepConj ho).elim)
        (hnext := fun s2 hsteps_pk hinv2 hpcm2 hrun2 hsp2 hcsm2 => ?_)
      · dsimp only [pksmSlotSpecPlaced, withLsCodeRoLoaded, pkX, r3b_stOf]
        simp only [sepConj_assoc]
        apply Entails.pure_right
        · exact ⟨by simp only [wp_norm, arm64_norm]; try rw [hx23_1],
            by simp only [wp_norm, arm64_norm]; exact hsub1_nat,
            hrest32,
            by simp only [wp_norm, arm64_norm]; try rw [hsp1],
            by
              have hpk_spb : preKeyTryFromStack ≤ fsp.toNat :=
                Nat.le_trans hpk_stk hfsp_sub
              simpa only [wp_norm, arm64_norm, hsp1] using hpk_spb,
            hfit_pk⟩
        rw [hsp1] at hstk_pk
        rw [hstk_pk]
        simp only [wp_norm, arm64_norm]
        try rw [hsp1]
        exact r3b_perm_post
          (Entails.pure_right (CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv.toRoCl hinv_pk) (Entails.refl _))
          (by dsimp only [fsp, r3b_stOf]; simp only [wp_norm, arm64_norm]; sep_ac_rfl)
      · dsimp only [pksmSlotSpecPlaced, withLsCodeRoLoaded, pkX]
        simp only [sepExists_sepConj_left]
        apply r3b_sepWPp_exists_left; intro evs_pk
        simp only [sepConj_assoc]
        apply r3b_sepWPp_pure_left; rintro ⟨htr_pk, hpk_ev⟩
        let st_pk := M.stepEvents evs_pk st
        have hpk_ev0 : PksmTryFromEnv (r3bPksmGhost rest) evs_pk := by
          rw [← hpk_eq]; exact hpk_ev
        have hs2 : InRunPlaced CodeOk s0 s2 0x994 :=
          r3b_inRun_step hs1 hpcm2 hrun2 (hsp2.trans (by simp only [r3b_stOf, wp_norm, arm64_norm]))
            (hcsm2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])) hinv2
            (hcsm2.2.2.2.2.2.2.2.2.2.2.2.trans
              (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm]))
        have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores :=
          hcsm2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19_1])
        have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res :=
          hcsm2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20_1])
        have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap :=
          hcsm2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21_1])
        have hx26_2 : s2.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 :=
          hcsm2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm]; exact hx26_1)
        have hx27_2 : s2.readReg64 (.gpr 27#5) = fsp + 0x1750#64 :=
          hcsm2.2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm]; exact hx27_1)
        have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr :=
          hcsm2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm]; exact hx28_1)
        have htr2_eq : s2.trace = s.trace :=
          (htr_pk.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])).trans htr1
        have hfs2_files : s2.fs.files = runFiles g.i :=
          ((r3b_files_of_trace_eq (hh.fs (runProgPlaced H) 579) hsteps_pk htr_pk).trans
            (by simp only [r3b_stOf, wp_norm, arm64_norm])).trans
            ((congrArg FsState.files hfs1).trans hd.fs)
        have htr2 : s0.trace <+: s2.trace := htr2_eq ▸ hd.trace
        have hhist2 : RunHistOk g.i s0 s2 :=
          ⟨hfs2_files, htr2_eq ▸ hd.stdout⟩
        rw [← hsp2, hs2.sp]
        rw [hsp1] at hstk_pk
        apply r3b_sepWPp_weaken_pre
          (r3b_perm
            (sepConj_mono_left
              (Q := pksmResAt A.repAlloc (fsp + 0x4d0#64) (S.pksmParse rest) ∗
                ((g.inp + 1#64) ↦ₛ rest) ∗ lsLogOff ∗ A.pool lim st_pk s2 ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦₈ 3#8) ∗
                coinsInstalledPlaced g.coins (coinsOf g.i) ∗
                tokenInitPlacedAt ∗
                addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
                memRegion fsp 0x220 ∗
                (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                  ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                  ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
                memRegion (fsp + 0x240#64) 0x20 ∗
                (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                  ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                  ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
                memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
                memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8))
              (Entails.of_eq hstk_pk.symm))
            (by dsimp only [fsp, st_pk]; sep_ac_rfl))
        rcases _hparse : S.pksmParse rest with _ | pm
        · (try rw [_hparse] at hga); dsimp only at hga
          have henv_parse_err : ∀ evs_drop, FreeOnlyEvs evs_drop →
              ∃ evs, R3bRecvPEnv S sEnvs PksmTryFromEnv g (.some meV meG) peerV rest evs ∧
                M.stepEvents (evs_drop ++ r3bFreeMePeerEvs meG peerG) st_pk =
                  M.stepEvents evs st := by
            intro evs_drop hfree_drop
            refine ⟨evs_pk ++ (evs_drop ++ r3bFreeMePeerEvs meG peerG), ?_, ?_⟩
            · simp only [R3bRecvPEnv, _hparse]
              exact SeqEnv.append hpk_ev0
                (FreeOnlyEvs.append hfree_drop (r3bFreeMePeerEvs_freeOnly meG peerG))
            · dsimp only [st_pk]
              exact (M.stepEvents_append evs_pk _ st).symm
          refine r3b_sepWPp_weaken_pre ?_
            (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudgetAux.r3b_recvP_parse_err_placed_codeOk meG peerG cw4 hiMe hh hdrop hstk32 hext_le hsub64 hs2
              hx19_2 hx20_2 hx21_2 hx26_2 hx28_2 htr2 hhist2 hga henv_parse_err hrej)
          rw [hinp_c, pointsToBytes_cons]
          have hany :
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗
                tokenInitPlacedAt ∗ lsLogOff ⊢ anyHeap :=
            entails_anyHeap _
          exact r3b_perm
            (r3b_perm_post
              (sepConj_mono hany
                (Entails.refl (pksmResAt A.repAlloc (fsp + 0x4d0#64) none ∗
                  (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                  stackAt fsp (resStack - runFrame) ∗ A.pool lim st_pk s2 ∗
                  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                  storesAt A.repAlloc g.stores StoresGhost.opened ∗
                  addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
                  memRegion fsp 0x220 ∗
                  (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                    ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                    ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
                  memRegion (fsp + 0x240#64) 0x20 ∗
                  (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                    ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                    ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
                  memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
                  memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8))))
              (by dsimp only [fsp]; sep_ac_rfl))
            (by dsimp only [fsp, pksmResAt]; sep_ac_rfl)
        · (try rw [_hparse] at hga); dsimp only at hga
          have hdp_ok := hdecPkOk pm (by first | exact rfl | exact _hparse)
          have hfit_pm : FitsEnv M lim st
              (SeqEnv (PksmTryFromEnv (r3bPksmGhost rest))
                (SeqEnv (sEnvs.decryptPrekey (r3bDecPkGhost g meV peerV pm)) FreeOnlyEvs)) := by
            simpa only [R3bRecvPEnv, _hparse] using hfit
          have hfit_dp0 :
              FitsEnv M lim st_pk (sEnvs.decryptPrekey (r3bDecPkGhost g meV peerV pm)) :=
            (hfit_pm.seq_right hpk_ev0).seq_left
          have hloc_shuf :
              pksmResAt A.repAlloc (fsp + 0x4d0#64) (some pm) ∗
                (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                  ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                  ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
                (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                  ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                  ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
                addrNameHeap A.repAlloc peerG ∗ addrNameHeap A.repAlloc meG ∗
                memRegion fsp 0x220 ∗
                memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
                memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ⊢
              ∃∗ pmG : PreKeyMsgGhost, ∃∗ w : r3b_W30,
                ∃∗ t0 : r3b_W5, ∃∗ t : r3b_W5, ∃∗ z : r3b_W30, ∃∗ m : r3b_W30,
                  ⌜pmG.msg.pqCap.toNat < 2 ^ 63⌝ ∗
                  ((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗
                  r3b_slot30 (fsp + 0x4d8#64) w ∗
                  r3b_slot5 (fsp + 0x2a0#64) t ∗
                  r3b_slot30 (fsp + 0x3e0#64) z ∗
                  r3b_slot30 (fsp + 0x1750#64) m ∗
                  r3b_slot5 fsp t0 ∗
                  ((((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (fsp + 0x4d8#64) w) -∗
                    preKeyMsgAt A.repAlloc pmG (fsp + 0x4d0#64) pm) ∗
                  protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
                  protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
                  memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                  memRegion (fsp + 0x280#64) 0x20 ∗
                  memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                  memRegion (fsp + 0x320#64) 48 ∗
                  memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                  memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                  memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                  anyHeap := by
            dsimp only [pksmResAt]
            have hf0 : memRegion fsp 0x220 =
                memRegion fsp 40 ∗ memRegion (fsp + 0x28#64) (0x220 - 0x28) :=
              ProofLib.memRegion_split' (b := fsp) (n := 40) (k := 504)
                (b' := fsp + 0x28#64) rfl (by bv_omega) (by decide)
            have hf280 : memRegion (fsp + 0x280#64) (0x4d0 - 0x280) =
                memRegion (fsp + 0x280#64) 0x20 ∗
                  memRegion (fsp + 0x2a0#64) 40 ∗
                  memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                  memRegion (fsp + 0x320#64) 48 ∗
                  memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                  memRegion (fsp + 0x3e0#64) 240 := by
              rw [r3b_split_at fsp 0x280 0x20 0x4d0 (by decide) (by decide),
                  r3b_split_at fsp 0x2a0 40 0x4d0 (by decide) (by decide),
                  r3b_split_at fsp 0x2c8 (0x320 - 0x2c8) 0x4d0 (by decide) (by decide),
                  r3b_split_at fsp 0x320 48 0x4d0 (by decide) (by decide),
                  r3b_split_at fsp 0x350 (0x3e0 - 0x350) 0x4d0 (by decide) (by decide)]
            have hf5c8 : memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) =
                memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                  memRegion (fsp + 0x1750#64) 240 ∗
                  memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) := by
              rw [r3b_split_at fsp 0x5c8 (0x1750 - 0x5c8) runLocalBytes (by decide) (by decide),
                  r3b_split_at fsp 0x1750 240 runLocalBytes (by decide) (by decide)]
            rw [hf0, hf280, hf5c8]
            have hp_pack := r3b_addr_pack A.repAlloc peerG (fsp + 0x220#64) (fsp + 0x228#64)
              (fsp + 0x230#64) (fsp + 0x238#64) cw4 (by bv_omega) (by bv_omega) (by bv_omega)
              hdev_cw4
            have hm_pack := r3b_addr_pack A.repAlloc meG (fsp + 0x260#64) (fsp + 0x268#64)
              (fsp + 0x270#64) (fsp + 0x278#64) hiMe (by bv_omega) (by bv_omega) (by bv_omega) hhi
            simp only [sepExists_sepConj_left]
            apply Entails.sepExists_elim; intro pmG
            refine Entails.trans
              (r3b_perm
                (sepConj_mono (r3b_pkm_to_words A.repAlloc pmG (fsp + 0x4d0#64) pm)
                  (sepConj_mono (r3b_mem40_to_slot5 fsp)
                    (sepConj_mono (r3b_mem40_to_slot5 (fsp + 0x2a0#64))
                      (sepConj_mono (r3b_mem240_to_slot30 (fsp + 0x3e0#64))
                        (sepConj_mono (r3b_mem240_to_slot30 (fsp + 0x1750#64))
                          (sepConj_mono hp_pack (sepConj_mono hm_pack
                            (Entails.refl (memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                              memRegion (fsp + 0x280#64) 0x20 ∗
                              memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                              memRegion (fsp + 0x320#64) 48 ∗
                              memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                              memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                              memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                              anyHeap)))))))))
                (by ac_rfl)) ?_
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply Entails.sepExists_elim; intro m
            apply Entails.sepExists_elim; intro z
            apply Entails.sepExists_elim; intro t
            apply Entails.sepExists_elim; intro t0
            apply Entails.sepExists_elim; intro w
            simp only [sepConj_assoc]
            apply Entails.pure_left; intro hcap_pm
            have ha4d8 : fsp + 0x4d0#64 + 8#64 = fsp + 0x4d8#64 := by bv_omega
            rw [ha4d8]
            exact Entails.sepExists_right pmG (Entails.sepExists_right w
              (Entails.sepExists_right t0 (Entails.sepExists_right t
                (Entails.sepExists_right z (Entails.sepExists_right m
                  (Entails.pure_right hcap_pm (Entails.of_eq (by ac_rfl))))))))
          apply r3b_sepWPp_weaken_pre
            (r3b_perm
              (sepConj_mono_left
                (Q := (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                  stackAt fsp (resStack - runFrame) ∗ A.pool lim st_pk s2 ∗
                  coinsInstalledPlaced g.coins (coinsOf g.i) ∗
                  tokenInitPlacedAt ∗ lsLogOff ∗
                  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                  storesAt A.repAlloc g.stores StoresGhost.opened ∗
                  runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)
                hloc_shuf)
              (by dsimp only [fsp]; sep_ac_rfl))
          simp only [sepExists_sepConj_left]
          apply r3b_sepWPp_exists_left; intro pmG
          apply r3b_sepWPp_exists_left; intro w
          apply r3b_sepWPp_exists_left; intro t0
          apply r3b_sepWPp_exists_left; intro t
          apply r3b_sepWPp_exists_left; intro z
          apply r3b_sepWPp_exists_left; intro m
          simp only [sepConj_assoc]
          apply r3b_sepWPp_pure_left; intro hcap_pm
          refine r3b_sepWPp_weaken_pre (Entails.of_eq (by dsimp only [fsp]))
            (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudgetAux.r3b_recvP_shuf1_placed_codeOk pmG.msg.pqCap w t z m _ hs2 hcap_pm hx26_2 hx27_2 ?_)
          intro s3 hvm3 hs3 hx8_3 hx9_3 hx19_3 hx20_3 hx21_3 hx26_3 hx28_3 htr3 hfs3
          rw [hx19_2] at hx19_3
          rw [hx20_2] at hx20_3
          rw [hx21_2] at hx21_3
          rw [hx26_2] at hx26_3
          rw [hx28_2] at hx28_3
          let shuf2F : SepProp :=
            (((runFsp s0 + 1232#64) ↦₆₄ pmG.msg.pqCap ∗ r3b_slot30 (runFsp s0 + 1240#64) w) -∗
              preKeyMsgAt A.repAlloc pmG (runFsp s0 + 1232#64) pm) ∗
            memRegion (runFsp s0 + 672#64) 40 ∗
            memRegion (runFsp s0 + 5968#64) 240 ∗
            protocolAddressAt A.repAlloc peerG (runFsp s0 + 544#64) ∗
            protocolAddressAt A.repAlloc meG (runFsp s0 + 608#64) ∗
            memRegion (runFsp s0 + 40#64) (544 - 40) ∗
            memRegion (runFsp s0 + 640#64) 32 ∗
            memRegion (runFsp s0 + 712#64) (800 - 712) ∗
            memRegion (runFsp s0 + 800#64) 48 ∗
            memRegion (runFsp s0 + 848#64) (992 - 848) ∗
            memRegion (runFsp s0 + 1480#64) (5968 - 1480) ∗
            memRegion (runFsp s0 + 6208#64) (runLocalBytes - 6208) ∗
            anyHeap ∗
            (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗
            A.pool lim st_pk s2 ∗
            coinsInstalledPlaced g.coins (coinsOf g.i) ∗
            tokenInitPlacedAt ∗
            lsLogOff ∗
            memRegion g.res runResSize ∗
            memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗
            runSaved s0 ∗
            memRegion (runFsp s0 + 576#64) 32
          refine r3b_sepWPp_weaken_pre (Entails.of_eq (by dsimp only [fsp, shuf2F]; sep_ac_rfl))
            (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudget.r3b_recvP_shuf2_placed_codeOk g.stores pmG.msg.pqCap t0 w z shuf2F hs3 hx8_3 hx9_3 hx19_3 ?_)
          intro sc hvm_c hinv_c hpc_c hrun_c hsp_c hsp_al_c hlr_c
            hx0_c hx1_c hx2_c hx3_c hx4_c hx5_c hx6_c hx7_c hx8_c
            hx19_c hx20_c hx21_c hx26_c hx28_c hfp_c hvregs_c htr_c hfs_c
          rw [hx20_3] at hx20_c
          rw [hx21_3] at hx21_c
          rw [hx26_3] at hx26_c
          rw [hx28_3] at hx28_c
          have htr_sc_eq : sc.trace = s2.trace := htr_c.trans htr3
          have hfs_sc_files : sc.fs.files = runFiles g.i :=
            (congrArg FsState.files (hfs_c.trans hfs3)).trans hfs2_files
          have htr_sc : s0.trace <+: sc.trace := htr_sc_eq ▸ htr2
          have hpool_sc : A.pool lim st_pk s2 = A.pool lim st_pk sc :=
            ((A.pool_transport lim st_pk s3 sc hvm_c).trans
              (A.pool_transport lim st_pk s2 s3 hvm3)).symm
          let dpX : DecPkGhost :=
            { peer := peerG
              peerA := fsp + 0x220#64
              me := meG
              meA := fsp + 0x260#64
              stores := g.stores
              ret := fsp + 0x320#64
              coinsP := g.coins
              F := runFiles g.i
              coins := coinsOf g.i
              msgA := fsp + 0x4d0#64
              msgG := pmG
              msg := pm }
          have hdp_eq :
              sEnvs.decryptPrekey dpX = sEnvs.decryptPrekey (r3bDecPkGhost g meV peerV pm) :=
            hdp_ghost dpX (r3bDecPkGhost g meV peerV pm) hpeer_val hme_val rfl rfl rfl rfl rfl
          have hfit_dp : FitsEnv M lim st_pk (sEnvs.decryptPrekey dpX) := by
            rw [hdp_eq]; exact hfit_dp0
          have hdp_call : subroutine_ok (runProgPlaced H) (lsmpl.base 520)
              (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf
                CodeOk A lim sEnvs.decryptPrekey S (resStack - runFrame)) := by
            have hdp_stk' : slots.decryptPrekey.need ≤ resStack - runFrame := by
              rw [hslot_eq]; exact hdp_stk
            have h := hc.decryptPrekey (resStack - runFrame) hdp_stk' hsub63
            rwa [hslot_eq] at h
          refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget.r3b_call_raw_codeOk
            (F := memRegion (fsp + 0x3e0#64) 240 ∗
              memRegion (fsp + 0x2a0#64) 40 ∗
              memRegion (fsp + 0x1750#64) 240 ∗
              memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
              memRegion (fsp + 0x280#64) 0x20 ∗
              memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
              memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
              memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
              memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
              anyHeap ∗
              (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)
            (dpX, st_pk)
            hdp_call hinv_c
            hpc_c hrun_c hsp_al_c (retAddr := runPcPlaced 0xb78) hlr_c
            ?_
            (hpanic := fun sf R' _ hp => by
              dsimp only [
                LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf,
                LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecBasePlaced,
                LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlaced,
                withLsCodeRoLoaded, dpX] at hp
              rw [sepConj_assoc, satisfies_pure_sepConj] at hp
              have hnone := hp.1
              rw [hpeer_val, hme_val] at hnone
              apply hpanic sf _ (Or.inl ?_)
              rw [hga, hnone]; rfl)
            (hoom := fun _ _ _ ho => by
              dsimp only [
                LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf,
                LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecBasePlaced,
                LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlaced,
                withLsCodeRoLoaded, dpX] at ho
              exact (not_satisfies_false_sepConj ho).elim)
            (hnext := fun s4 _ hinv4 hpcm4 hrun4 hsp4 hcsm4 => ?_)
          · dsimp only [
              LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf,
              LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecBasePlaced,
              slotFramePlaced,
              LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
              withLsCodeRoLoaded, dpX, shuf2F]
            rw [hpool_sc]
            simp only [sepConj_assoc]
            apply Entails.pure_right
            · exact ⟨hx0_c, hx1_c, hx2_c, hx3_c, hx4_c, hx5_c, hx6_c, hx7_c, hx8_c, hfs_sc_files,
                by rw [hpeer_val, hme_val]; exact hfilesOk,
                by rw [hpeer_val, hme_val]; exact hdp_ok,
                hsp_c ▸ hfsp_sub,
                hfit_dp⟩
            apply Entails.pure_right
            · exact hcoins63
            rw [hsp_c]
            have hpkm_restore :
                ((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (fsp + 0x4d8#64) w ∗
                  ((((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (fsp + 0x4d8#64) w) -∗
                    preKeyMsgAt A.repAlloc pmG (fsp + 0x4d0#64) pm) ⊢
                preKeyMsgAt A.repAlloc pmG (fsp + 0x4d0#64) pm := by
              rw [← sepConj_assoc]
              exact Entails.wand_elim _ _
            exact r3b_perm
              (r3b_perm_post
                (Entails.pure_right hinv_c
                  (sepConj_mono hpkm_restore
                    (Entails.refl ((fsp ↦₆₄ lsρ cliPreKeyVtSym) ∗
                      ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                      ((fsp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
                      ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                      ((fsp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
                      memRegion (fsp + 0x3e0#64) 240 ∗
                      memRegion (fsp + 0x2a0#64) 40 ∗ memRegion (fsp + 0x1750#64) 240 ∗
                      protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
                      protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
                      memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                      memRegion (fsp + 0x280#64) 0x20 ∗
                      memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                      memRegion (fsp + 0x320#64) 48 ∗
                      memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                      memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                      memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                      anyHeap ∗
                      (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                      stackAt fsp (resStack - runFrame) ∗ A.pool lim st_pk sc ∗
                      coinsInstalledPlaced g.coins (coinsOf g.i) ∗
                      tokenInitPlacedAt ∗ lsLogOff ∗
                      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                      storesAt A.repAlloc g.stores StoresGhost.opened ∗
                      runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20))))
                (by dsimp only [fsp]; sep_ac_rfl))
              (by dsimp only [fsp]; sep_ac_rfl)
          · dsimp only [
              LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf,
              LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecBasePlaced,
              LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlaced,
              withLsCodeRoLoaded, dpX]
            simp only [sepExists_sepConj_left]
            apply r3b_sepWPp_exists_left; intro evs_dp
            apply r3b_sepWPp_exists_left; intro g'
            apply r3b_sepWPp_exists_left; intro e
            simp only [sepConj_assoc]
            apply r3b_sepWPp_pure_left; rintro ⟨hdp_ev, ⟨htr_dp, hfs_dp, hout_str_dp⟩, hout_dp⟩
            let st_dp := M.stepEvents evs_dp st_pk
            have hdp_ev0 : sEnvs.decryptPrekey (r3bDecPkGhost g meV peerV pm) evs_dp := by
              rw [← hdp_eq]; exact hdp_ev
            have hs4 : InRunPlaced CodeOk s0 s4 0xb78 :=
              r3b_inRun_step hs3 hpcm4 hrun4 (hsp4.trans (hsp_c.trans hs3.sp.symm))
                (hcsm4.2.2.2.2.2.2.2.2.2.2.1.trans hfp_c) hinv4
                (hcsm4.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_c)
            have htr4 : s0.trace <+: s4.trace := htr_sc.trans htr_dp
            have hhist4 : RunHistOk g.i s0 s4 :=
              ⟨hfs_dp.trans hfs_sc_files, hout_str_dp.trans (htr_sc_eq ▸ htr2_eq ▸ hd.stdout)⟩
            have hx19_4 : s4.readReg64 (.gpr 19#5) = g.stores := hcsm4.1.trans hx19_c
            have hx20_4 : s4.readReg64 (.gpr 20#5) = g.res := hcsm4.2.1.trans hx20_c
            have hx21_4 : s4.readReg64 (.gpr 21#5) = meG.name.cap := hcsm4.2.2.1.trans hx21_c
            have hx26_4 : s4.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 :=
              hcsm4.2.2.2.2.2.2.2.1.trans hx26_c
            have hx28_4 : s4.readReg64 (.gpr 28#5) = meG.name.ptr :=
              hcsm4.2.2.2.2.2.2.2.2.2.1.trans hx28_c
            rw [hsp_c]
            have hpc4 : s4.pc = runPcPlaced 0xb78 := hs4.pc
            rw [runPcPlaced_eq] at hpc4
            have hrun4' : s4.status = .Running := hs4.run
            have hsp4' : s4.sp = fsp := hs4.sp
            have hsp4_al : s4.spAligned = true := hs4.spAligned_cur
            apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := blkPl_555.base) hs4.inv
            dsimp only [runProgPlaced, lsProg_579]
            by_vm_open (
              wp_steps
              refine SepWP.done
                (by simp only [wp_norm, arm64_norm]; rfl)
                (by simp only [wp_norm, arm64_norm, hrun4'])
                ⟨by simp only [wp_norm, arm64_norm], fun hvm_dm hinv_dm => ?_⟩
              change SepWPp (runProgPlaced H) _ _ _ _ _ _
              rw [← A.pool_transport lim st_dp s4 (r3b_stOf hinv_dm) hvm_dm]
              refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget.r3b_call_lscro_codeOk
                (F := storesAt A.repAlloc g.stores g' ∗
                  decResAt A.repAlloc (fsp + 0x320#64) e ∗
                  protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
                  protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
                  (fsp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                  ((fsp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
                  ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                  ((fsp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
                  lsLogOff ∗ anyHeap ∗
                  memRegion (fsp + 0x3e0#64) 240 ∗
                  memRegion (fsp + 0x2a0#64) 40 ∗
                  memRegion (fsp + 0x1750#64) 240 ∗
                  memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                  memRegion (fsp + 0x280#64) 0x20 ∗
                  memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                  memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                  memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                  memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                  anyHeap ∗
                  (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                  runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)
                (⟨fsp + 0x4d0#64, pmG, pm⟩, st_dp)
                (dropPreKeyMsg_placed_ok (callerProg := runProgPlaced H) (i := 579) hh (resStack - runFrame) hstk32 hsub64) hinv_dm
                (by simp only [r3b_stOf, wp_norm, arm64_norm]; rfl)
                (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun4'])
                (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp4_al)
                (retAddr := runPcPlaced 0xb80)
                (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
                ?_
                (hnext := fun s5 hsteps_dm hinv5 hpcm5 hrun5 hsp5 hcsm5 => ?_)
              · dsimp only [dropPreKeyMsgSpec, r3b_stOf]
                simp only [sepConj_assoc]
                apply Entails.pure_right
                · refine ⟨by dsimp only [fsp]; simp only [wp_norm, arm64_norm]; try rw [hx26_4],
                    by simp (config := { decide := true }) only [wp_norm, arm64_norm, runPcPlaced_eq]⟩
                simp only [wp_norm, arm64_norm]
                try rw [hsp4']
                exact Entails.of_eq (by dsimp only [fsp, st_dp]; simp only [wp_norm, arm64_norm]; sep_ac_rfl)
              · dsimp only [dropPreKeyMsgSpec]
                simp only [sepExists_sepConj_left]
                apply r3b_sepWPp_exists_left; intro evs_dm
                simp only [sepConj_assoc]
                apply r3b_sepWPp_pure_left; rintro ⟨htr_dm, hdm_free⟩
                let st_dm := M.stepEvents evs_dm st_dp
                have htr5_eq : s5.trace = s4.trace :=
                  htr_dm.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
                have hfs5_eq : s5.fs.files = s4.fs.files :=
                  (r3b_files_of_trace_eq (hh.fs (runProgPlaced H) 579) hsteps_dm htr_dm).trans
                    (by simp only [r3b_stOf, wp_norm, arm64_norm])
                have hs5_pre : InRunPlaced CodeOk s0 s5 0xb80 :=
                  r3b_inRun_step hs4 hpcm5 hrun5
                    (hsp5.trans (by simp only [r3b_stOf, wp_norm, arm64_norm]))
                    (hcsm5.2.2.2.2.2.2.2.2.2.2.1.trans
                      (by simp only [r3b_stOf, wp_norm, arm64_norm]))
                    hinv5
                    (hcsm5.2.2.2.2.2.2.2.2.2.2.2.trans
                      (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm]))
                have hx19_5 : s5.readReg64 (.gpr 19#5) = g.stores :=
                  hcsm5.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19_4])
                have hx20_5 : s5.readReg64 (.gpr 20#5) = g.res :=
                  hcsm5.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20_4])
                have hx21_5 : s5.readReg64 (.gpr 21#5) = meG.name.cap :=
                  hcsm5.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21_4])
                have hx26_5 : s5.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 :=
                  hcsm5.2.2.2.2.2.2.2.1.trans
                    (by simp only [r3b_stOf, wp_norm, arm64_norm]; exact hx26_4)
                have hx28_5 : s5.readReg64 (.gpr 28#5) = meG.name.ptr :=
                  hcsm5.2.2.2.2.2.2.2.2.2.1.trans
                    (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28_4])
                rw [← hsp5, hs5_pre.sp]
                have hpc5 : s5.pc = runPcPlaced 0xb80 := hs5_pre.pc
                rw [runPcPlaced_eq] at hpc5
                have hrun5' : s5.status = .Running := hs5_pre.run
                apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := runPcPlaced 0xd94) hs5_pre.inv
                rw [runPcPlaced_eq]
                dsimp only [runProgPlaced, lsProg_579]
                by_vm_open (
                  wp_steps
                  refine SepWP.done
                    (by simp only [wp_norm, arm64_norm])
                    (by simp only [wp_norm, arm64_norm, hrun5'])
                    ⟨by simp only [wp_norm, arm64_norm], fun hvm6 hinv6 => ?_⟩
                  change SepWPp (runProgPlaced H) _ _ _ _ _ _
                  rw [← A.pool_transport lim st_dm s5 (r3b_stOf hinv6) hvm6]
                  have hs6 : InRunPlaced CodeOk s0 (r3b_stOf hinv6) 0xd94 :=
                    r3b_inRun_step hs5_pre
                      (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
                      (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun5'])
                      (by simp only [r3b_stOf, wp_norm, arm64_norm])
                      (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv6
                      (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
                  have htr6_eq : (r3b_stOf hinv6).trace = s4.trace :=
                    (by simp only [r3b_stOf, wp_norm, arm64_norm] :
                      (r3b_stOf hinv6).trace = s5.trace).trans htr5_eq
                  have hfs6_eq : (r3b_stOf hinv6).fs.files = s4.fs.files :=
                    (by simp only [r3b_stOf, wp_norm, arm64_norm] :
                      (r3b_stOf hinv6).fs.files = s5.fs.files).trans hfs5_eq
                  have htr6 : s0.trace <+: (r3b_stOf hinv6).trace := htr6_eq ▸ htr4
                  have hhist6 : RunHistOk g.i s0 (r3b_stOf hinv6) :=
                    r3b_hist_of_eq htr6_eq hfs6_eq hhist4
                  have hclean6 :
                      (memRegion (fsp + 0x4d0#64) 248 ∗
                        (fsp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                        ((fsp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
                        ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                        ((fsp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
                        memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                        memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2a0#64) 40 ∗
                        memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                        memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                        memRegion (fsp + 0x3e0#64) 240 ∗
                        memRegion (fsp + 0x1750#64) 240 ∗
                        memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                        memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840)) ∗
                      (lsLogOff ∗ anyHeap ∗ anyHeap) ⊢
                      memRegion fsp 0x220 ∗
                        memRegion (fsp + 0x280#64) 0xa0 ∗
                        memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) ∗
                        anyHeap := by
                    have h0_220 :
                        (fsp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                          ((fsp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
                          ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                          ((fsp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
                          memRegion (fsp + 0x28#64) (0x220 - 0x28) ⊢
                        memRegion fsp 0x220 := by
                      have h40 := r3b_slot5_to_mem40 fsp
                        ⟨lsρ cliPreKeyVtSym, g.stores + 0x50#64, lsρ cliSignedPreKeyVtSym,
                          g.stores + 0x78#64, lsρ cliKyberPreKeyVtSym⟩
                      dsimp only [r3b_slot5] at h40
                      rw [ProofLib.memRegion_split' (b := fsp) (n := 40) (k := 504)
                            (b' := fsp + 0x28#64) rfl (by bv_omega) (by decide)]
                      exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left h40)
                    have h280_a0 :
                        memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2a0#64) 40 ∗
                          memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) =
                        memRegion (fsp + 0x280#64) 0xa0 := by
                      rw [r3b_split_at fsp 0x280 0x20 0x320 (by decide) (by decide),
                          r3b_split_at fsp 0x2a0 40 0x320 (by decide) (by decide)]
                    have h350_all :
                        memRegion (fsp + 0x4d0#64) 248 ∗
                          memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                          memRegion (fsp + 0x3e0#64) 240 ∗
                          memRegion (fsp + 0x1750#64) 240 ∗
                          memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                          memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) =
                        memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) := by
                      rw [r3b_split_at fsp 0x350 (0x3e0 - 0x350) runLocalBytes (by decide) (by decide),
                          r3b_split_at fsp 0x3e0 240 runLocalBytes (by decide) (by decide),
                          r3b_split_at fsp 0x4d0 248 runLocalBytes (by decide) (by decide),
                          r3b_split_at fsp 0x5c8 (0x1750 - 0x5c8) runLocalBytes (by decide) (by decide),
                          r3b_split_at fsp 0x1750 240 runLocalBytes (by decide) (by decide)]
                      ac_rfl
                    exact r3b_perm
                      (sepConj_mono h0_220
                        (sepConj_mono (Entails.of_eq h280_a0)
                          (sepConj_mono (Entails.of_eq h350_all)
                            (entails_anyHeap (lsLogOff ∗ anyHeap ∗ anyHeap)))))
                      (by ac_rfl)
                  have hinp_back :
                      (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) = (g.inp ↦ₛ inputOf g.i g.c) := by
                    rw [hinp_c, pointsToBytes_cons]
                  cases e with
                  | error err =>
                    have hans_err : g.a = some none := by
                      have hnone := hout_dp.2.2
                      rw [hpeer_val, hme_val] at hnone
                      rw [hga, hnone]; rfl
                    have henv_dec_err : ∀ evs_drop, FreeOnlyEvs evs_drop →
                        ∃ evs,
                          R3bRecvPEnv S sEnvs PksmTryFromEnv g (.some meV meG) peerV rest evs ∧
                          M.stepEvents (evs_drop ++ r3bFreeMePeerEvs meG peerG) st_dm =
                            M.stepEvents evs st := by
                      intro evs_drop hfree_drop
                      refine ⟨evs_pk ++
                        (evs_dp ++ (evs_dm ++ (evs_drop ++ r3bFreeMePeerEvs meG peerG))), ?_, ?_⟩
                      · simp only [R3bRecvPEnv, _hparse]
                        exact SeqEnv.append hpk_ev0
                          (SeqEnv.append hdp_ev0
                            (FreeOnlyEvs.append hdm_free
                              (FreeOnlyEvs.append hfree_drop
                                (r3bFreeMePeerEvs_freeOnly meG peerG))))
                      · dsimp only [st_dm, st_dp, st_pk]
                        rw [M.stepEvents_append evs_pk, M.stepEvents_append evs_dp,
                            M.stepEvents_append evs_dm]
                    refine r3b_sepWPp_weaken_pre ?_
                      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudget.r3b_recvP_dec_err_placed_codeOk g' err peerG meG hh hdrop hstk32 hext_le hsub64 hs6
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19_5])
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20_5])
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21_5])
                        (by dsimp only [fsp] at hx26_5; simp only [r3b_stOf, wp_norm, arm64_norm, hx26_5])
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28_5])
                        htr6 hhist6 hans_err henv_dec_err hrej)
                    exact r3b_perm
                      (r3b_perm_post
                        (sepConj_mono hclean6
                          (sepConj_mono (Entails.of_eq hinp_back)
                            (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                              storesAt A.repAlloc g.stores g' ∗
                              protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
                              protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
                              runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20 ∗
                              decResAt A.repAlloc (fsp + 0x320#64) (.error err) ∗
                              stackAt fsp (resStack - runFrame) ∗
                              A.pool lim st_dm (r3b_stOf hinv6)))))
                        (by dsimp only [fsp, st_dm]; sep_ac_rfl))
                      (by dsimp only [fsp, st_dm]; sep_ac_rfl)
                  | ok pt =>
                    have hout_ok : g.a = some (some (namedWrites g'.writes, pt)) ∧
                        ∀ pw ∈ g'.writes, cliWrOk pw.1 := by
                      rcases hout_dp.2.2 with ⟨hsome, hwrok⟩
                      rw [hpeer_val, hme_val] at hsome
                      exact ⟨by rw [hga, hsome]; rfl, hwrok⟩
                    have henv_dec_ok :
                        ∃ evs,
                          R3bRecvPEnv S sEnvs PksmTryFromEnv g (.some meV meG) peerV rest evs ∧
                          M.stepEvents (r3bFreeMePeerEvs meG peerG) st_dm =
                            M.stepEvents evs st := by
                      refine ⟨evs_pk ++ (evs_dp ++ (evs_dm ++ r3bFreeMePeerEvs meG peerG)), ?_, ?_⟩
                      · simp only [R3bRecvPEnv, _hparse]
                        exact SeqEnv.append hpk_ev0
                          (SeqEnv.append hdp_ev0
                            (FreeOnlyEvs.append hdm_free (r3bFreeMePeerEvs_freeOnly meG peerG)))
                      · dsimp only [st_dm, st_dp, st_pk]
                        rw [M.stepEvents_append evs_pk, M.stepEvents_append evs_dp,
                            M.stepEvents_append evs_dm]
                    refine r3b_sepWPp_weaken_pre ?_
                      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudgetAux.r3b_recvP_dec_ok_placed_codeOk g' pt peerG meG hh hext_le hsub64 hs6
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19_5])
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20_5])
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21_5])
                        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28_5])
                        htr6 hhist6 hout_ok.1 hout_ok.2 henv_dec_ok hjoin)
                    exact r3b_perm
                      (r3b_perm_post
                        (sepConj_mono hclean6
                          (sepConj_mono (Entails.of_eq hinp_back)
                            (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                              storesAt A.repAlloc g.stores g' ∗
                              protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
                              protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
                              runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20 ∗
                              decResAt A.repAlloc (fsp + 0x320#64) (.ok pt) ∗
                              stackAt fsp (resStack - runFrame) ∗
                              A.pool lim st_dm (r3b_stOf hinv6)))))
                        (by dsimp only [fsp, st_dm]; sep_ac_rfl))
                      (by dsimp only [fsp, st_dm]; sep_ac_rfl))))

/-- `LibsignalFrozen lsmpl` specialization of `run_hop_recvP_of_codeOk_placed_ok` at
`slotsOfSigPkFrozenPlaced`. -/
theorem run_hop_recvP_frozen_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmTryFromEnv x = PksmTryFromEnv y := by
      intros; rfl)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y := by intros; rfl) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget.RunHopRecvPPlacedOf
      (CryptoVerification.LibsignalFrozen lsmpl)
      A lim cEnvs PksmTryFromEnv (R3bRecvPEnv S sEnvs PksmTryFromEnv)
      H B S
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim sEnvs S needs)
      resStack :=
  run_hop_recvP_of_codeOk_placed_ok
    (CodeOk := CryptoVerification.LibsignalFrozen lsmpl)
    (slots := LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
      A lim sEnvs S needs)
    (sEnvs := sEnvs) (needs := needs) rfl rfl hpksm_addr hdp_ghost

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
