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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailBuildMessage
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded `signal_session::run` Placed Arm `R3a`: Whisper Arm Proof

Defines the `Recv`-Whisper allocation-event envelope `R3aRecvWEnv` and proves
`run_hop_recvW_placed_ok_of_env`, `run_hop_recvW_placed_ok`, `run_hop_recvW_of_codeOk_placed_ok`,
and `run_hop_recvW_frozen_placed_ok` on Block `579` (`runProgPlaced H`) under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (SignalMessage SignalProtocolError)
open CryptoGames.LibsignalSessionApi (ApiError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey (signalMessageAt_relocate)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet (extHookStack logOff smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Wire (logOff_tryFromPlacedImg tryFromPlacedImg)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SignalMessageGhost errTag protocolAddressAt
   signalMessageAt signalMessageResultAt)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli (StoresGhost cliIdentityVtSym cliSessionVtSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV CallW RunCall callAt cliWrOk coinsInstalledPlaced coinsOf inputOf namedWrites
   ownedBytes runResAt runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553 blkPl_554)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtRunEntryPlaced Bytes DecSigGhost InRunPlaced MeAtDispatch PanicK RejectKind
   RunHistOk RunNeeds RunSem SlotAns addrNameHeap addrUpperAt addrValOf decResAt decResAt_ok
   dispatchCells dispatchMeHeap finish idVtPlaced protocolAddressAt_eq_parts runFiles runFsp
   runPcPlaced runPcPlaced_eq runProgPlaced runSaved sessVtPlaced slotOut slotTrace)
open CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers
  (R1cCodeOk r1c_W6 r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
   r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setPState
   r1c_calleeSavedVRegs_writeReg64 r1c_extractLsb_append_hi r1c_extractLsb_append_lo
   r1c_fs_setMem r1c_fs_setPC r1c_fs_setPState r1c_fs_writeReg64 r1c_fs_writeVReg128
   r1c_mem48_to_slot6 r1c_mem_setPState r1c_readReg64_setPState r1c_sepWPp_exists_left
   r1c_sepWPp_pure_left r1c_sepWPp_weaken_pre r1c_slot6 r1c_slot6_to_mem48 r1c_spAligned
   r1c_sp_setPState r1c_stackAt_split_ge r1c_status_setPState r1c_symtab_setPState
   r1c_trace_setPState r1c_with_speOwned_words6)
open CryptoVerification.SignalSession.Cli.RunDrop (SpeOwned speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunProofs
  (decResAt_err_owned msgResultAt_err_owned sret120_rejoin)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame runNeed)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv VmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cHelpersPlacedBudget
  (r1c_call_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aPlacedBudget
  (RunHopRecvWPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux
  (r3a_accept_tail r3a_addrNameHeap_atState r3a_addrNameHeap_cap_lt r3a_addrUpper_relocate
   r3a_bounds r3a_callRecv_open r3a_cs_regs r3a_drop_spe_call r3a_files_eq r3a_frameGaps
   r3a_frame_seq_vm r3a_frame_some_eq r3a_freeOnly_append r3a_freeOnly_nil r3a_hiGaps
   r3a_hist_eq r3a_hist_of_slotTrace r3a_hist_step r3a_locals_empty_rest r3a_memRegion_words
   r3a_open_words r3a_pack_peer r3a_rejoin_1d0 r3a_res_split r3a_restFrame
   r3a_sepWPp_bind r3a_sepWPp_exists_left r3a_sigTryFrom_ok r3a_slotOut_err r3a_slotOut_ok
   r3a_storesAt_atState r3a_tail_me_reject r3a_tail_peer_reject r3a_tw r3a_words64At
   r3a_words_to_memRegion tryFromEnv_iff_bytes)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlacedEnv RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decSigSlotSpecPlaced slotFramePlaced slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (callAt_atState dispatchMemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessageBudget
  (dropSignalMessageSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced dropSignalMessage_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux (tryFromPlacedSpecGen)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
  (TryFromEnv tryFromPlacedSpec)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

private theorem r3a_readVReg128_writeReg64 (s : State) (r : Reg) (v : BitVec 64) (i : BitVec 5) :
    (s.writeReg64 r v).readVReg128 i = s.readVReg128 i := by cases s; cases r <;> rfl
private theorem r3a_readVReg128_setPC (s : State) (pc : BitVec 64) (i : BitVec 5) :
    (s.setPC pc).readVReg128 i = s.readVReg128 i := by cases s; rfl
private theorem r3a_readVReg128_setMem (s : State) (m : Memory) (i : BitVec 5) :
    (s.setMem m).readVReg128 i = s.readVReg128 i := by cases s; rfl
private theorem r3a_readVReg128_setPState (s : State) (ps : PState) (i : BitVec 5) :
    (s.setPState ps).readVReg128 i = s.readVReg128 i := by cases s; rfl
private theorem r3a_vreg_same (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).readVReg128 i = v := by
  simp [State.readVReg128, State.writeVReg128, VRegFile.read, VRegFile.write]
private theorem r3a_vreg_01 (s : State) (v : BitVec 128) :
    (s.writeVReg128 1#5 v).readVReg128 0#5 = s.readVReg128 0#5 := rfl
private theorem r3a_vreg_02 (s : State) (v : BitVec 128) :
    (s.writeVReg128 2#5 v).readVReg128 0#5 = s.readVReg128 0#5 := rfl
private theorem r3a_vreg_10 (s : State) (v : BitVec 128) :
    (s.writeVReg128 0#5 v).readVReg128 1#5 = s.readVReg128 1#5 := rfl
private theorem r3a_vreg_12 (s : State) (v : BitVec 128) :
    (s.writeVReg128 2#5 v).readVReg128 1#5 = s.readVReg128 1#5 := rfl
private theorem r3a_vreg_20 (s : State) (v : BitVec 128) :
    (s.writeVReg128 0#5 v).readVReg128 2#5 = s.readVReg128 2#5 := rfl
private theorem r3a_vreg_21 (s : State) (v : BitVec 128) :
    (s.writeVReg128 1#5 v).readVReg128 2#5 = s.readVReg128 2#5 := rfl

private theorem r3a_sepWP_seq_vm {prog : Program} {mid tgt : BitVec 64}
    {s : State} {P P' P'' : SepProp} {post1 post2 : State → Prop}
    (h1 : SepWP prog mid s P (fun s1 P1 => VmPreserved s s1 ∧ post1 s1 ∧ (P1 ⊢ P')))
    (h2 : ∀ s1 : State, VmPreserved s s1 → s1.pc = mid → s1.status = .Running → post1 s1 →
      SepWP prog tgt s1 P' (fun s2 P2 => VmPreserved s1 s2 ∧ post2 s2 ∧ (P2 ⊢ P''))) :
    SepWP prog tgt s P (fun s2 P2 => VmPreserved s s2 ∧ post2 s2 ∧ (P2 ⊢ P'')) := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, hvm1, hp1, hent1⟩ | ⟨_, hf⟩⟩ :=
    SepWP.to_reaches_pc h1 hm hL
  · have hm1' : s1.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent1) hm1
    obtain ⟨s2, hst2, ⟨hpc2, hrun2, P2, hm2, hvm2, hp2, hent2⟩ | ⟨_, hf⟩⟩ :=
      SepWP.to_reaches_pc (h2 s1 hvm1 hpc1 hrun1 hp1) hm1' (hst1.codeLoaded hL)
    · exact ⟨s2, hst1.trans hst2, Or.inl ⟨hpc2, hrun2, P2, hm2, hvm1.trans hvm2, hp2, hent2⟩⟩
    · exact (not_satisfies_false_sepConj hf).elim
  · exact (not_satisfies_false_sepConj hf).elim

attribute [local simp, local arm64_norm, local wp_norm]
  r1c_extractLsb_append_lo r1c_extractLsb_append_hi
  r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
  r1c_calleeSavedVRegs_writeReg64
  r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPState
  r1c_readReg64_setPState r1c_sp_setPState r1c_mem_setPState r1c_status_setPState
  r1c_trace_setPState r1c_symtab_setPState r1c_fs_setPState
  r1c_fs_writeReg64 r1c_fs_writeVReg128 r1c_fs_setPC r1c_fs_setMem
  r3a_readVReg128_writeReg64 r3a_readVReg128_setPC r3a_readVReg128_setMem r3a_readVReg128_setPState
  r3a_vreg_same r3a_vreg_01 r3a_vreg_02 r3a_vreg_10 r3a_vreg_12 r3a_vreg_20 r3a_vreg_21

local macro "r3a_close_post" : tactic =>
  `(tactic| (repeat' apply And.intro; all_goals ((try simp (config := { zetaDelta := true }) only [runPcPlaced_eq, RejectKind.pcOff, sessVtPlaced, idVtPlaced, cliSessionVtSym, cliIdentityVtSym, LibsignalBinary.Proofs.Placed.Bridge.lsρ, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, runFsp, wp_norm, arm64_norm, *]); try rfl; try bv_omega)))

/-! ## 1. Canonical Ghost Builders and Non-Vacuous `R3aRecvWEnv` -/

/-- Canonical `AddrGhost` built from `CallW` and `peerV`. -/
def r3aPeerGhost (w : CallW) (peerV : AddrV) : AddrGhost :=
  ⟨⟨w.w1, w.w2, peerV.name⟩, peerV.device⟩

/-- Pointer-free representative `AddrGhost` for `peerV` (same `.val` as `r3aPeerGhost w peerV`). -/
def r3aPeerGhost0 (peerV : AddrV) : AddrGhost :=
  ⟨⟨0#64, 0#64, peerV.name⟩, peerV.device⟩

/-- Canonical `DecSigGhost` constructed by Arm `R3a` at frame `fsp`. -/
def r3aDecSigGhost (g : RunCall) (fsp : BitVec 64) (peerG meG : AddrGhost)
    (msgG : SignalMessageGhost) (m : SignalMessage) : DecSigGhost where
  peer := peerG
  peerA := fsp + 0x220#64
  me := meG
  meA := fsp + 0x260#64
  stores := g.stores
  ret := fsp + 0x320#64
  coinsP := g.coins
  F := runFiles g.i
  coins := coinsOf g.i
  msgA := fsp + 0x4d0#64
  msgG := msgG
  msg := m

def r3aMsgGhost0 : SignalMessageGhost where
  pqCap := 0#64
  pqPtr := 0#64
  ctPtr := 0#64
  serPtr := 0#64
  addrPtr := 0#64

def r3aDecSigGhost0 (g : RunCall) (peerV : AddrV) (meG : AddrGhost) (m : SignalMessage) :
    DecSigGhost :=
  r3aDecSigGhost g 0#64 (r3aPeerGhost0 peerV) meG r3aMsgGhost0 m

/-- Concrete, non-vacuous allocation-event envelope for Arm `R3a` (`Recv` Whisper):
- on `me = .none`: deallocation-only (`FreeOnlyEvs`);
- on `me = .some meV meG`: `TryFromEnv` on `rest`, followed by `FreeOnlyEvs` on `try_from` error
  or `SeqEnv (sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m)) FreeOnlyEvs` on `try_from = .ok m`. -/
def R3aRecvWEnv (sEnvs : RunSlotEnvs) (g : RunCall) (me : MeAtDispatch)
    (peerV : AddrV) (rest : List (BitVec 8)) : List AllocEvent → Prop :=
  match me with
  | .none => FreeOnlyEvs
  | .some _ meG =>
      SeqEnv (TryFromEnv ⟨0#64, rest, 0#64⟩)
        (match SignalMessage.tryFrom protoSignalCodec rest with
         | .error _ => FreeOnlyEvs
         | .ok m => SeqEnv (sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m)) FreeOnlyEvs)

/-! ## 2. Error and Drop Continuations (`R+0x7f0`, `R+0xd8c`, `R+0xd94`) -/

set_option maxHeartbeats 1600000 in
theorem r3a_after_decrypt_err [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost}
    {err : ApiError AddrVal Unit} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hext : extHookStack ≤ resStack - runFrame)
    (h32 : 32 + extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 3476)
    (herr : err ≠ .store ())
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' .postDispatch (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion (runFsp s0 + 0x4d0#64) 120 ∗ A.pool lim st s ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗
        (decResAt A.repAlloc (runFsp s0 + 0x320#64) (.error err) ∗
          protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
          protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
          storesAt A.repAlloc g.stores g' ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ r3a_restFrame (runFsp s0) ∗ anyHeap))
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  have hm120 : memRegion (fsp + 0x4d0#64) 120 =
      memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) 72 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (fsp + 0x4d0#64) 48 72 (by decide)
  let errBase : SepProp := memRegion (fsp + 0x500#64) 72 ∗
    protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    storesAt A.repAlloc g.stores g' ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ r3a_restFrame fsp ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ k : SpeOwned, speOwnedAt A.repAlloc (fsp + 0x320#64) k) ∗
      ((∃∗ dv : r1c_W6, r1c_slot6 (fsp + 0x4d0#64) dv) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase))
    (by
      dsimp +zetaDelta only at hm120 ⊢; rw [hm120]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono (decResAt_err_owned A.repAlloc (runFsp s0 + 0x320#64) err herr)
          (sepConj_mono_left (r1c_mem48_to_slot6 (runFsp s0 + 0x4d0#64)))))
    (r3a_sepWPp_exists_left fun k => ?_)
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ dv : r1c_W6, r1c_slot6 (fsp + 0x4d0#64) dv) ∗
      (speOwnedAt A.repAlloc (fsp + 0x320#64) k ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
    (r3a_sepWPp_exists_left fun dv => ?_)
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x320#64) k ∗
      (r1c_slot6 (fsp + 0x4d0#64) dv ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)) ?_
  refine r1c_with_speOwned_words6 (dst := fsp + 0x4d0#64)
    fun sw H_spe hu3 hu2 hspe_close => ?_
  have hpc : s.pc = runPcPlaced 3476 := hs.pc
  change s.pc = (blkPl_579).base + 3476#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  rw [← hs.sp] at hx26
  have hb3 : (sw.w0 + 3#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hu3
  have hb2 : (sw.w0 + 2#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hu2
  let P_step : SepProp := r1c_slot6 (s.sp + 0x320#64) sw ∗ r1c_slot6 (s.sp + 0x4d0#64) dv
  let P_after : SepProp := r1c_slot6 (s.sp + 0x320#64) sw ∗ r1c_slot6 (s.sp + 0x4d0#64) sw
  have hstep : SepWP (runProgPlaced H) (blkPl_553).base s P_step
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .lr = runPcPlaced 4076 ∧
          s1.readReg64 .x0 = fsp + 0x4d0#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
          s1.readReg64 (.gpr 21#5) = meG.name.cap ∧ s1.readReg64 (.gpr 28#5) = meG.name.ptr) ∧
        (P1 ⊢ P_after)) := by
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after, r1c_slot6]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hP_in :
      r1c_slot6 (fsp + 0x320#64) sw ∗ H_spe ∗
        (r1c_slot6 (fsp + 0x4d0#64) dv ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase) ⊢
      P_step ∗ (H_spe ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase) := by
    dsimp +zetaDelta only [P_step]; rw [hs.sp]; exact Entails.of_eq (by sep_ac_rfl)
  refine r3a_frame_seq_vm hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1
      ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx19_1, hx20_1, hx21_1, hx28_1⟩ => ?_
  have hal1 : s1.spAligned = true := r1c_spAligned hs.spAligned hsp1
  rw [← A.pool_transport lim st s s1 hvm1]
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x4d0#64) k ∗ A.pool lim st s1 ∗ stackAt fsp sub ∗
      (memRegion (fsp + 0x320#64) 48 ∗ errBase))
    (by
      dsimp only [P_after]; rw [hs.sp]
      have hm320 := r1c_slot6_to_mem48 (fsp + 0x320#64) sw
      dsimp +zetaDelta only at hspe_close hm320 ⊢
      exact Entails.trans (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
        (Entails.trans
          (sepConj_mono hspe_close
            (sepConj_mono hm320
              (Entails.refl (A.pool lim st s1 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ errBase))))
          (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)))) ?_
  refine r3a_drop_spe_call (k := k) hdrop h32 hsub64 hinv1 hpc1 hrun1 hal1 hlr1 hsp1 hfp1 hv1
    hs.spAligned hx0_1 fun s2 evs_drop hfree_drop hsteps2 hin2 hcsm2 htr2 => ?_
  have hcs2 := r3a_cs_regs hcsm2
  have htr2_tot : s0.trace <+: s2.trace := (htr2.trans htr1) ▸ htr
  have hhist2 : RunHistOk g.i s0 s2 :=
    r3a_hist_step hh hsteps2 htr2 (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist)
  let st2 := M.stepEvents evs_drop st
  have henv2 : ∀ evs_rem, FreeOnlyEvs evs_rem →
      EnvAt g' .postDispatch (M.stepEvents evs_rem st2) := by
    intro evs_rem hf_rem
    rw [← M.stepEvents_append]
    exact henv (evs_drop ++ evs_rem) (r3a_freeOnly_append hfree_drop hf_rem)
  refine r1c_sepWPp_weaken_pre ?_
    (r3a_tail_me_reject (g' := g') (peerG := peerG) (meG := meG) hh hext hsub64 hin2
      (hcs2.1.trans hx19_1) (hcs2.2.1.trans hx20_1) (hcs2.2.2.1.trans hx21_1)
      (hcs2.2.2.2.2.1.trans hx28_1) htr2_tot hhist2 hans henv2 hrej)
  dsimp +zetaDelta only at hm120 ⊢
  have hrej120 :
      memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x500#64) 72 ∗
        stackAt (runFsp s0) (resStack - runFrame) =
      memRegion (runFsp s0 + 0x4d0#64) 120 ∗ stackAt (runFsp s0) (resStack - runFrame) := by
    rw [← sepConj_assoc, ← hm120]
  exact Entails.trans
    (Entails.of_eq (show _ =
      (memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x500#64) 72 ∗
        stackAt (runFsp s0) (resStack - runFrame)) ∗
      (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
        r3a_restFrame (runFsp s0) ∗ A.pool lim st2 s2 ∗ anyHeap) by sep_ac_rfl))
    (by rw [hrej120]; exact Entails.of_eq (by sep_ac_rfl))

set_option maxHeartbeats 1600000 in
theorem r3a_recvW_try_err [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {peerG meG : AddrGhost} {e : SignalProtocolError}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hext : extHookStack ≤ resStack - runFrame)
    (h32 : 32 + extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 2032)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (signalMessageResultAt A.repAlloc [] (runFsp s0 + 0x4d0#64) (.error e) ∗
        A.pool lim st s ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
          protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
          r3a_restFrame (runFsp s0) ∗ anyHeap))
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let tryErrRest : SepProp := memRegion (fsp + 0x508#64) 64 ∗
    protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    storesAt A.repAlloc g.stores StoresGhost.opened ∗
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x320#64) 48 ∗
    memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗ r3a_frameGaps fsp ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ k : SpeOwned, speOwnedAt A.repAlloc (fsp + 0x4d8#64) k) ∗
      ((∃∗ dv : r1c_W6, r1c_slot6 (fsp + 0x23b0#64) dv) ∗
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest))
    (by
      dsimp +zetaDelta only [r3a_restFrame]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact Entails.trans
        (sepConj_mono_left (msgResultAt_err_owned A.repAlloc [] (runFsp s0 + 0x4d0#64) e))
        (Entails.trans (Entails.of_eq (by sep_ac_rfl))
          (sepConj_mono_right (sepConj_mono_left (r1c_mem48_to_slot6 (runFsp s0 + 0x23b0#64))))))
    (r3a_sepWPp_exists_left fun k => ?_)
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ dv : r1c_W6, r1c_slot6 (fsp + 0x23b0#64) dv) ∗
      (speOwnedAt A.repAlloc (fsp + 0x4d8#64) k ∗
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
    (r3a_sepWPp_exists_left fun dv => ?_)
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x4d8#64) k ∗
      (r1c_slot6 (fsp + 0x23b0#64) dv ∗
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)) ?_
  refine r1c_with_speOwned_words6 (dst := fsp + 0x23b0#64)
    fun sw H_spe _ _ hspe_close => ?_
  have hpc : s.pc = runPcPlaced 2032 := hs.pc
  change s.pc = (blkPl_579).base + 2032#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  rw [← hs.sp] at hx26
  let P_step : SepProp :=
    ((s.sp + 0x4d0#64) ↦₆₄ errTag) ∗ r1c_slot6 (s.sp + 0x4d8#64) sw ∗
      r1c_slot6 (s.sp + 0x23b0#64) dv
  let P_after : SepProp :=
    ((s.sp + 0x4d0#64) ↦₆₄ errTag) ∗ r1c_slot6 (s.sp + 0x4d8#64) sw ∗
      r1c_slot6 (s.sp + 0x23b0#64) sw
  have hstep : SepWP (runProgPlaced H) (blkPl_553).base s P_step
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .lr = runPcPlaced 4076 ∧
          s1.readReg64 .x0 = fsp + 0x23b0#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
          s1.readReg64 (.gpr 21#5) = meG.name.cap ∧ s1.readReg64 (.gpr 28#5) = meG.name.ptr) ∧
        (P1 ⊢ P_after)) := by
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after, r1c_slot6, errTag]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hP_in :
      r1c_slot6 (fsp + 0x4d8#64) sw ∗ H_spe ∗
        (r1c_slot6 (fsp + 0x23b0#64) dv ∗
          ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest) ⊢
      P_step ∗ (H_spe ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest) := by
    dsimp +zetaDelta only [P_step]; rw [hs.sp]; exact Entails.of_eq (by sep_ac_rfl)
  refine r3a_frame_seq_vm hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1
      ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx19_1, hx20_1, hx21_1, hx28_1⟩ => ?_
  have hal1 : s1.spAligned = true := r1c_spAligned hs.spAligned hsp1
  rw [← A.pool_transport lim st s s1 hvm1]
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x23b0#64) k ∗ A.pool lim st s1 ∗ stackAt fsp sub ∗
      (memRegion (fsp + 0x4d0#64) 120 ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x320#64) 48 ∗
        memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗
        r3a_frameGaps fsp ∗ anyHeap))
    (by
      dsimp only [P_after]; rw [hs.sp]
      have hm4d0 : ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ r1c_slot6 (fsp + 0x4d8#64) sw ∗
          memRegion (fsp + 0x508#64) 64 ⊢ memRegion (fsp + 0x4d0#64) 120 := by
        refine Entails.trans
          (sepConj_mono_right (sepConj_mono_left (r1c_slot6_to_mem48 (fsp + 0x4d8#64) sw))) ?_
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sret120_rejoin (fsp + 0x4d0#64) errTag
      dsimp +zetaDelta only at hspe_close hm4d0 ⊢
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (Entails.trans
          (sepConj_mono hspe_close
            (sepConj_mono hm4d0
              (Entails.refl (A.pool lim st s1 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
                protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
                protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
                storesAt A.repAlloc g.stores StoresGhost.opened ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
                memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
                memRegion (runFsp s0 + 0x380#64) 16 ∗ memRegion (runFsp s0 + 0x460#64) 112 ∗
                r3a_frameGaps (runFsp s0) ∗ anyHeap))))
          (Entails.of_eq (by sep_ac_rfl)))) ?_
  refine r3a_drop_spe_call (k := k) hdrop h32 hsub64 hinv1 hpc1 hrun1 hal1 hlr1 hsp1 hfp1 hv1
    hs.spAligned hx0_1 fun s2 evs_drop hfree_drop hsteps2 hin2 hcsm2 htr2 => ?_
  have hcs2 := r3a_cs_regs hcsm2
  have htr2_tot : s0.trace <+: s2.trace := (htr2.trans htr1) ▸ htr
  have hhist2 : RunHistOk g.i s0 s2 :=
    r3a_hist_step hh hsteps2 htr2 (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist)
  let st2 := M.stepEvents evs_drop st
  have henv2 : ∀ evs_rem, FreeOnlyEvs evs_rem →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs_rem st2) := by
    intro evs_rem hf_rem
    rw [← M.stepEvents_append]
    exact henv (evs_drop ++ evs_rem) (r3a_freeOnly_append hfree_drop hf_rem)
  exact r1c_sepWPp_weaken_pre
    (by dsimp +zetaDelta only [r3a_restFrame]; exact Entails.of_eq (by sep_ac_rfl))
    (r3a_tail_me_reject (g' := StoresGhost.opened) (peerG := peerG) (meG := meG)
      hh hext hsub64 hin2
      (hcs2.1.trans hx19_1) (hcs2.2.1.trans hx20_1) (hcs2.2.2.1.trans hx21_1)
      (hcs2.2.2.2.2.1.trans hx28_1) htr2_tot hhist2 hans henv2 hrej)

set_option maxHeartbeats 1600000 in
theorem r3a_after_decrypt_drop [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvRej : StoresGhost → RejectKind → M.σ → Prop}
    {EnvJoin : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {peerG meG : AddrGhost} {msgG : SignalMessageGhost} {m : SignalMessage}
    {ans : SlotAns Bytes} {res : Except (ApiError AddrVal Unit) Bytes}
    {s0 s1 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (h32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 3468)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (_htr_s1 : s0.trace <+: s1.trace)
    (hga : g.a = finish ans id)
    (hslot2 : slotOut ans g' res s1 s)
    (htr2_tot : s0.trace <+: s.trace)
    (hhist2 : RunHistOk g.i s0 s)
    (henv_rej : ∀ evs_tail, FreeOnlyEvs evs_tail →
      EnvRej g' .postDispatch (M.stepEvents evs_tail st))
    (henv_join : ∀ out, res = .ok out → ∀ evs_tail, FreeOnlyEvs evs_tail →
      EnvJoin g' out (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim EnvRej g s0 resStack Q Qp)
    (hjoin : JoinKPlacedEnv R1cCodeOk H A lim EnvJoin g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (storesAt A.repAlloc g.stores g' ∗ decResAt A.repAlloc (runFsp s0 + 0x320#64) res ∗
        signalMessageAt A.repAlloc msgG (runFsp s0 + 0x4d0#64) m ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        (lsLogOff ∗ anyHeap ∗ A.pool lim st s ∗ stackAt (runFsp s0) (resStack - runFrame)) ∗
        (r3a_restFrame (runFsp s0) ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24)))
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let callKeep : SepProp := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24
  have hpc : s.pc = runPcPlaced 3468 := hs.pc
  change s.pc = (blkPl_579).base + 3468#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hstep : SepWP (runProgPlaced H) (blkPl_554).base s emp
      (fun s3 P3 => VmPreserved s s3 ∧
        (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s.trace ∧ s3.fs = s.fs ∧
          s3.readReg64 .lr = runPcPlaced 3476 ∧
          s3.readReg64 .x0 = fsp + 0x4d0#64 ∧
          s3.readReg64 (.gpr 19#5) = g.stores ∧ s3.readReg64 (.gpr 20#5) = g.res ∧
          s3.readReg64 (.gpr 21#5) = meG.name.cap ∧
          s3.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 ∧
          s3.readReg64 (.gpr 28#5) = meG.name.ptr) ∧
        (P3 ⊢ emp)) := by
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.refl _⟩
      r3a_close_post)
  refine r3a_frame_seq_vm hs.inv (Entails.of_eq (by rw [emp_sepConj])) hstep
    fun s3 hvm3 hinv3 hpc3 hrun3
      ⟨hsp3, hfp3, hv3, htr3, hfs3, hlr3, hx0_3, hx19_3, hx20_3, hx21_3, hx26_3, hx28_3⟩ => ?_
  have hal3 : s3.spAligned = true := r1c_spAligned hs.spAligned hsp3
  rw [emp_sepConj, ← A.pool_transport lim st s s3 hvm3]
  have hdsm_ok := dropSignalMessage_placed_ok (callerProg := runProgPlaced H) (i := 579) hh sub h32 hsub64
  let dropKeep : SepProp := storesAt A.repAlloc g.stores g' ∗
    decResAt A.repAlloc (fsp + 0x320#64) res ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
    r3a_restFrame fsp ∗ callKeep ∗ anyHeap
  refine r1c_call_lscro (⟨fsp + 0x4d0#64, msgG, m⟩, st) hdsm_ok hinv3 hpc3 hrun3 hal3 hlr3
    (F := dropKeep) ?_
    (hnext := fun s4 hsteps4 hinv4 hpcm4 hrun4 hsp4 hcsm4 => ?_)
  · dsimp only [dropSignalMessageSpec]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (lsLogOff ∗ anyHeap) ∗
          (signalMessageAt A.repAlloc msgG (fsp + 0x4d0#64) m ∗
            A.pool lim st s3 ∗ stackAt fsp sub ∗ storesAt A.repAlloc g.stores g' ∗
            decResAt A.repAlloc (fsp + 0x320#64) res ∗
            protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
            protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
            r3a_restFrame fsp ∗ callKeep) by dsimp +zetaDelta only; sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (entails_anyHeap _)) ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0_3, by rw [hlr3]; simp (config := { decide := true }) only [wp_norm, arm64_norm, runPcPlaced_eq]⟩
      (Entails.of_eq (by rw [hsp3]; dsimp +zetaDelta only; sep_ac_rfl))
  · dsimp only [dropSignalMessageSpec]
    rw [sepExists_sepConj_left]
    refine r1c_sepWPp_exists_left fun evs_dsm => ?_
    simp only [sepConj_assoc]
    refine r1c_sepWPp_pure_left fun ⟨htr4, hfree_dsm⟩ => ?_
    have hcs4 := r3a_cs_regs hcsm4; rw [hsp3]
    have hin4 : InRunPlaced R1cCodeOk s0 s4 3476 :=
      ⟨hpcm4, hrun4, hsp4.trans hsp3, hcs4.2.2.2.2.2.1.trans hfp3, hinv4,
        hcs4.2.2.2.2.2.2.trans hv3, hs.spAligned⟩
    have hx19_4 := hcs4.1.trans hx19_3; have hx20_4 := hcs4.2.1.trans hx20_3
    have hx21_4 := hcs4.2.2.1.trans hx21_3; have hx26_4 := hcs4.2.2.2.1.trans hx26_3
    have hx28_4 := hcs4.2.2.2.2.1.trans hx28_3
    have htr4_tot : s0.trace <+: s4.trace := (htr4.trans htr3) ▸ htr2_tot
    have hhist4 : RunHistOk g.i s0 s4 :=
      r3a_hist_step hh hsteps4 htr4 (r3a_hist_eq htr3 (congrArg FsState.files hfs3) hhist2)
    let st4 := M.stepEvents evs_dsm st
    cases res with
    | ok out =>
      obtain ⟨hans_ok, hwr⟩ := r3a_slotOut_ok hslot2
      have hans4 : g.a = some (some (namedWrites g'.writes, out)) := by
        rw [hga, hans_ok]; rfl
      have henv4 : ∀ evs_rem, FreeOnlyEvs evs_rem →
          EnvJoin g' out (M.stepEvents evs_rem st4) := by
        intro evs_rem hf_rem
        rw [← M.stepEvents_append]
        exact henv_join out rfl (evs_dsm ++ evs_rem) (r3a_freeOnly_append hfree_dsm hf_rem)
      exact r1c_sepWPp_weaken_pre
        (Entails.of_eq (by dsimp +zetaDelta only; rw [decResAt_ok]; sep_ac_rfl))
        (r3a_accept_tail (g' := g') (peerG := peerG) (meG := meG) (out := out)
          hh hext hsub64 hin4 hx19_4 hx20_4 hx21_4 hx28_4 htr4_tot hhist4 hans4 hwr henv4 hjoin)
    | error err =>
      obtain ⟨herr, hans_err⟩ := r3a_slotOut_err hga hslot2
      have henv4 : ∀ evs_rem, FreeOnlyEvs evs_rem →
          EnvRej g' .postDispatch (M.stepEvents evs_rem st4) := by
        intro evs_rem hf_rem
        rw [← M.stepEvents_append]
        exact henv_rej (evs_dsm ++ evs_rem) (r3a_freeOnly_append hfree_dsm hf_rem)
      exact r1c_sepWPp_weaken_pre
        (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
        (r3a_after_decrypt_err (g' := g') (peerG := peerG) (meG := meG)
          hh hdrop hext h32 hsub64 hin4 herr hx19_4 hx20_4 hx21_4 hx26_4 hx28_4
          htr4_tot hhist4 hans_err henv4 hrej)

/-! ## 3. `wrap_decrypt_signal` Call (`R+0x7f0`) and Entry Paths (`me = .none` / `me = .some`) -/

set_option maxHeartbeats 1600000 in
theorem r3a_after_try_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {EnvRej : StoresGhost → RejectKind → M.σ → Prop}
    {EnvJoin : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {peerG meG : AddrGhost} {msgG : SignalMessageGhost} {m : SignalMessage}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs))
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hrf : runFrame ≤ resStack)
    (hdec : needs.decryptSignal ≤ resStack - runFrame)
    (hsub63 : resStack - runFrame ≤ 2 ^ 63)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hspb : resStack ≤ s0.sp.toNat)
    (h32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext : extHookStack ≤ resStack - runFrame)
    (hs : InRunPlaced R1cCodeOk s0 s 2032)
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
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim EnvRej g s0 resStack Q Qp)
    (hjoin : JoinKPlacedEnv R1cCodeOk H A lim EnvJoin g s0 resStack Q Qp) :
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
    refine r3a_sepWP_seq_vm hstep1 fun s1a _ hpc1a hrun1a
      ⟨hsp1a, hfp1a, hv1a, htr1a, hfs1a, hx8_1a, hx9_1a, hv0_1a, hv1_1a, hv2_1a,
        hx19_1a, hx20_1a, hx21_1a, hx26_1a, hx28_1a⟩ => ?_
    refine r3a_sepWP_seq_vm (mid := (blkPl_579).base + 3380#64) (P' := P_after) (post1 := midPost2)
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
    refine r3a_sepWP_seq_vm (mid := (blkPl_579).base + 3396#64) (P' := P_after) (post1 := midPost3)
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
    refine r3a_sepWP_seq_vm (mid := (blkPl_579).base + 3404#64) (P' := P_after) (post1 := midPost4)
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
  refine r3a_frame_seq_vm hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1
      ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1,
        hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx8_1,
        hx19_1, hx20_1, hx21_1, hx26_1, hx28_1⟩ => ?_
  have hal1 : s1.spAligned = true := r1c_spAligned hs.spAligned hsp1
  dsimp only [preF]
  rw [← A.pool_transport lim st s s1 hvm1]
  have htr_s1 : s0.trace <+: s1.trace := htr1 ▸ htr
  have hdec_ok : subroutine_ok (runProgPlaced H) (lsmpl.base 463)
      (decSigSlotSpecPlaced A lim sEnvs.decryptSignal S sub) :=
    hc.decryptSignal sub hdec hsub63
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
  refine r1c_call_lscro (decCtx, st) hdec_ok hinv1 hpc1 hrun1 hal1 hlr1
    (F := r3a_restFrame fsp ∗ callKeep) ?_
    (hpanic := fun sf _ _ hp => by
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hpanic sf _ (Or.inl (by rw [hga]; dsimp only [decCtx, r3aDecSigGhost] at hp; rw [hp.1]; rfl)))
    (hnext := fun s2 _ hinv2 hpcm2 hrun2 hsp2 hcsm2 => ?_)
  · dsimp only [slotFramePlaced,
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
    have hin2 : InRunPlaced R1cCodeOk s0 s2 3468 :=
      ⟨hpcm2, hrun2, hsp2.trans hsp1, hcs2.2.2.2.2.2.1.trans hfp1, hinv2,
        hcs2.2.2.2.2.2.2.trans hv1, hs.spAligned⟩
    dsimp only [decCtx, r3aDecSigGhost]
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
      (r3a_after_decrypt_drop (g' := g') (peerG := peerG) (meG := meG) (msgG := msgG) (m := m)
        hh hdrop h32 hext hsub64 hin2
        (hcs2.1.trans hx19_1) (hcs2.2.1.trans hx20_1) (hcs2.2.2.1.trans hx21_1)
        (hcs2.2.2.2.1.trans hx26_1) (hcs2.2.2.2.2.1.trans hx28_1)
        htr_s1 hga hslot2 htr2_tot hhist2 henv_rej2 henv_join2 hrej hjoin)

set_option maxHeartbeats 1600000 in
private theorem r3a_some_pre_try [LibsignalPlacement]
    (A : RustAlloc) (pool : SepProp) (g : RunCall) (peerV : AddrV) (rest : Bytes)
    (s0 : State) (resStack : Nat) (meV : AddrV) (meG : AddrGhost) (w : CallW) (u1 : BitVec 64)
    (hme_bytes : meG.name.bytes = meV.name)
    (hsm : smallRootStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hcall56 : r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ⊢ memRegion g.call 56)
    (hpeer : r3a_words64At (runFsp s0 + 0x220#64) [w.w1, w.w2, w.w3, w.w4] ∗
      ownedBytes A w.w1 w.w2 w.w3 peerV.name ⊢
      protocolAddressAt A (r3aPeerGhost w peerV) (runFsp s0 + 0x220#64))
    (hme_close : ∀ dst : BitVec 64,
      r3a_words64At dst [BitVec.ofNat 64 meG.name.bytes.length, u1] ⊢ addrUpperAt dst meG)
    (h1d0 : r3a_words64At (runFsp s0 + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗
      memRegion (runFsp s0) 0x1d0 ∗ memRegion (runFsp s0 + 0x1e0#64) 40 ⊢
      memRegion (runFsp s0) 0x208) :
    (r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      r3a_words64At (runFsp s0 + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗
      r3a_words64At (runFsp s0 + 0x220#64) [w.w1, w.w2, w.w3, w.w4] ∗
      r3a_words64At (runFsp s0 + 0x260#64)
        [meG.name.cap, meG.name.ptr, BitVec.ofNat 64 meV.name.length, u1] ∗
      (g.inp ↦₈ 2#8)) ∗
      (ownedBytes A w.w1 w.w2 w.w3 peerV.name ∗ addrNameHeap A meG ∗
        ((g.inp + 1#64) ↦ₛ rest) ∗
        (memRegion g.res runResSize ∗
          storesAt A g.stores StoresGhost.opened ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff ∗
          runSaved s0 ∗ memRegion (runFsp s0) 0x1d0 ∗ memRegion (runFsp s0 + 0x1e0#64) 40 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
          memRegion (runFsp s0 + 0x380#64) 16 ∗ memRegion (runFsp s0 + 0x460#64) 112 ∗
          memRegion (runFsp s0 + 0x4d0#64) 120 ∗ memRegion (runFsp s0 + 0x23b0#64) 48 ∗
          r3a_hiGaps (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ pool)) ⊢
    ((g.inp + 1#64) ↦ₛ rest) ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗ lsLogOff ∗
      stackAt (runFsp s0) smallRootStack ∗ pool ∗
      (memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
        (resStack - runFrame - smallRootStack) ∗
        ((g.inp ↦₈ 2#8) ∗
          protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗
          protocolAddressAt A (r3aPeerGhost w peerV) (runFsp s0 + 0x220#64) ∗
          storesAt A g.stores StoresGhost.opened ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗ runSaved s0 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
          r3a_restFrame (runFsp s0))) := by
  have hsp_sm := r1c_stackAt_split_ge (runFsp s0) hsm hsub64
  simp only [r3a_words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hcall56 hpeer h1d0 ⊢
  have hme_up := hme_close (runFsp s0 + 0x270#64)
  simp only [r3a_words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hme_up
  have hme_pack :
      ((runFsp s0 + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((runFsp s0 + 0x268#64) ↦₆₄ meG.name.ptr) ∗
        (((runFsp s0 + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((runFsp s0 + 0x278#64) ↦₆₄ u1)) ∗ addrNameHeap A meG ⊢
      protocolAddressAt A meG (runFsp s0 + 0x260#64) := by
    rw [protocolAddressAt_eq_parts A meG (runFsp s0 + 0x260#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hme_up))
  dsimp +zetaDelta only [r3a_restFrame, r3a_frameGaps] at hcall56 hpeer hme_pack h1d0 hsp_sm ⊢
  rw [hme_bytes] at hme_pack; rw [hsp_sm]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (Entails.trans
      (sepConj_mono hcall56 (sepConj_mono hpeer (sepConj_mono hme_pack (sepConj_mono h1d0
        (Entails.refl (tokenInitPlacedAt ∗ lsLogOff ∗ pool ∗ runSaved s0 ∗
          r3a_hiGaps (runFsp s0) ∗ memRegion g.res runResSize ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
          memRegion (runFsp s0 + 0x380#64) 16 ∗ memRegion (runFsp s0 + 0x460#64) 112 ∗
          memRegion (runFsp s0 + 0x4d0#64) 120 ∗ memRegion (runFsp s0 + 0x23b0#64) 48 ∗
          memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - smallRootStack) ∗
          (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
          stackAt (runFsp s0) smallRootStack ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗
          storesAt A g.stores StoresGhost.opened))))))
      (Entails.of_eq (by sep_ac_rfl)))

set_option maxHeartbeats 1600000 in
theorem r3a_recvW_none [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {sEnvs : RunSlotEnvs}
    {EnvRej : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {peerV : AddrV} {rest : Bytes} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (he : AtRunEntryPlaced R1cCodeOk S g s0)
    (hd : AtDispatchPlaced R1cCodeOk g .none s0 s)
    (hcall : g.c = .recv peerV)
    (hstdin : g.i.stdin = 2#8 :: rest)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvRej StoresGhost.opened .postDispatch (M.stepEvents evs st))
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim EnvRej g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g .none s0 s resStack)
      Q Qp (fun _ => ⌜False⌝) := by
  obtain ⟨_, _, hsub64, _, _, hext, _⟩ := r3a_bounds hres hres64
  let fsp := runFsp s0; let sub := resStack - runFrame
  have hs : InRunPlaced R1cCodeOk s0 s 532 := hd.base
  have hpc : s.pc = runPcPlaced 532 := hs.pc
  change s.pc = (blkPl_579).base + 532#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa only [hcall, CallV.tag] using hd.x8
  have hx19 := hd.x19; have hx20 := hd.x20; have hx23 := hd.x23; have hx25 := hd.x25
  have hinp_eq : inputOf g.i g.c = 2#8 :: rest := by rw [hcall]; exact hstdin
  have hinp_merge : (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) = (g.inp ↦ₛ inputOf g.i g.c) := by
    rw [hinp_eq, pointsToBytes_cons]
  have hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (rest.length + 1) := by
    rw [hd.x24, hinp_eq]; rfl
  have hrest32 : rest.length < 2 ^ 32 := by
    simpa [hstdin] using he.rel.2.1.2.2.1 peerV (hcall ▸ he.parse)
  have hnz24 : (BitVec.ofNat 64 (rest.length + 1) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; bv_omega
  have hans0 : g.a = some none := hd.reject_of_me_none he
  have hx21 : s.readReg64 (.gpr 21#5) = -1#64 := hd.meRegs
  have hhist0 : RunHistOk g.i s0 s := ⟨hd.fs, hd.stdout⟩
  have hres_split := r3a_res_split g.res
  let noneTail : SepProp := memRegion (g.res + 8#64) (runResSize - 8) ∗
    storesAt A.repAlloc g.stores StoresGhost.opened ∗
    ((g.inp + 1#64) ↦ₛ rest) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗
    memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗
    r3a_restFrame fsp ∗ stackAt fsp sub ∗ A.pool lim st s
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ w : CallW, ⌜w.w4.setWidth 8 = peerV.device⌝ ∗
        r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
        ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name) ∗
      ((∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗
        memRegion (fsp + 0x220#64) 32 ∗ (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap)) ?_ ?_
  · dsimp +zetaDelta only [dispatchMemPlaced,
      CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced,
      dispatchMeHeap, dispatchCells]
    simp only [RustCliAllocBudget.atState_pool, callAt_atState, r3a_storesAt_atState]
    rw [hinp_eq, pointsToBytes_cons, hcall, hres_split, emp_sepConj,
      r3a_locals_empty_rest (runFsp s0)]
    refine Entails.trans
      (Entails.of_eq (show _ =
        callAt A.repAlloc g.call (.recv peerV) ∗
        (coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff) ∗
        ((∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗ memRegion (runFsp s0 + 0x220#64) 32 ∗
          (g.inp ↦₈ 2#8) ∗
          (memRegion (g.res + 8#64) (runResSize - 8) ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗
            ((g.inp + 1#64) ↦ₛ rest) ∗ runSaved s0 ∗
            memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x260#64) 32 ∗
            memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗
            r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
            A.pool lim st s)) by sep_ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono (r3a_callRecv_open A.repAlloc g.call peerV)
        (sepConj_mono_left (entails_anyHeap _)))
      (Entails.of_eq (by sep_ac_rfl))
  refine r3a_sepWPp_exists_left fun w => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine r1c_sepWPp_pure_left fun hw4 => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗
      (memRegion (fsp + 0x220#64) 32 ∗
        r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
        ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗
        (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap))
    (Entails.of_eq (by (try dsimp +zetaDelta only); try sep_ac_rfl))
    (r3a_sepWPp_exists_left fun w_res => ?_)
  refine r3a_sepWPp_bind (A0 := memRegion (fsp + 0x220#64) 32)
    (F := (g.res ↦₆₄ w_res) ∗
      r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗
      (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap) ?_ |>
    r1c_sepWPp_weaken_pre (Entails.of_eq (by (try dsimp +zetaDelta only); try sep_ac_rfl))
  intro R hm
  obtain ⟨ws220, hlen220, hm⟩ := r3a_memRegion_words 4 (fsp + 0x220#64) (by decide) hm
  rcases ws220 with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen220; done)
  refine ⟨r3a_words64At (fsp + 0x220#64) [p0, p1, p2, p3], hm, ?_⟩
  let P_step : SepProp :=
    (g.res ↦₆₄ w_res) ∗
      r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      r3a_words64At (s.sp + 0x220#64) [p0, p1, p2, p3] ∗ (g.inp ↦₈ 2#8)
  let P_after : SepProp :=
    (g.res ↦₆₄ 0xffffffffffffffff#64) ∗
      r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      r3a_words64At (s.sp + 0x220#64) [w.w1, w.w2, w.w3, w.w4] ∗ (g.inp ↦₈ 2#8)
  have hstep : SepWP (runProgPlaced H) (runPcPlaced 4104) s P_step
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores) ∧
        (P1 ⊢ P_after)) := by
    rw [runPcPlaced_eq]
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after, r3a_words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hP_in :
      r3a_words64At (fsp + 0x220#64) [p0, p1, p2, p3] ∗
        ((g.res ↦₆₄ w_res) ∗
          r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
          ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗
          (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap) ⊢
      P_step ∗ (ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗ noneTail ∗ anyHeap) := by
    dsimp +zetaDelta only [P_step]; rw [hs.sp]; exact Entails.of_eq (by sep_ac_rfl)
  refine r3a_frame_seq_vm hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
  dsimp only [noneTail]
  rw [← A.pool_transport lim st s s1 hvm1]
  refine r1c_sepWPp_weaken_pre ?_
    (r3a_tail_peer_reject (g' := StoresGhost.opened)
      (peerG := ⟨⟨w.w1, w.w2, peerV.name⟩, peerV.device⟩)
      hh hext hsub64 ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
      hx19_1 (htr1 ▸ hd.trace) (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist0)
      hans0 henv hrej)
  dsimp +zetaDelta only [P_after]; rw [hs.sp]
  have hpeer := r3a_pack_peer A.repAlloc (fsp + 0x220#64) peerV w.w1 w.w2 w.w3 w.w4 hw4
  have hcall56 := r3a_words_to_memRegion [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] g.call 56
  dsimp +zetaDelta only [runResAt] at hpeer hcall56 ⊢; rw [← hinp_merge]
  exact Entails.trans (Entails.of_eq (by (try dsimp +zetaDelta only); try sep_ac_rfl))
    (Entails.trans
      (sepConj_mono hpeer (sepConj_mono hcall56
        (Entails.refl ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦₈ 2#8) ∗
          ((g.inp + 1#64) ↦ₛ rest) ∗ runSaved s0 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x260#64) 32 ∗
          memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗
          r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim st s1 ∗ anyHeap))))
      (Entails.of_eq (by (try dsimp +zetaDelta only); try sep_ac_rfl)))

set_option maxHeartbeats 1600000 in
theorem r3a_recvW_some [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {RecvWEnv : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
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
    (hc : RunCalleesPlaced A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs))
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hspb : resStack ≤ s0.sp.toNat)
    (he : AtRunEntryPlaced R1cCodeOk S g s0)
    (hd : AtDispatchPlaced R1cCodeOk g (.some meV meG) s0 s)
    (hcall : g.c = .recv peerV)
    (hstdin : g.i.stdin = 2#8 :: rest)
    (hfit : FitsEnv M lim st (RecvWEnv g (.some meV meG) peerV rest))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim
      (fun _ _ st' => ∃ evs, RecvWEnv g (.some meV meG) peerV rest evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp)
    (hjoin : JoinKPlacedEnv R1cCodeOk H A lim
      (fun _ _ st' => ∃ evs, RecvWEnv g (.some meV meG) peerV rest evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g (.some meV meG) s0 s resStack)
      Q Qp (fun _ => ⌜False⌝) := by
  have htry := r3a_sigTryFrom_ok hh
  have hlog : logOff tryFromPlacedImg = lsLogOff := logOff_tryFromPlacedImg
  obtain ⟨hrf, hsub63, hsub64, hsm, h32, hext, hdec⟩ := r3a_bounds hres hres64
  let fsp := runFsp s0; let sub := resStack - runFrame
  have hs : InRunPlaced R1cCodeOk s0 s 532 := hd.base
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
  refine r3a_frame_seq_vm hs.inv hP_in hstep
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
      exact r3a_some_pre_try A.repAlloc (A.pool lim st s1) g peerV rest s0 resStack meV meG w u1
        hme_bytes hsm hsub64
        (r3a_words_to_memRegion [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] g.call 56)
        (r3a_pack_peer A.repAlloc (runFsp s0 + 0x220#64) peerV w.w1 w.w2 w.w3 w.w4 hw4)
        hme_close
        (r3a_rejoin_1d0 (runFsp s0) (BitVec.ofNat 64 meG.name.bytes.length) u1)) ?_
  have hfit_try : FitsEnv M lim st (TryFromEnv ⟨g.inp + 1#64, rest, fsp + 0x4d0#64⟩) :=
    fun evs hevs => hfit evs (h_try_fit evs (tryFromEnv_iff_bytes.mp hevs))
  refine r1c_call_lscro (⟨g.inp + 1#64, rest, fsp + 0x4d0#64⟩, st) htry hinv1 hpc1 hrun1 hal1 hlr1
    (F := memRegion (fsp - BitVec.ofNat 64 sub) (sub - smallRootStack) ∗ tryKeep) ?_
    (hnext := fun s2 hsteps2 hinv2 hpcm2 hrun2 hsp2 hcsm2 => ?_)
  · dsimp only [tryFromPlacedSpec, tryFromPlacedSpecGen]; rw [hlog]; simp only [sepConj_assoc]
    have hx1_nat : (s1.readReg64 .x1).toNat = rest.length := by
      rw [hx1_1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rest.length < 2 ^ 64)]
    refine Entails.pure_right ⟨hx0_1, hx1_nat, hrest32, hx8_1, hfit_try⟩ ?_
    exact Entails.of_eq (by rw [hsp1]; (try dsimp +zetaDelta only); try sep_ac_rfl)
  · have hcs2 := r3a_cs_regs hcsm2
    have hsp2_fsp : s2.sp = fsp := hsp2.trans hsp1
    have hin2 : InRunPlaced R1cCodeOk s0 s2 2032 :=
      ⟨hpcm2, hrun2, hsp2_fsp, hcs2.2.2.2.2.2.1.trans hfp1, hinv2,
        hcs2.2.2.2.2.2.2.trans hv1, hs.spAligned⟩
    have hx19_2 := hcs2.1.trans hx19_1; have hx20_2 := hcs2.2.1.trans hx20_1
    have hx21_2 := hcs2.2.2.1.trans hx21_1; have hx26_2 := hcs2.2.2.2.1.trans hx26_1
    have hx28_2 := hcs2.2.2.2.2.1.trans hx28_1
    dsimp only [tryFromPlacedSpec, tryFromPlacedSpecGen]; rw [hlog]; simp only [sepConj_assoc]
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
        (r3a_recvW_try_err (peerG := peerG) (meG := meG) (e := e)
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
    · dsimp only [signalMessageResultAt]
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
        exact ((LibsignalBinary.Heap.fitsEvents_append M lim evs_try evs_dec st).mp htot).2
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
        (r3a_after_try_ok (peerG := peerG) (meG := meG) (msgG := msgG) (m := m)
          hh hc hdrop hrf hdec hsub63 hsub64 hspb h32 hext hin2
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

/-! ## 4. Top-Level `RunHopRecvWPlaced` Theorems (`run_hop_recvW_placed_ok_of_env`, `run_hop_recvW_placed_ok`) -/

/-- Envelope-monotonicity form of `run_hop_recvW_placed_ok` for any caller-supplied `RecvWEnv`. -/
theorem run_hop_recvW_placed_ok_of_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {RecvWEnv : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (h_none : ∀ g peerV rest evs, FreeOnlyEvs evs → RecvWEnv g .none peerV rest evs)
    (h_try_fit : ∀ g meV meG peerV rest evs_try,
      TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try →
      RecvWEnv g (.some meV meG) peerV rest evs_try)
    (h_try_err : ∀ g meV meG peerV rest e,
      SignalMessage.tryFrom protoSignalCodec rest = .error e →
      ∀ evs_try evs_tail, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try → FreeOnlyEvs evs_tail →
        RecvWEnv g (.some meV meG) peerV rest (evs_try ++ evs_tail))
    (h_dec_fit : ∀ g fsp w peerV meV meG msgG rest m,
      SignalMessage.tryFrom protoSignalCodec rest = .ok m →
      ∀ evs_try evs_dec, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try →
        sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) evs_dec →
        RecvWEnv g (.some meV meG) peerV rest (evs_try ++ evs_dec))
    (h_dec_end : ∀ g fsp w peerV meV meG msgG rest m,
      SignalMessage.tryFrom protoSignalCodec rest = .ok m →
      ∀ evs_try evs_dec evs_tail, TryFromEnv ⟨0#64, rest, 0#64⟩ evs_try →
        sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) evs_dec →
        FreeOnlyEvs evs_tail →
        RecvWEnv g (.some meV meG) peerV rest (evs_try ++ (evs_dec ++ evs_tail))) :
    RunHopRecvWPlaced (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs sEnvs RecvWEnv H B S needs resStack := by
  intro g st s0 s me peerV rest Q Qp hh hc hdrop hres hres64 hspb he hd hcall hstdin hfit
    hpanic hrej hjoin
  cases me with
  | none =>
    exact r3a_recvW_none hh hres hres64 he hd hcall hstdin
      (fun evs hf => ⟨evs, h_none g peerV rest evs hf, rfl⟩) hrej
  | some meV meG =>
    exact r3a_recvW_some
      (h_try_fit g meV meG peerV rest)
      (h_try_err g meV meG peerV rest)
      (h_dec_fit g (runFsp s0) · peerV meV meG · rest)
      (h_dec_end g (runFsp s0) · peerV meV meG · rest)
      hh hc hdrop hres hres64 hspb he hd hcall hstdin hfit hpanic hrej hjoin

/-- Budget-threaded Arm `R3a` Whisper hop proof (`R+0x214 → R+0xf8c / R+0x2c7c`) on Block `579`
(`runProgPlaced H`), instantiated with `R3aRecvWEnv sEnvs` for any pointer-invariant
`sEnvs.decryptSignal`. -/
theorem run_hop_recvW_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) := by
      intros; rfl) :
    RunHopRecvWPlaced (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs sEnvs (R3aRecvWEnv sEnvs) H B S needs resStack :=
  run_hop_recvW_placed_ok_of_env
    (fun _ _ _ _ hf => hf)
    (fun _ _ _ _ _ _ ht => SeqEnv.inl ht)
    (fun _ _ _ _ _ _ hm _ _ ht hf => by
      dsimp only [R3aRecvWEnv]; rw [hm]
      exact SeqEnv.append ht hf)
    (fun g fsp w peerV _ meG msgG _ m hm _ _ ht hd => by
      dsimp only [R3aRecvWEnv]; rw [hm]; rw [hdec_ghost] at hd
      exact SeqEnv.append ht (SeqEnv.inl hd))
    (fun g fsp w peerV _ meG msgG _ m hm _ _ _ ht hd hf => by
      dsimp only [R3aRecvWEnv]; rw [hm]; rw [hdec_ghost] at hd
      exact SeqEnv.append ht (SeqEnv.append hd hf))



/-! ## 5. `CodeOk`-Parametric Counterparts (`run_hop_recvW_of_codeOk_placed_ok`) -/

private theorem r3a_call_codeOk [LibsignalPlacement]
    {CodeOk : Memory → Prop} [hCI : CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {α : Type} {prog : Program}
    {callee retAddr ret : BitVec 64} {spec : Spec α} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (x : α)
    (hcall : subroutine_ok prog callee (CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk CodeOk spec))
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
      s.mem ⊨ (CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk CodeOk spec).pre x s ∗ (F ∗ R) := by
    dsimp only [CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk]
    refine Satisfies.mono ?_ hm_pre
    exact Entails.trans
      (Entails.pure_right hinv (Entails.refl _))
      (Entails.of_eq (by sep_ac_rfl))
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) hpcm hrunm hspm hcsm R hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

set_option maxHeartbeats 1600000 in
private theorem r3a_after_decrypt_err_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost}
    {err : ApiError AddrVal Unit} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hext : extHookStack ≤ resStack - runFrame)
    (h32 : 32 + extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 3476)
    (herr : err ≠ .store ())
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' .postDispatch (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion (runFsp s0 + 0x4d0#64) 120 ∗ A.pool lim st s ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗
        (decResAt A.repAlloc (runFsp s0 + 0x320#64) (.error err) ∗
          protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
          protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
          storesAt A.repAlloc g.stores g' ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ r3a_restFrame (runFsp s0) ∗ anyHeap))
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  have hm120 : memRegion (fsp + 0x4d0#64) 120 =
      memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) 72 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (fsp + 0x4d0#64) 48 72 (by decide)
  let errBase : SepProp := memRegion (fsp + 0x500#64) 72 ∗
    protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    storesAt A.repAlloc g.stores g' ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ r3a_restFrame fsp ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ k : SpeOwned, speOwnedAt A.repAlloc (fsp + 0x320#64) k) ∗
      ((∃∗ dv : r1c_W6, r1c_slot6 (fsp + 0x4d0#64) dv) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase))
    (by
      dsimp +zetaDelta only at hm120 ⊢; rw [hm120]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono (decResAt_err_owned A.repAlloc (runFsp s0 + 0x320#64) err herr)
          (sepConj_mono_left (r1c_mem48_to_slot6 (runFsp s0 + 0x4d0#64)))))
    (r3a_sepWPp_exists_left fun k => ?_)
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ dv : r1c_W6, r1c_slot6 (fsp + 0x4d0#64) dv) ∗
      (speOwnedAt A.repAlloc (fsp + 0x320#64) k ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
    (r3a_sepWPp_exists_left fun dv => ?_)
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x320#64) k ∗
      (r1c_slot6 (fsp + 0x4d0#64) dv ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)) ?_
  refine r1c_with_speOwned_words6 (dst := fsp + 0x4d0#64)
    fun sw H_spe hu3 hu2 hspe_close => ?_
  have hpc : s.pc = runPcPlaced 3476 := hs.pc
  change s.pc = (blkPl_579).base + 3476#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  rw [← hs.sp] at hx26
  have hb3 : (sw.w0 + 3#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hu3
  have hb2 : (sw.w0 + 2#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hu2
  let P_step : SepProp := r1c_slot6 (s.sp + 0x320#64) sw ∗ r1c_slot6 (s.sp + 0x4d0#64) dv
  let P_after : SepProp := r1c_slot6 (s.sp + 0x320#64) sw ∗ r1c_slot6 (s.sp + 0x4d0#64) sw
  have hstep : SepWP (runProgPlaced H) (blkPl_553).base s P_step
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .lr = runPcPlaced 4076 ∧
          s1.readReg64 .x0 = fsp + 0x4d0#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
          s1.readReg64 (.gpr 21#5) = meG.name.cap ∧ s1.readReg64 (.gpr 28#5) = meG.name.ptr) ∧
        (P1 ⊢ P_after)) := by
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after, r1c_slot6]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hP_in :
      r1c_slot6 (fsp + 0x320#64) sw ∗ H_spe ∗
        (r1c_slot6 (fsp + 0x4d0#64) dv ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase) ⊢
      P_step ∗ (H_spe ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase) := by
    dsimp +zetaDelta only [P_step]; rw [hs.sp]; exact Entails.of_eq (by sep_ac_rfl)
  refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_frame_seq_vm_codeOk hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1
      ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx19_1, hx20_1, hx21_1, hx28_1⟩ => ?_
  have hal1 : s1.spAligned = true := r1c_spAligned hs.spAligned hsp1
  rw [← A.pool_transport lim st s s1 hvm1]
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x4d0#64) k ∗ A.pool lim st s1 ∗ stackAt fsp sub ∗
      (memRegion (fsp + 0x320#64) 48 ∗ errBase))
    (by
      dsimp only [P_after]; rw [hs.sp]
      have hm320 := r1c_slot6_to_mem48 (fsp + 0x320#64) sw
      dsimp +zetaDelta only at hspe_close hm320 ⊢
      exact Entails.trans (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
        (Entails.trans
          (sepConj_mono hspe_close
            (sepConj_mono hm320
              (Entails.refl (A.pool lim st s1 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ errBase))))
          (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)))) ?_
  refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_drop_spe_call_codeOk (k := k) hdrop h32 hsub64 hinv1 hpc1 hrun1 hal1 hlr1 hsp1 hfp1 hv1
    hs.spAligned hx0_1 fun s2 evs_drop hfree_drop hsteps2 hin2 hcsm2 htr2 => ?_
  have hcs2 := r3a_cs_regs hcsm2
  have htr2_tot : s0.trace <+: s2.trace := (htr2.trans htr1) ▸ htr
  have hhist2 : RunHistOk g.i s0 s2 :=
    r3a_hist_step hh hsteps2 htr2 (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist)
  let st2 := M.stepEvents evs_drop st
  have henv2 : ∀ evs_rem, FreeOnlyEvs evs_rem →
      EnvAt g' .postDispatch (M.stepEvents evs_rem st2) := by
    intro evs_rem hf_rem
    rw [← M.stepEvents_append]
    exact henv (evs_drop ++ evs_rem) (r3a_freeOnly_append hfree_drop hf_rem)
  refine r1c_sepWPp_weaken_pre ?_
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_tail_me_reject_codeOk (g' := g') (peerG := peerG) (meG := meG) hh hext hsub64 hin2
      (hcs2.1.trans hx19_1) (hcs2.2.1.trans hx20_1) (hcs2.2.2.1.trans hx21_1)
      (hcs2.2.2.2.2.1.trans hx28_1) htr2_tot hhist2 hans henv2 hrej)
  dsimp +zetaDelta only at hm120 ⊢
  have hrej120 :
      memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x500#64) 72 ∗
        stackAt (runFsp s0) (resStack - runFrame) =
      memRegion (runFsp s0 + 0x4d0#64) 120 ∗ stackAt (runFsp s0) (resStack - runFrame) := by
    rw [← sepConj_assoc, ← hm120]
  exact Entails.trans
    (Entails.of_eq (show _ =
      (memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x500#64) 72 ∗
        stackAt (runFsp s0) (resStack - runFrame)) ∗
      (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
        r3a_restFrame (runFsp s0) ∗ A.pool lim st2 s2 ∗ anyHeap) by sep_ac_rfl))
    (by rw [hrej120]; exact Entails.of_eq (by sep_ac_rfl))

set_option maxHeartbeats 1600000 in
private theorem r3a_recvW_try_err_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {peerG meG : AddrGhost} {e : SignalProtocolError}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hext : extHookStack ≤ resStack - runFrame)
    (h32 : 32 + extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 2032)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (signalMessageResultAt A.repAlloc [] (runFsp s0 + 0x4d0#64) (.error e) ∗
        A.pool lim st s ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
          protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
          r3a_restFrame (runFsp s0) ∗ anyHeap))
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let tryErrRest : SepProp := memRegion (fsp + 0x508#64) 64 ∗
    protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    storesAt A.repAlloc g.stores StoresGhost.opened ∗
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x320#64) 48 ∗
    memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗ r3a_frameGaps fsp ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ k : SpeOwned, speOwnedAt A.repAlloc (fsp + 0x4d8#64) k) ∗
      ((∃∗ dv : r1c_W6, r1c_slot6 (fsp + 0x23b0#64) dv) ∗
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest))
    (by
      dsimp +zetaDelta only [r3a_restFrame]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact Entails.trans
        (sepConj_mono_left (msgResultAt_err_owned A.repAlloc [] (runFsp s0 + 0x4d0#64) e))
        (Entails.trans (Entails.of_eq (by sep_ac_rfl))
          (sepConj_mono_right (sepConj_mono_left (r1c_mem48_to_slot6 (runFsp s0 + 0x23b0#64))))))
    (r3a_sepWPp_exists_left fun k => ?_)
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ dv : r1c_W6, r1c_slot6 (fsp + 0x23b0#64) dv) ∗
      (speOwnedAt A.repAlloc (fsp + 0x4d8#64) k ∗
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
    (r3a_sepWPp_exists_left fun dv => ?_)
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x4d8#64) k ∗
      (r1c_slot6 (fsp + 0x23b0#64) dv ∗
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)) ?_
  refine r1c_with_speOwned_words6 (dst := fsp + 0x23b0#64)
    fun sw H_spe _ _ hspe_close => ?_
  have hpc : s.pc = runPcPlaced 2032 := hs.pc
  change s.pc = (blkPl_579).base + 2032#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  rw [← hs.sp] at hx26
  let P_step : SepProp :=
    ((s.sp + 0x4d0#64) ↦₆₄ errTag) ∗ r1c_slot6 (s.sp + 0x4d8#64) sw ∗
      r1c_slot6 (s.sp + 0x23b0#64) dv
  let P_after : SepProp :=
    ((s.sp + 0x4d0#64) ↦₆₄ errTag) ∗ r1c_slot6 (s.sp + 0x4d8#64) sw ∗
      r1c_slot6 (s.sp + 0x23b0#64) sw
  have hstep : SepWP (runProgPlaced H) (blkPl_553).base s P_step
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .lr = runPcPlaced 4076 ∧
          s1.readReg64 .x0 = fsp + 0x23b0#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
          s1.readReg64 (.gpr 21#5) = meG.name.cap ∧ s1.readReg64 (.gpr 28#5) = meG.name.ptr) ∧
        (P1 ⊢ P_after)) := by
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after, r1c_slot6, errTag]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hP_in :
      r1c_slot6 (fsp + 0x4d8#64) sw ∗ H_spe ∗
        (r1c_slot6 (fsp + 0x23b0#64) dv ∗
          ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest) ⊢
      P_step ∗ (H_spe ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest) := by
    dsimp +zetaDelta only [P_step]; rw [hs.sp]; exact Entails.of_eq (by sep_ac_rfl)
  refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_frame_seq_vm_codeOk hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1
      ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx19_1, hx20_1, hx21_1, hx28_1⟩ => ?_
  have hal1 : s1.spAligned = true := r1c_spAligned hs.spAligned hsp1
  rw [← A.pool_transport lim st s s1 hvm1]
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x23b0#64) k ∗ A.pool lim st s1 ∗ stackAt fsp sub ∗
      (memRegion (fsp + 0x4d0#64) 120 ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x320#64) 48 ∗
        memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗
        r3a_frameGaps fsp ∗ anyHeap))
    (by
      dsimp only [P_after]; rw [hs.sp]
      have hm4d0 : ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ r1c_slot6 (fsp + 0x4d8#64) sw ∗
          memRegion (fsp + 0x508#64) 64 ⊢ memRegion (fsp + 0x4d0#64) 120 := by
        refine Entails.trans
          (sepConj_mono_right (sepConj_mono_left (r1c_slot6_to_mem48 (fsp + 0x4d8#64) sw))) ?_
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sret120_rejoin (fsp + 0x4d0#64) errTag
      dsimp +zetaDelta only at hspe_close hm4d0 ⊢
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (Entails.trans
          (sepConj_mono hspe_close
            (sepConj_mono hm4d0
              (Entails.refl (A.pool lim st s1 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
                protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
                protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
                storesAt A.repAlloc g.stores StoresGhost.opened ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
                memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
                memRegion (runFsp s0 + 0x380#64) 16 ∗ memRegion (runFsp s0 + 0x460#64) 112 ∗
                r3a_frameGaps (runFsp s0) ∗ anyHeap))))
          (Entails.of_eq (by sep_ac_rfl)))) ?_
  refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_drop_spe_call_codeOk (k := k) hdrop h32 hsub64 hinv1 hpc1 hrun1 hal1 hlr1 hsp1 hfp1 hv1
    hs.spAligned hx0_1 fun s2 evs_drop hfree_drop hsteps2 hin2 hcsm2 htr2 => ?_
  have hcs2 := r3a_cs_regs hcsm2
  have htr2_tot : s0.trace <+: s2.trace := (htr2.trans htr1) ▸ htr
  have hhist2 : RunHistOk g.i s0 s2 :=
    r3a_hist_step hh hsteps2 htr2 (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist)
  let st2 := M.stepEvents evs_drop st
  have henv2 : ∀ evs_rem, FreeOnlyEvs evs_rem →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs_rem st2) := by
    intro evs_rem hf_rem
    rw [← M.stepEvents_append]
    exact henv (evs_drop ++ evs_rem) (r3a_freeOnly_append hfree_drop hf_rem)
  exact r1c_sepWPp_weaken_pre
    (by dsimp +zetaDelta only [r3a_restFrame]; exact Entails.of_eq (by sep_ac_rfl))
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_tail_me_reject_codeOk (g' := StoresGhost.opened) (peerG := peerG) (meG := meG)
      hh hext hsub64 hin2
      (hcs2.1.trans hx19_1) (hcs2.2.1.trans hx20_1) (hcs2.2.2.1.trans hx21_1)
      (hcs2.2.2.2.2.1.trans hx28_1) htr2_tot hhist2 hans henv2 hrej)

set_option maxHeartbeats 1600000 in
private theorem r3a_after_decrypt_drop_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvRej : StoresGhost → RejectKind → M.σ → Prop}
    {EnvJoin : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {peerG meG : AddrGhost} {msgG : SignalMessageGhost} {m : SignalMessage}
    {ans : SlotAns Bytes} {res : Except (ApiError AddrVal Unit) Bytes}
    {s0 s1 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (h32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 3468)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (_htr_s1 : s0.trace <+: s1.trace)
    (hga : g.a = finish ans id)
    (hslot2 : slotOut ans g' res s1 s)
    (htr2_tot : s0.trace <+: s.trace)
    (hhist2 : RunHistOk g.i s0 s)
    (henv_rej : ∀ evs_tail, FreeOnlyEvs evs_tail →
      EnvRej g' .postDispatch (M.stepEvents evs_tail st))
    (henv_join : ∀ out, res = .ok out → ∀ evs_tail, FreeOnlyEvs evs_tail →
      EnvJoin g' out (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvRej g s0 resStack Q Qp)
    (hjoin : JoinKPlacedEnv CodeOk H A lim EnvJoin g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (storesAt A.repAlloc g.stores g' ∗ decResAt A.repAlloc (runFsp s0 + 0x320#64) res ∗
        signalMessageAt A.repAlloc msgG (runFsp s0 + 0x4d0#64) m ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        (lsLogOff ∗ anyHeap ∗ A.pool lim st s ∗ stackAt (runFsp s0) (resStack - runFrame)) ∗
        (r3a_restFrame (runFsp s0) ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24)))
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let callKeep : SepProp := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24
  have hpc : s.pc = runPcPlaced 3468 := hs.pc
  change s.pc = (blkPl_579).base + 3468#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hstep : SepWP (runProgPlaced H) (blkPl_554).base s emp
      (fun s3 P3 => VmPreserved s s3 ∧
        (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s.trace ∧ s3.fs = s.fs ∧
          s3.readReg64 .lr = runPcPlaced 3476 ∧
          s3.readReg64 .x0 = fsp + 0x4d0#64 ∧
          s3.readReg64 (.gpr 19#5) = g.stores ∧ s3.readReg64 (.gpr 20#5) = g.res ∧
          s3.readReg64 (.gpr 21#5) = meG.name.cap ∧
          s3.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 ∧
          s3.readReg64 (.gpr 28#5) = meG.name.ptr) ∧
        (P3 ⊢ emp)) := by
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.refl _⟩
      r3a_close_post)
  refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_frame_seq_vm_codeOk hs.inv (Entails.of_eq (by rw [emp_sepConj])) hstep
    fun s3 hvm3 hinv3 hpc3 hrun3
      ⟨hsp3, hfp3, hv3, htr3, hfs3, hlr3, hx0_3, hx19_3, hx20_3, hx21_3, hx26_3, hx28_3⟩ => ?_
  have hal3 : s3.spAligned = true := r1c_spAligned hs.spAligned hsp3
  rw [emp_sepConj, ← A.pool_transport lim st s s3 hvm3]
  have hdsm_ok := dropSignalMessage_placed_ok (callerProg := runProgPlaced H) (i := 579) hh sub h32 hsub64
  let dropKeep : SepProp := storesAt A.repAlloc g.stores g' ∗
    decResAt A.repAlloc (fsp + 0x320#64) res ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
    r3a_restFrame fsp ∗ callKeep ∗ anyHeap
  refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_call_lscro_codeOk (⟨fsp + 0x4d0#64, msgG, m⟩, st) hdsm_ok hinv3 hpc3 hrun3 hal3 hlr3
    (F := dropKeep) ?_
    (hnext := fun s4 hsteps4 hinv4 hpcm4 hrun4 hsp4 hcsm4 => ?_)
  · dsimp only [dropSignalMessageSpec]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (lsLogOff ∗ anyHeap) ∗
          (signalMessageAt A.repAlloc msgG (fsp + 0x4d0#64) m ∗
            A.pool lim st s3 ∗ stackAt fsp sub ∗ storesAt A.repAlloc g.stores g' ∗
            decResAt A.repAlloc (fsp + 0x320#64) res ∗
            protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
            protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
            r3a_restFrame fsp ∗ callKeep) by dsimp +zetaDelta only; sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (entails_anyHeap _)) ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0_3, by rw [hlr3]; simp (config := { decide := true }) only [wp_norm, arm64_norm, runPcPlaced_eq]⟩
      (Entails.of_eq (by rw [hsp3]; dsimp +zetaDelta only; sep_ac_rfl))
  · dsimp only [dropSignalMessageSpec]
    rw [sepExists_sepConj_left]
    refine r1c_sepWPp_exists_left fun evs_dsm => ?_
    simp only [sepConj_assoc]
    refine r1c_sepWPp_pure_left fun ⟨htr4, hfree_dsm⟩ => ?_
    have hcs4 := r3a_cs_regs hcsm4; rw [hsp3]
    have hin4 : InRunPlaced CodeOk s0 s4 3476 :=
      ⟨hpcm4, hrun4, hsp4.trans hsp3, hcs4.2.2.2.2.2.1.trans hfp3, hinv4,
        hcs4.2.2.2.2.2.2.trans hv3, hs.spAligned⟩
    have hx19_4 := hcs4.1.trans hx19_3; have hx20_4 := hcs4.2.1.trans hx20_3
    have hx21_4 := hcs4.2.2.1.trans hx21_3; have hx26_4 := hcs4.2.2.2.1.trans hx26_3
    have hx28_4 := hcs4.2.2.2.2.1.trans hx28_3
    have htr4_tot : s0.trace <+: s4.trace := (htr4.trans htr3) ▸ htr2_tot
    have hhist4 : RunHistOk g.i s0 s4 :=
      r3a_hist_step hh hsteps4 htr4 (r3a_hist_eq htr3 (congrArg FsState.files hfs3) hhist2)
    let st4 := M.stepEvents evs_dsm st
    cases res with
    | ok out =>
      obtain ⟨hans_ok, hwr⟩ := r3a_slotOut_ok hslot2
      have hans4 : g.a = some (some (namedWrites g'.writes, out)) := by
        rw [hga, hans_ok]; rfl
      have henv4 : ∀ evs_rem, FreeOnlyEvs evs_rem →
          EnvJoin g' out (M.stepEvents evs_rem st4) := by
        intro evs_rem hf_rem
        rw [← M.stepEvents_append]
        exact henv_join out rfl (evs_dsm ++ evs_rem) (r3a_freeOnly_append hfree_dsm hf_rem)
      exact r1c_sepWPp_weaken_pre
        (Entails.of_eq (by dsimp +zetaDelta only; rw [decResAt_ok]; sep_ac_rfl))
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_accept_tail_codeOk (g' := g') (peerG := peerG) (meG := meG) (out := out)
          hh hext hsub64 hin4 hx19_4 hx20_4 hx21_4 hx28_4 htr4_tot hhist4 hans4 hwr henv4 hjoin)
    | error err =>
      obtain ⟨herr, hans_err⟩ := r3a_slotOut_err hga hslot2
      have henv4 : ∀ evs_rem, FreeOnlyEvs evs_rem →
          EnvRej g' .postDispatch (M.stepEvents evs_rem st4) := by
        intro evs_rem hf_rem
        rw [← M.stepEvents_append]
        exact henv_rej (evs_dsm ++ evs_rem) (r3a_freeOnly_append hfree_dsm hf_rem)
      exact r1c_sepWPp_weaken_pre
        (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
        (r3a_after_decrypt_err_codeOk (g' := g') (peerG := peerG) (meG := meG)
          hh hdrop hext h32 hsub64 hin4 herr hx19_4 hx20_4 hx21_4 hx26_4 hx28_4
          htr4_tot hhist4 hans_err henv4 hrej)

/-! ## 6. `CodeOk`-Parametric `wrap_decrypt_signal` Call and Entry Paths -/

set_option maxHeartbeats 1600000 in
private theorem r3a_after_try_ok_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {EnvRej : StoresGhost → RejectKind → M.σ → Prop}
    {EnvJoin : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : CryptoVerification.SignalSession.Cli.RunSkeleton.RunSlots}
    {g : RunCall} {peerG meG : AddrGhost} {msgG : SignalMessageGhost} {m : SignalMessage}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B slots)
    (hslot_eq : slots.decryptSignal =
      CryptoVerification.SignalSession.Cli.RunCompose.mkSlot
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decSigSlotSpecPlacedOf
          CodeOk A lim sEnvs.decryptSignal S)
        needs.decryptSignal)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hrf : runFrame ≤ resStack)
    (hdec : needs.decryptSignal ≤ resStack - runFrame)
    (hsub63 : resStack - runFrame ≤ 2 ^ 63)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hspb : resStack ≤ s0.sp.toNat)
    (h32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext : extHookStack ≤ resStack - runFrame)
    (hs : InRunPlaced CodeOk s0 s 2032)
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
    refine r3a_sepWP_seq_vm hstep1 fun s1a _ hpc1a hrun1a
      ⟨hsp1a, hfp1a, hv1a, htr1a, hfs1a, hx8_1a, hx9_1a, hv0_1a, hv1_1a, hv2_1a,
        hx19_1a, hx20_1a, hx21_1a, hx26_1a, hx28_1a⟩ => ?_
    refine r3a_sepWP_seq_vm (mid := (blkPl_579).base + 3380#64) (P' := P_after) (post1 := midPost2)
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
    refine r3a_sepWP_seq_vm (mid := (blkPl_579).base + 3396#64) (P' := P_after) (post1 := midPost3)
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
    refine r3a_sepWP_seq_vm (mid := (blkPl_579).base + 3404#64) (P' := P_after) (post1 := midPost4)
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
  refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_frame_seq_vm_codeOk hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1
      ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1,
        hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx8_1,
        hx19_1, hx20_1, hx21_1, hx26_1, hx28_1⟩ => ?_
  have hal1 : s1.spAligned = true := r1c_spAligned hs.spAligned hsp1
  dsimp only [preF]
  rw [← A.pool_transport lim st s s1 hvm1]
  have htr_s1 : s0.trace <+: s1.trace := htr1 ▸ htr
  have hdec_ok : subroutine_ok (runProgPlaced H) (lsmpl.base 463)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decSigSlotSpecPlacedOf
        CodeOk A lim sEnvs.decryptSignal S sub) := by
    have hdec' : slots.decryptSignal.need ≤ sub := by rw [hslot_eq]; exact hdec
    have h := hc.decryptSignal sub hdec' hsub63
    rwa [hslot_eq] at h
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
  refine r3a_call_codeOk (decCtx, st) hdec_ok hinv1 hpc1 hrun1 hal1 hlr1
    (F := r3a_restFrame fsp ∗ callKeep) ?_
    (hpanic := fun sf _ _ hp => by
      dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decSigSlotSpecBasePlaced, decCtx, r3aDecSigGhost] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hpanic sf _ (Or.inl (by rw [hga, hp.1]; rfl)))
    (hnext := fun s2 _ hinv2 hpcm2 hrun2 hsp2 hcsm2 => ?_)
  · dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decSigSlotSpecBasePlaced, slotFramePlaced,
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
    dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decSigSlotSpecBasePlaced, decCtx, r3aDecSigGhost]
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
      (r3a_after_decrypt_drop_codeOk (g' := g') (peerG := peerG) (meG := meG) (msgG := msgG) (m := m)
        hh hdrop h32 hext hsub64 hin2
        (hcs2.1.trans hx19_1) (hcs2.2.1.trans hx20_1) (hcs2.2.2.1.trans hx21_1)
        (hcs2.2.2.2.1.trans hx26_1) (hcs2.2.2.2.2.1.trans hx28_1)
        htr_s1 hga hslot2 htr2_tot hhist2 henv_rej2 henv_join2 hrej hjoin)


set_option maxHeartbeats 1600000 in
private theorem r3a_recvW_none_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {sEnvs : RunSlotEnvs}
    {EnvRej : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {peerV : AddrV} {rest : Bytes} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (he : AtRunEntryPlaced CodeOk S g s0)
    (hd : AtDispatchPlaced CodeOk g .none s0 s)
    (hcall : g.c = .recv peerV)
    (hstdin : g.i.stdin = 2#8 :: rest)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvRej StoresGhost.opened .postDispatch (M.stepEvents evs st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvRej g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g .none s0 s resStack)
      Q Qp (fun _ => ⌜False⌝) := by
  obtain ⟨_, _, hsub64, _, _, hext, _⟩ := r3a_bounds hres hres64
  let fsp := runFsp s0; let sub := resStack - runFrame
  have hs : InRunPlaced CodeOk s0 s 532 := hd.base
  have hpc : s.pc = runPcPlaced 532 := hs.pc
  change s.pc = (blkPl_579).base + 532#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa only [hcall, CallV.tag] using hd.x8
  have hx19 := hd.x19; have hx20 := hd.x20; have hx23 := hd.x23; have hx25 := hd.x25
  have hinp_eq : inputOf g.i g.c = 2#8 :: rest := by rw [hcall]; exact hstdin
  have hinp_merge : (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) = (g.inp ↦ₛ inputOf g.i g.c) := by
    rw [hinp_eq, pointsToBytes_cons]
  have hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (rest.length + 1) := by
    rw [hd.x24, hinp_eq]; rfl
  have hrest32 : rest.length < 2 ^ 32 := by
    simpa [hstdin] using he.rel.2.1.2.2.1 peerV (hcall ▸ he.parse)
  have hnz24 : (BitVec.ofNat 64 (rest.length + 1) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; bv_omega
  have hans0 : g.a = some none := hd.reject_of_me_none he
  have hx21 : s.readReg64 (.gpr 21#5) = -1#64 := hd.meRegs
  have hhist0 : RunHistOk g.i s0 s := ⟨hd.fs, hd.stdout⟩
  have hres_split := r3a_res_split g.res
  let noneTail : SepProp := memRegion (g.res + 8#64) (runResSize - 8) ∗
    storesAt A.repAlloc g.stores StoresGhost.opened ∗
    ((g.inp + 1#64) ↦ₛ rest) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗
    memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗
    r3a_restFrame fsp ∗ stackAt fsp sub ∗ A.pool lim st s
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ w : CallW, ⌜w.w4.setWidth 8 = peerV.device⌝ ∗
        r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
        ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name) ∗
      ((∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗
        memRegion (fsp + 0x220#64) 32 ∗ (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap)) ?_ ?_
  · dsimp +zetaDelta only [dispatchMemPlaced,
      CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced,
      dispatchMeHeap, dispatchCells]
    simp only [RustCliAllocBudget.atState_pool, callAt_atState, r3a_storesAt_atState]
    rw [hinp_eq, pointsToBytes_cons, hcall, hres_split, emp_sepConj,
      r3a_locals_empty_rest (runFsp s0)]
    refine Entails.trans
      (Entails.of_eq (show _ =
        callAt A.repAlloc g.call (.recv peerV) ∗
        (coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff) ∗
        ((∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗ memRegion (runFsp s0 + 0x220#64) 32 ∗
          (g.inp ↦₈ 2#8) ∗
          (memRegion (g.res + 8#64) (runResSize - 8) ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗
            ((g.inp + 1#64) ↦ₛ rest) ∗ runSaved s0 ∗
            memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x260#64) 32 ∗
            memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗
            r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
            A.pool lim st s)) by sep_ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono (r3a_callRecv_open A.repAlloc g.call peerV)
        (sepConj_mono_left (entails_anyHeap _)))
      (Entails.of_eq (by sep_ac_rfl))
  refine r3a_sepWPp_exists_left fun w => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine r1c_sepWPp_pure_left fun hw4 => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗
      (memRegion (fsp + 0x220#64) 32 ∗
        r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
        ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗
        (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap))
    (Entails.of_eq (by (try dsimp +zetaDelta only); try sep_ac_rfl))
    (r3a_sepWPp_exists_left fun w_res => ?_)
  refine r3a_sepWPp_bind (A0 := memRegion (fsp + 0x220#64) 32)
    (F := (g.res ↦₆₄ w_res) ∗
      r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗
      (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap) ?_ |>
    r1c_sepWPp_weaken_pre (Entails.of_eq (by (try dsimp +zetaDelta only); try sep_ac_rfl))
  intro R hm
  obtain ⟨ws220, hlen220, hm⟩ := r3a_memRegion_words 4 (fsp + 0x220#64) (by decide) hm
  rcases ws220 with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen220; done)
  refine ⟨r3a_words64At (fsp + 0x220#64) [p0, p1, p2, p3], hm, ?_⟩
  let P_step : SepProp :=
    (g.res ↦₆₄ w_res) ∗
      r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      r3a_words64At (s.sp + 0x220#64) [p0, p1, p2, p3] ∗ (g.inp ↦₈ 2#8)
  let P_after : SepProp :=
    (g.res ↦₆₄ 0xffffffffffffffff#64) ∗
      r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      r3a_words64At (s.sp + 0x220#64) [w.w1, w.w2, w.w3, w.w4] ∗ (g.inp ↦₈ 2#8)
  have hstep : SepWP (runProgPlaced H) (runPcPlaced 4104) s P_step
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores) ∧
        (P1 ⊢ P_after)) := by
    rw [runPcPlaced_eq]
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after, r3a_words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hP_in :
      r3a_words64At (fsp + 0x220#64) [p0, p1, p2, p3] ∗
        ((g.res ↦₆₄ w_res) ∗
          r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
          ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗
          (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap) ⊢
      P_step ∗ (ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗ noneTail ∗ anyHeap) := by
    dsimp +zetaDelta only [P_step]; rw [hs.sp]; exact Entails.of_eq (by sep_ac_rfl)
  refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_frame_seq_vm_codeOk hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
  dsimp only [noneTail]
  rw [← A.pool_transport lim st s s1 hvm1]
  refine r1c_sepWPp_weaken_pre ?_
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_tail_peer_reject_codeOk (g' := StoresGhost.opened)
      (peerG := ⟨⟨w.w1, w.w2, peerV.name⟩, peerV.device⟩)
      hh hext hsub64 ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
      hx19_1 (htr1 ▸ hd.trace) (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist0)
      hans0 henv hrej)
  dsimp +zetaDelta only [P_after]; rw [hs.sp]
  have hpeer := r3a_pack_peer A.repAlloc (fsp + 0x220#64) peerV w.w1 w.w2 w.w3 w.w4 hw4
  have hcall56 := r3a_words_to_memRegion [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] g.call 56
  dsimp +zetaDelta only [runResAt] at hpeer hcall56 ⊢; rw [← hinp_merge]
  exact Entails.trans (Entails.of_eq (by (try dsimp +zetaDelta only); try sep_ac_rfl))
    (Entails.trans
      (sepConj_mono hpeer (sepConj_mono hcall56
        (Entails.refl ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦₈ 2#8) ∗
          ((g.inp + 1#64) ↦ₛ rest) ∗ runSaved s0 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x260#64) 32 ∗
          memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗
          r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim st s1 ∗ anyHeap))))
      (Entails.of_eq (by (try dsimp +zetaDelta only); try sep_ac_rfl)))

set_option maxHeartbeats 1600000 in
private theorem r3a_recvW_some_codeOk [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {RecvWEnv : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : CryptoVerification.SignalSession.Cli.RunSkeleton.RunSlots}
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
    (hc : RunCalleesPlaced A lim cEnvs H B slots)
    (hslot_eq : slots.decryptSignal =
      CryptoVerification.SignalSession.Cli.RunCompose.mkSlot
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decSigSlotSpecPlacedOf
          CodeOk A lim sEnvs.decryptSignal S)
        needs.decryptSignal)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hspb : resStack ≤ s0.sp.toNat)
    (he : AtRunEntryPlaced CodeOk S g s0)
    (hd : AtDispatchPlaced CodeOk g (.some meV meG) s0 s)
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
  have htry := r3a_sigTryFrom_ok hh
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
  refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_frame_seq_vm_codeOk hs.inv hP_in hstep
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
      exact r3a_some_pre_try A.repAlloc (A.pool lim st s1) g peerV rest s0 resStack meV meG w u1
        hme_bytes hsm hsub64
        (r3a_words_to_memRegion [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] g.call 56)
        (r3a_pack_peer A.repAlloc (runFsp s0 + 0x220#64) peerV w.w1 w.w2 w.w3 w.w4 hw4)
        hme_close
        (r3a_rejoin_1d0 (runFsp s0) (BitVec.ofNat 64 meG.name.bytes.length) u1)) ?_
  have hfit_try : FitsEnv M lim st (TryFromEnv ⟨g.inp + 1#64, rest, fsp + 0x4d0#64⟩) :=
    fun evs hevs => hfit evs (h_try_fit evs (tryFromEnv_iff_bytes.mp hevs))
  refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux.r3a_call_lscro_codeOk (⟨g.inp + 1#64, rest, fsp + 0x4d0#64⟩, st) htry hinv1 hpc1 hrun1 hal1 hlr1
    (F := memRegion (fsp - BitVec.ofNat 64 sub) (sub - smallRootStack) ∗ tryKeep) ?_
    (hnext := fun s2 hsteps2 hinv2 hpcm2 hrun2 hsp2 hcsm2 => ?_)
  · dsimp only [tryFromPlacedSpec, tryFromPlacedSpecGen]; rw [hlog]; simp only [sepConj_assoc]
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
    dsimp only [tryFromPlacedSpec, tryFromPlacedSpecGen]; rw [hlog]; simp only [sepConj_assoc]
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
        (r3a_recvW_try_err_codeOk (peerG := peerG) (meG := meG) (e := e)
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
    · dsimp only [signalMessageResultAt]
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
        exact ((LibsignalBinary.Heap.fitsEvents_append M lim evs_try evs_dec st).mp htot).2
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
        (r3a_after_try_ok_codeOk (peerG := peerG) (meG := meG) (msgG := msgG) (m := m)
          hh hc hslot_eq hdrop hrf hdec hsub63 hsub64 hspb h32 hext hin2
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


theorem run_hop_recvW_of_codeOk_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : CryptoVerification.SignalSession.Cli.RunSkeleton.RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A lim sEnvs S needs))
    (hslot_eq : slots.decryptSignal =
      CryptoVerification.SignalSession.Cli.RunCompose.mkSlot
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decSigSlotSpecPlacedOf
          CodeOk A lim sEnvs.decryptSignal S)
        needs.decryptSignal)
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) := by
      intros; rfl) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aPlacedBudget.RunHopRecvWPlacedOf
      CodeOk A lim cEnvs (R3aRecvWEnv sEnvs) H B S slots resStack := by
  intro g st s0 s me peerV rest Q Qp hh hc hdrop hres hres64 hspb he hd hcall hstdin hfit
    hpanic hrej hjoin
  rw [hneed_eq] at hres
  cases me with
  | none =>
    exact r3a_recvW_none_codeOk hh hres hres64 he hd hcall hstdin
      (fun evs hf => ⟨evs, hf, rfl⟩) hrej
  | some meV meG =>
    exact r3a_recvW_some_codeOk
      (fun _ ht => SeqEnv.inl ht)
      (fun _ hm _ _ ht hf => by
        dsimp only [R3aRecvWEnv]; rw [hm]
        exact SeqEnv.append ht hf)
      (fun w msgG m hm _ _ ht hd_ev => by
        dsimp only [R3aRecvWEnv]; rw [hm]; rw [hdec_ghost] at hd_ev
        exact SeqEnv.append ht (SeqEnv.inl hd_ev))
      (fun w msgG m hm _ _ _ ht hd_ev hf => by
        dsimp only [R3aRecvWEnv]; rw [hm]; rw [hdec_ghost] at hd_ev
        exact SeqEnv.append ht (SeqEnv.append hd_ev hf))
      hh hc hslot_eq hdrop hres hres64 hspb he hd hcall hstdin hfit hpanic hrej hjoin

/-- `LibsignalFrozen lsmpl` specialization of `run_hop_recvW_of_codeOk_placed_ok` at
`slotsOfSigPkFrozenPlaced`. -/
theorem run_hop_recvW_frozen_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) := by
      intros; rfl) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aPlacedBudget.RunHopRecvWPlacedOf
      (CryptoVerification.LibsignalFrozen lsmpl)
      A lim cEnvs (R3aRecvWEnv sEnvs) H B S
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim sEnvs S needs)
      resStack :=
  run_hop_recvW_of_codeOk_placed_ok
    (CodeOk := CryptoVerification.LibsignalFrozen lsmpl)
    (slots := LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
      A lim sEnvs S needs)
    (sEnvs := sEnvs) (needs := needs) rfl rfl hdec_ghost

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
