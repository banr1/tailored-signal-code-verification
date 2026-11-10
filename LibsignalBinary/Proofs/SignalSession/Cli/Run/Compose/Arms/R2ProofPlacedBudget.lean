/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2OkArmsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Frame
import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonCalleesExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.Disproof.Basic

/-!
# Budget-Threaded `signal_session::run` Placed Send Arm

Defines the `Send`-arm allocation-event envelope `R2SendEnv` and proves
`run_hop_send_placed_ok_of_env` and `run_hop_send_placed_ok` (`RunHopSendPlaced`) on Block `579`
(`runProgPlaced H`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open scoped LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2StepsPlacedBudget
open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi
  (ApiError CiphertextMessage PreKeySignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr
  (AddrVal PreKeyMsgGhost apiEncResultAt ctSignalTag preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SignalMessageGhost protocolAddressAt signalMessageAt)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession.Cli
  (StoresGhost cliIdentityVtSym cliSessionVtSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallW RunCall callAt cliWrOk coinsInstalledPlaced coinsOf inputOf namedWrites
   runResAt runResSize sepWPp_weaken_pre storesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_555 blkPl_598)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtRunEntryPlaced Bytes EncGhost InRunPlaced MeAtDispatch PanicK
   RejectKind RunHistOk RunNeeds RunSem addrNameHeap addrUpperAt
   addrUpperAt_entails_memRegion addrValOf dispatchCells dispatchMeHeap encResAt
   encResAt_ok idVtPlaced nowCellAt protocolAddressAt_eq_parts r2_addrNameHeap_cap_lt
   r2_addrUpperAt_reloc r2_ans_of_trace_eq r2_boxLive r2_boxLive_to_sliceDeallocX
   r2_callAt_send_unpack r2_callWords_to_memRegion56 r2_csm_trans r2_hold r2_hold_eq
   r2_localGaps r2_locals_none_eq r2_locals_some_eq r2_memRegion248_open
   r2_memRegion32_words4 r2_now_open r2_now_to_mem16 r2_open_preKeyMessage
   r2_open_signalMessage r2_peerWords_pack r2_protocolAddress_to_mem32_heap r2_res_open
   r2_res_write_none r2_tag8_close r2_tag8_open r2_words31 r2_words31_to_memRegion248
   r2_words4_216_rejoin r2p_CodeOk r2p_cs_regs r2p_histOk_of_slotTrace
   r2p_histOk_of_trace_files r2p_inRun_mk r2p_vregs_0 r2p_vregs_1 r2p_vregs_2 runFiles
   runFsp runLocals runPcPlaced runPcPlaced_eq runProgPlaced runSaved sessVtPlaced
   slotOut slotTrace unixEpoch)
open CryptoVerification.SignalSession.Cli.RunProofs
  (DropPreKeyMsgGhost slotOut_err_ne_store)
open CryptoVerification.SignalSession.Cli.RunProofs.DropPreKeyMsgHelpers
  (optSliceDeallocX sliceDeallocX)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame runNeed)
open CryptoVerification.SpqrV1.ChainProofs (SliceConcat2Ghost bytesAt bytesAt_false)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget SeqEnv VmPreserved fitsEvents_append)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2OkArmsPlacedBudget
  (r2pb_pk_arm r2pb_sig_arm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2PlacedBudget
  (RunHopSendPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudgetAux
  (r2pb_err_arm r2pb_sig_free_ad r2pb_sig_free_ct r2pb_sig_free_pq r2pb_sig_free_ser
   r2pb_step_chk_copy_pk r2pb_step_chk_copy_sig)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2StepsPlacedBudget
  (r2pbFreeMePeerEvs r2pbFreeMePeerEvs_freeOnly r2pbFreeOptSliceEvs r2pbFreePeerEvs
   r2pbFreePeerEvs_freeOnly r2pbFreeSliceEvs r2pbSigFree3Evs r2pbSigFreeEvs
   r2pbSigFreeEvs_freeOnly r2pb_call r2pb_files_of_trace_eq r2pb_freeOnlyEvs_of_forall
   r2pb_free_me_peer_join r2pb_free_peer_reject r2pb_peel_pure_tc r2pb_peel_tc
   r2pb_sepWPp_exists_left r2pb_seq_lscro_oom r2pb_stOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlacedEnv RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs encSlotSpecPlaced slotFramePlaced slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (dispatchMemPlaced runNeed_bounds_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget
  (cliConcat2Events cliConcat2Spec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2PlacedBudget
  (cliConcat2SpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgBudget
  (dropPreKeyMsgSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgPlacedBudget
  (dropPreKeyMsgSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced concat_placed_ok dropPreKeyMsg_placed_ok)

private theorem storesAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    storesAt (A.atState lim st s) = storesAt A.repAlloc := rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff r2_hold
  tokenInitPlacedAt coinsInstalledPlaced storesAt r2_localGaps
attribute [local arm64_norm, local wp_norm]
  ProofLib.bv_sub_add_lit BitVec.toNat_zero r2p_vregs_0 r2p_vregs_1 r2p_vregs_2

/-! ## 1. Arm `R2` Envelope (`R2SendEnv`) & `run_hop_send_placed_ok` (`R+0x214` → Join/Reject) -/

private theorem r2pb_seq_step [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s s_nomem : State} {P P_end : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : r2p_CodeOk s.mem)
    (hstep : SepWP prog mid s P
      (fun sm Pm => VmPreserved s sm ∧ (∃ m_end, sm = s_nomem.setMem m_end) ∧ Pm = P_end) oom)
    (hcont : ∀ m_end, VmPreserved s (s_nomem.setMem m_end) →
      r2p_CodeOk (s_nomem.setMem m_end).mem →
      SepWPp prog ret (s_nomem.setMem m_end) P_end Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  refine r2pb_seq_lscro_oom (mid := mid) hcrl ?_
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hPm, hvm, ⟨m_end, rfl⟩, rfl⟩ | h_oom⟩ :=
    SepWP.to_reaches_pc hstep hm hL
  · exact ⟨_, hsteps, Or.inl ⟨hpc, hrun, _, hPm, fun hinv => hcont m_end hvm hinv⟩⟩
  · exact ⟨sm, hsteps, Or.inr h_oom⟩

/-- Canonical frame-address-erased peer `AddrGhost` with `.val = addrValOf peerV`. -/
def r2PeerGhost0 (peerV : AddrV) : AddrGhost :=
  ⟨⟨0#64, 0#64, peerV.name⟩, peerV.device⟩

theorem r2PeerGhost0_val (peerV : AddrV) : (r2PeerGhost0 peerV).val = addrValOf peerV := rfl

/-- `EncGhost` passed to `sEnvs.encrypt` at `signal_session::run` frame stack pointer `fsp`. -/
def r2EncGhost (g : RunCall) (peerG meG : AddrGhost) (fsp : BitVec 64) : EncGhost where
  peer := peerG
  peerA := fsp + 0x320#64
  me := meG
  meA := fsp + 0x23b0#64
  stores := g.stores
  ret := fsp + 0x4d0#64
  coinsP := g.coins
  F := runFiles g.i
  coins := coinsOf g.i
  ptA := g.inp
  ptext := g.i.stdin

/-- Tail allocation-event envelope of Arm `R2` after `wrap_encrypt` returns:
either `FreeOnlyEvs` (`.error _` drop + address frees) or `cliConcat2Events` on the
prepend-tagged serialized ciphertext followed by `FreeOnlyEvs` (message drop + address frees). -/
def R2TailEnv (S : RunSem) (g : RunCall) (meV peerV : AddrV)
    (evs_tail : List AllocEvent) : Prop :=
  FreeOnlyEvs evs_tail ∨
    match S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV) g.i.stdin (coinsOf g.i) with
    | some (some (_, .signalMessage m)) =>
        evs_tail = cliConcat2Events [2#8] m.serialized ∨
          ∃ evs_f : List AllocEvent, FreeOnlyEvs evs_f ∧
            evs_tail = cliConcat2Events [2#8] m.serialized ++ evs_f
    | some (some (_, .preKeySignalMessage m)) =>
        evs_tail = cliConcat2Events [3#8] m.serialized ∨
          ∃ evs_f : List AllocEvent, FreeOnlyEvs evs_f ∧
            evs_tail = cliConcat2Events [3#8] m.serialized ++ evs_f
    | _ => False

/-- Allocation-event envelope for Arm `R2` (`Send`): `FreeOnlyEvs` when `me = .none`, else
`SeqEnv` of `sEnvs.encrypt` and `R2TailEnv`. -/
def R2SendEnv (sEnvs : RunSlotEnvs) (S : RunSem)
    (g : RunCall) (me : MeAtDispatch) (peerV : AddrV)
    (evs : List AllocEvent) : Prop :=
  match me with
  | .none => FreeOnlyEvs evs
  | .some meV meG =>
      SeqEnv (sEnvs.encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64))
        (R2TailEnv S g meV peerV)
        evs

set_option maxHeartbeats 1600000 in
/-- Budget-threaded Arm `R2` hop proof (`R+0x214` → Join/Reject) on Block `579` (`runProgPlaced H`),
parameterized over any `SendEnv` closed under `me = .none` peer free, `sEnvs.encrypt`, `.error`
free-only tail, and `.signalMessage` / `.preKeySignalMessage` `cliConcat2Events` + free-only tails. -/
theorem run_hop_send_placed_ok_of_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {SendEnv : RunCall → MeAtDispatch → AddrV → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (h_none : ∀ g peerV peerG,
      SendEnv g .none peerV (r2pbFreePeerEvs peerG))
    (h_pre : ∀ g meV meG peerV peerG fsp evs,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) evs →
      SendEnv g (.some meV meG) peerV evs)
    (h_err : ∀ g meV meG peerV peerG fsp evs_enc evs_f,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) evs_enc →
      FreeOnlyEvs evs_f →
      SendEnv g (.some meV meG) peerV (evs_enc ++ evs_f))
    (h_sig_cat : ∀ g meV meG peerV peerG fsp evs_enc g' m,
      peerG.val = addrValOf peerV →
      S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV) g.i.stdin (coinsOf g.i) =
        some (some (g', .signalMessage m)) →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) evs_enc →
      SendEnv g (.some meV meG) peerV (evs_enc ++ cliConcat2Events [2#8] m.serialized))
    (h_sig_ok : ∀ g meV meG peerV peerG fsp evs_enc g' m evs_f,
      peerG.val = addrValOf peerV →
      S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV) g.i.stdin (coinsOf g.i) =
        some (some (g', .signalMessage m)) →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) evs_enc →
      FreeOnlyEvs evs_f →
      SendEnv g (.some meV meG) peerV
        (evs_enc ++ (cliConcat2Events [2#8] m.serialized ++ evs_f)))
    (h_pk_cat : ∀ g meV meG peerV peerG fsp evs_enc g' m,
      peerG.val = addrValOf peerV →
      S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV) g.i.stdin (coinsOf g.i) =
        some (some (g', .preKeySignalMessage m)) →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) evs_enc →
      SendEnv g (.some meV meG) peerV (evs_enc ++ cliConcat2Events [3#8] m.serialized))
    (h_pk_ok : ∀ g meV meG peerV peerG fsp evs_enc g' m evs_f,
      peerG.val = addrValOf peerV →
      S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV) g.i.stdin (coinsOf g.i) =
        some (some (g', .preKeySignalMessage m)) →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) evs_enc →
      FreeOnlyEvs evs_f →
      SendEnv g (.some meV meG) peerV
        (evs_enc ++ (cliConcat2Events [3#8] m.serialized ++ evs_f))) :
    RunHopSendPlaced (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs sEnvs SendEnv H B S needs resStack := by
  intro g st s0 s me peerV Q Qp hh hc hdrop hres hres64 _hspb he hd hcall hfits hpanic hrej hjoin
  obtain ⟨hframeLe, hsub63, hsub64, _, _, _, _, _, _, _, _, _, _, _,
      hdropNeed, hcatNeed, hextNeed, hencNeed, _, _, _, hdpkNeed⟩ :=
    runNeed_bounds_placed hres hres64
  let fsp := runFsp s0
  have hfsp_def : runFsp s0 = fsp := rfl
  have hpc : s.pc = runPcPlaced 532 := hd.base.pc; change s.pc = (blkPl_579).base + 532#64 at hpc
  have hrun0 : s.status = .Running := hd.base.run
  have hsp_al : s.spAligned = true := hd.base.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 2#64 := by rw [hd.x8, hcall]; rfl
  have hx25 : s.readReg64 (.gpr 25#5) = g.call := hd.x25
  have hd_gt : ConditionHolds .GT (subsPState64 2#64 1#64) = true := by r2pb_cond
  have hd_le : ConditionHolds .LE (subsPState64 2#64 1#64) = false := by r2pb_cond
  have hs_ne : ConditionHolds .NE (subsPState64 2#64 2#64) = false := by r2pb_cond
  have hs_eq : ConditionHolds .EQ (subsPState64 2#64 2#64) = true := by r2pb_cond
  have hhist0 : RunHistOk g.i s0 s := ⟨hd.fs, hd.stdout⟩
  refine sepWPp_weaken_pre
    (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
      (sepConj_mono_right (entails_anyHeap emp))) ?_
  cases me with
  | none =>
    have hans_none : g.a = some none := hd.reject_of_me_none he
    have hx20 : s.readReg64 (.gpr 20#5) = g.res := hd.x20
    have hx21_none : s.readReg64 (.gpr 21#5) = 0xffffffffffffffff#64 := hd.meRegs
    have hmn_eq : ConditionHolds .EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by r2pb_cond
    have hmn_ne : ConditionHolds .NE (addsPState64 0xffffffffffffffff#64 1#64) = false := by r2pb_cond
    dsimp only [dispatchMemPlaced,
      CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced,
      dispatchMeHeap, dispatchCells]
    rw [storesAt_atState]
    change SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((memRegion g.res runResSize ∗ callAt A.repAlloc g.call g.c ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗
        tokenInitPlacedAt ∗ lsLogOff ∗ emp ∗ runSaved s0 ∗
        runLocals (runFsp s0) [] ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s) ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝)
    rw [hfsp_def, hcall, emp_sepConj, r2_locals_none_eq fsp]
    have hopen_none :
        (memRegion g.res runResSize ∗ callAt A.repAlloc g.call (.send peerV) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗
          tokenInitPlacedAt ∗ lsLogOff ∗ runSaved s0 ∗
          (memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) ∗ anyHeap ⊢
        (∃∗ r0 : BitVec 64, (g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
        (∃∗ peerG : AddrGhost, ∃∗ cw : CallW,
          ⌜peerG.val = addrValOf peerV ∧ peerG.name.cap = cw.w1 ∧ peerG.name.ptr = cw.w2 ∧
            cw.w3 = BitVec.ofNat 64 peerG.name.bytes.length ∧ cw.w4.setWidth 8 = peerG.device⌝ ∗
          ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
            ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
            ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
          addrNameHeap A.repAlloc peerG) ∗
        (∃∗ p0 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p2 : BitVec 64, ∃∗ p3 : BitVec 64,
          ((fsp + 0x320#64) ↦₆₄ p0) ∗ (((fsp + 0x320#64) + 8#64) ↦₆₄ p1) ∗
          (((fsp + 0x320#64) + 16#64) ↦₆₄ p2) ∗ (((fsp + 0x320#64) + 24#64) ↦₆₄ p3)) ∗
        (storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗
          tokenInitPlacedAt ∗ lsLogOff ∗ runSaved s0 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
          memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗
          memRegion (fsp + 0x1750#64) 248 ∗ memRegion (fsp + 0x23b0#64) 32 ∗
          r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) := by
      refine Entails.trans (Entails.of_eq (Q :=
          memRegion g.res runResSize ∗ callAt A.repAlloc g.call (.send peerV) ∗
            memRegion (fsp + 0x320#64) 32 ∗
            (storesAt A.repAlloc g.stores StoresGhost.opened ∗
              (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗
              tokenInitPlacedAt ∗ lsLogOff ∗ runSaved s0 ∗
              memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
              memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗
              memRegion (fsp + 0x1750#64) 248 ∗ memRegion (fsp + 0x23b0#64) 32 ∗
              r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗
              A.pool lim st s ∗ anyHeap)) (by sep_ac_rfl)) ?_
      exact sepConj_mono (r2_res_open g.res)
        (sepConj_mono (r2_callAt_send_unpack A.repAlloc g.call peerV)
          (sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x320#64))))
    refine sepWPp_weaken_pre hopen_none ?_
    apply r2pb_peel_tc; intro _r0; apply r2pb_peel_tc; intro peerG; apply r2pb_peel_tc; intro cw
    apply r2pb_peel_tc; intro _p0; apply r2pb_peel_tc; intro _p1
    apply r2pb_peel_tc; intro _p2; apply r2pb_peel_tc; intro _p3
    apply r2pb_peel_pure_tc; rintro ⟨_, hw1, hw2, _, _⟩
    simp only [emp_sepConj, sepConj_assoc]
    apply r2pb_seq_step (mid := runPcPlaced 2984) hd.base.inv
    · rw [← r2_hold_eq (memRegion (g.res + 8#64) (runResSize - 8)),
          ← r2_hold_eq (addrNameHeap A.repAlloc peerG),
          ← r2_hold_eq (storesAt A.repAlloc g.stores StoresGhost.opened ∗ _),
          runPcPlaced_eq]
      dsimp +zetaDelta only [fsp]; rw [← hd.base.sp]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ⟨hvm, ⟨_, rfl⟩, rfl⟩⟩
      )
    intro _m_none hvm1 hinv1
    change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
    rw [hd.base.sp, r2_hold_eq, r2_hold_eq, r2_hold_eq]
    have hin1 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv1) 2984 :=
      r2p_inRun_mk hd.base (by r2pb_pc_done)
        (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
        (by r2pb_eq) (by r2pb_eq) hinv1 (by r2pb_eq)
    have hp16 :
        ((fsp + 0x330#64) ↦₆₄ cw.w3) ∗ ((fsp + 0x338#64) ↦₆₄ cw.w4) ⊢
          memRegion (fsp + 0x330#64) 16 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x330#64) (n := 8) (k := 8)
            (b' := fsp + 0x338#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    let postNone : SepProp :=
      runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st (r2pb_stOf hinv1) ∗ anyHeap
    refine sepWPp_weaken_pre (P' := postNone) ?_ ?_
    · dsimp +zetaDelta only [postNone]; rw [hcall]
      have hres_n := r2_res_write_none A.repAlloc g.res 0xffffffffffffffff#64 rfl
      have hcw_m := r2_callWords_to_memRegion56 g.call cw
      have hpool_n : A.pool lim st s ⊢ A.pool lim st (r2pb_stOf hinv1) :=
        Entails.of_eq (A.pool_transport lim st s (r2pb_stOf hinv1) hvm1).symm
      refine Entails.trans (Entails.of_eq (Q :=
          (((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
            ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
              ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
              ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
            (((fsp + 0x330#64) ↦₆₄ cw.w3) ∗ ((fsp + 0x338#64) ↦₆₄ cw.w4)) ∗
            (coinsInstalledPlaced g.coins (coinsOf g.i) ∗
              tokenInitPlacedAt ∗ lsLogOff ∗ anyHeap) ∗
            A.pool lim st s ∗
            (storesAt A.repAlloc g.stores StoresGhost.opened ∗
              (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
              addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
              memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
              memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
              memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
              stackAt fsp (resStack - runFrame)))) ?_) ?_
      · rw [← hw1, ← hw2]; dsimp +zetaDelta only [fsp]; sep_ac_rfl
      · refine Entails.trans (sepConj_mono hres_n (sepConj_mono hcw_m (sepConj_mono hp16
          (sepConj_mono (entails_anyHeap _) (sepConj_mono_left hpool_n)))))
          (Entails.of_eq (by sep_ac_rfl))
    · exact r2pb_free_peer_reject (peerG := peerG) hh hextNeed hsub64 hin1
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x19)
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.trace)
        (r2p_histOk_of_trace_files hhist0 (by r2pb_eq) (by r2pb_eq))
        hans_none
        ⟨r2pbFreePeerEvs peerG, h_none g peerV peerG, rfl⟩
        hrej
  | some meV meG =>
    obtain ⟨hptLt, hcoinsLt, hfs0, hfilesOk, hencOk, hansLink⟩ := hd.send_facts he hcall
    rcases hd.meRegs with ⟨hx21, hx28, hme_bytes, _, hme_dev⟩
    have hme_val : meG.val = addrValOf meV := by
      unfold AddrGhost.val addrValOf; simp [hme_bytes, hme_dev]
    dsimp only [dispatchMemPlaced,
      CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced,
      dispatchMeHeap, dispatchCells]
    rw [storesAt_atState]
    change SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((memRegion g.res runResSize ∗ callAt A.repAlloc g.call g.c ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗
        tokenInitPlacedAt ∗ lsLogOff ∗ addrNameHeap A.repAlloc meG ∗ runSaved s0 ∗
        runLocals (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s) ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝)
    rw [hfsp_def, hcall, r2_locals_some_eq fsp]
    have hopen_some :
        (memRegion g.res runResSize ∗ callAt A.repAlloc g.call (.send peerV) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗
          tokenInitPlacedAt ∗ lsLogOff ∗
          addrNameHeap A.repAlloc meG ∗ runSaved s0 ∗
          (memRegion fsp 16 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion (fsp + 0x208#64) 24 ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) ∗ anyHeap ⊢
        (∃∗ peerG : AddrGhost, ∃∗ cw : CallW,
          ⌜peerG.val = addrValOf peerV ∧ peerG.name.cap = cw.w1 ∧ peerG.name.ptr = cw.w2 ∧
            cw.w3 = BitVec.ofNat 64 peerG.name.bytes.length ∧ cw.w4.setWidth 8 = peerG.device⌝ ∗
          ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
            ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
            ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
          addrNameHeap A.repAlloc peerG) ∗
        (⌜meG.name.cap.toNat < 2 ^ 63⌝ ∗ addrNameHeap A.repAlloc meG) ∗
        (∃∗ n0 : BitVec 64, ∃∗ n1 : BitVec 32,
          (fsp ↦₆₄ n0) ∗ ((fsp + 8#64) ↦₃₂ n1) ∗ memRegion (fsp + 12#64) 4) ∗
        (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
          ⌜∀ dst, (dst ↦₆₄ u0) ∗ ((dst + 8#64) ↦₆₄ u1) ⊢ addrUpperAt dst meG⌝ ∗
            ((fsp + 0x1d0#64) ↦₆₄ u0) ∗ (((fsp + 0x1d0#64) + 8#64) ↦₆₄ u1)) ∗
        (∃∗ p0 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p2 : BitVec 64, ∃∗ p3 : BitVec 64,
          ((fsp + 0x320#64) ↦₆₄ p0) ∗ (((fsp + 0x320#64) + 8#64) ↦₆₄ p1) ∗
          (((fsp + 0x320#64) + 16#64) ↦₆₄ p2) ∗ (((fsp + 0x320#64) + 24#64) ↦₆₄ p3)) ∗
        (∃∗ m0 : BitVec 64, ∃∗ m1 : BitVec 64, ∃∗ m2 : BitVec 64, ∃∗ m3 : BitVec 64,
          ((fsp + 0x23b0#64) ↦₆₄ m0) ∗ (((fsp + 0x23b0#64) + 8#64) ↦₆₄ m1) ∗
          (((fsp + 0x23b0#64) + 16#64) ↦₆₄ m2) ∗ (((fsp + 0x23b0#64) + 24#64) ↦₆₄ m3)) ∗
        (memRegion g.res runResSize ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
          (g.inp ↦ₛ g.i.stdin) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗
          tokenInitPlacedAt ∗ lsLogOff ∗ runSaved s0 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
          r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗
          A.pool lim st s ∗ anyHeap) := by
      have hinp : inputOf g.i (.send peerV) = g.i.stdin := rfl
      rw [hinp]
      refine Entails.trans (Entails.of_eq (Q :=
          callAt A.repAlloc g.call (.send peerV) ∗ addrNameHeap A.repAlloc meG ∗
            memRegion fsp 16 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗
            memRegion (fsp + 0x320#64) 32 ∗ memRegion (fsp + 0x23b0#64) 32 ∗
            (memRegion g.res runResSize ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
              (g.inp ↦ₛ g.i.stdin) ∗
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗
              tokenInitPlacedAt ∗ lsLogOff ∗ runSaved s0 ∗
              memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
              memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
              r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗
              A.pool lim st s ∗ anyHeap)) (by sep_ac_rfl)) ?_
      exact sepConj_mono (r2_callAt_send_unpack A.repAlloc g.call peerV)
        (sepConj_mono (r2_addrNameHeap_cap_lt A.repAlloc meG)
          (sepConj_mono (r2_now_open fsp)
            (sepConj_mono (r2_addrUpperAt_reloc (fsp + 0x1d0#64) meG)
              (sepConj_mono (r2_memRegion32_words4 (fsp + 0x320#64))
                (sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x23b0#64)))))))
    refine sepWPp_weaken_pre hopen_some ?_
    apply r2pb_peel_tc; intro peerG; apply r2pb_peel_tc; intro cw
    apply r2pb_peel_tc; intro _n0; apply r2pb_peel_tc; intro _n1
    apply r2pb_peel_tc; intro u0; apply r2pb_peel_tc; intro u1
    apply r2pb_peel_tc; intro _p0; apply r2pb_peel_tc; intro _p1
    apply r2pb_peel_tc; intro _p2; apply r2pb_peel_tc; intro _p3
    apply r2pb_peel_tc; intro _m0; apply r2pb_peel_tc; intro _m1
    apply r2pb_peel_tc; intro _m2; apply r2pb_peel_tc; intro _m3
    apply r2pb_peel_pure_tc; rintro ⟨hpeer_val, hw1, hw2, hw3, hw4⟩
    apply r2pb_peel_pure_tc; intro hme_lt
    let _ := hme_lt
    apply r2pb_peel_pure_tc; intro hu_me
    simp only [emp_sepConj, sepConj_assoc]
    have hcmn_z : (meG.name.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr (by bv_omega)
    have hcmn_nz : (meG.name.cap + 1#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
    have hcmn_ne : ConditionHolds .EQ (addsPState64 meG.name.cap 1#64) = false := by
      rw [conditionHolds_eq_addsPState64]; exact hcmn_z
    have hcmn_neq : ConditionHolds .NE (addsPState64 meG.name.cap 1#64) = true := by
      rw [conditionHolds_ne_addsPState64]; exact hcmn_nz
    let _ := hcmn_z; let _ := hcmn_nz; let _ := hcmn_ne; let _ := hcmn_neq
    apply r2pb_seq_step (mid := blkPl_579.base + 1236#64) hd.base.inv
    · rw [← r2_hold_eq (addrNameHeap A.repAlloc peerG),
          ← r2_hold_eq (addrNameHeap A.repAlloc meG),
          ← r2_hold_eq (memRegion (fsp + 12#64) 4),
          ← r2_hold_eq (memRegion g.res runResSize ∗ _)]
      dsimp +zetaDelta only [fsp]; rw [← hd.base.sp]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ⟨hvm, ⟨_, rfl⟩, rfl⟩⟩
      )
    intro _m_enc1 hvm_enc1 hinv_enc1
    apply r2pb_seq_lscro_oom (mid := blkPl_579.base + 1252#64) hinv_enc1
    dsimp only [runProgPlaced, lsProg_579]
    wp_steps
    apply SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
    intro hinv_enc2
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hvm_enc2 : VmPreserved s (r2pb_stOf hinv_enc2) :=
      hvm_enc1.trans ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    apply r2pb_seq_step (mid := lsmpl.base 464) hinv_enc2
    · dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ⟨hvm, ⟨_, rfl⟩, rfl⟩⟩
      )
    intro _m_enc hvm_enc3 hinv_enc
    change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv_enc) _ _ _ _
    have hvm_enc : VmPreserved s (r2pb_stOf hinv_enc) := hvm_enc2.trans hvm_enc3
    have hsp0 : s.sp = fsp := hd.base.sp
    have hsp_enc : (r2pb_stOf hinv_enc).sp = fsp := by
      dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hsp0
    have hx24_toNat : (s.readReg64 (.gpr 24#5)).toNat = g.i.stdin.length := by
      rw [hd.x24, hcall]
      have hinp : (inputOf g.i (.send peerV)).length = g.i.stdin.length := rfl
      rw [hinp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    let encG : EncGhost := r2EncGhost g peerG meG fsp
    have hfits_enc : FitsEnv M lim st (sEnvs.encrypt encG) :=
      fun evs hevs => hfits evs (h_pre g meV meG peerV peerG fsp evs hpeer_val hevs)
    have hspb_enc : resStack - runFrame ≤ (runFsp s0).toNat := by
      dsimp only [runFsp]; dsimp only [runFrame] at hframeLe ⊢; bv_omega
    have hmeA_ne : fsp + 0x23b0#64 ≠ 0#64 := by
      dsimp only [fsp, runFsp]; dsimp only [runFrame] at hframeLe; bv_omega
    have henc_call : subroutine_ok (runProgPlaced H) (lsmpl.base 464)
        (encSlotSpecPlaced A lim sEnvs.encrypt S (resStack - runFrame)) :=
      hc.encrypt (resStack - runFrame) hencNeed hsub63
    dsimp only [encSlotSpecPlaced] at henc_call
    refine r2pb_call (encG, st) henc_call hinv_enc
      (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
      (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hsp_al)
      (ret_pc := runPcPlaced 1308) (by r2pb_pc_done)
      (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗ runSaved s0 ∗
        memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
        memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        r2_localGaps fsp ∗ anyHeap) ?_
      (hpanic := fun sf _ _ hp => by
        dsimp +zetaDelta only [encG, r2EncGhost] at hp
        rw [sepConj_assoc, satisfies_pure_sepConj] at hp
        have hnone := hp.1
        rw [hpeer_val, hme_val] at hnone
        exact hpanic sf _ (Or.inl (by rw [hansLink, hnone]; rfl)))
      (hoom := fun _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
      (hnext := fun s_ret _ hinv_ret hpcm_ret hrun_ret hsp_ret hcs_ret => ?_)
    · have hcw_m := r2_callWords_to_memRegion56 g.call cw
      have hpeer_p := r2_peerWords_pack A.repAlloc (fsp + 0x320#64) peerG cw hw1 hw2 hw3 hw4
      have hme_p :
          ((fsp + 0x23b0#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x23b8#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x23c0#64) ↦₆₄ u0) ∗ ((fsp + 0x23c8#64) ↦₆₄ u1) ∗
            addrNameHeap A.repAlloc meG ⊢
          protocolAddressAt A.repAlloc meG (fsp + 0x23b0#64) := by
        rw [protocolAddressAt_eq_parts A.repAlloc meG (fsp + 0x23b0#64)]
        (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
        exact sepConj_mono_right (sepConj_mono_right
          (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm)
            (sepConj_mono_left
              (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                hu_me (fsp + 0x23c0#64)))))
      have hu16 :
          ((fsp + 0x1d0#64) ↦₆₄ u0) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1) ⊢
            memRegion (fsp + 0x1d0#64) 16 := by
        rw [ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 8) (k := 8)
              (b' := fsp + 0x1d8#64) rfl (by bv_omega) (by decide)]
        exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
      have hpool_e : A.pool lim st s ⊢ A.pool lim st (r2pb_stOf hinv_enc) :=
        Entails.of_eq (A.pool_transport lim st s (r2pb_stOf hinv_enc) hvm_enc).symm
      have hnow_e : nowCellAt fsp unixEpoch ⊢ nowCellAt (r2pb_stOf hinv_enc).sp unixEpoch :=
        Entails.of_eq (congrArg (nowCellAt · unixEpoch) hsp_enc.symm)
      have hstk_e :
          stackAt fsp (resStack - runFrame) ⊢
            stackAt (r2pb_stOf hinv_enc).sp (resStack - runFrame) :=
        Entails.of_eq (congrArg (stackAt · (resStack - runFrame)) hsp_enc.symm)
      have hassoc_coins : ∀ (X Y Z W : SepProp),
          X ∗ ((Y ∗ Z) ∗ W) = ((X ∗ Y) ∗ Z) ∗ W := fun X Y Z W =>
        (sepConj_assoc X (Y ∗ Z) W).symm.trans (congrArg (· ∗ W) (sepConj_assoc X Y Z).symm)
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpeer_p)
      refine Entails.trans (Entails.of_eq (Q :=
          (((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗
              ((g.call + 16#64) ↦₆₄ cw.w2) ∗
              ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
              ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
            (((fsp + 0x320#64) ↦₆₄ cw.w1) ∗ ((fsp + 0x328#64) ↦₆₄ cw.w2) ∗
              ((fsp + 0x330#64) ↦₆₄ cw.w3) ∗ ((fsp + 0x338#64) ↦₆₄ cw.w4) ∗
              addrNameHeap A.repAlloc peerG) ∗
            (((fsp + 0x23b0#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x23b8#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x23c0#64) ↦₆₄ u0) ∗ ((fsp + 0x23c8#64) ↦₆₄ u1) ∗
              addrNameHeap A.repAlloc meG) ∗
            (((fsp + 0x1d0#64) ↦₆₄ u0) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1)) ∗
            A.pool lim st s ∗
            nowCellAt fsp unixEpoch ∗
            stackAt fsp (resStack - runFrame) ∗
            (storesAt A.repAlloc g.stores StoresGhost.opened ∗
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗
              tokenInitPlacedAt ∗ lsLogOff ∗
              (g.inp ↦ₛ g.i.stdin) ∗ memRegion (fsp + 0x4d0#64) 248 ∗
              memRegion g.res runResSize ∗ runSaved s0 ∗
              memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
              memRegion (fsp + 0x1750#64) 248 ∗ r2_localGaps fsp ∗ anyHeap))) ?_) ?_
      · rw [hsp0, r2_hold_eq, r2_hold_eq, r2_hold_eq, r2_hold_eq]
        (try rw [← hw3])
        dsimp +zetaDelta only [nowCellAt, unixEpoch, fsp, runFsp]
        sep_ac_rfl
      · refine Entails.trans
          (sepConj_mono hcw_m (sepConj_mono hpeer_p (sepConj_mono hme_p
            (sepConj_mono hu16 (sepConj_mono hpool_e
              (sepConj_mono hnow_e (sepConj_mono_left hstk_e))))))) ?_
        dsimp +zetaDelta only [slotFramePlaced,
          LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
          CryptoVerification.SignalSession.Cli.RunCompose.slotFramePlaced,
          encG, r2EncGhost, CryptoVerification.SignalSession.Cli.RunCompose.EncGhost.toSlotCtx]
        refine Entails.trans ?_ (Entails.of_eq (sepConj_assoc _ _ _).symm)
        apply Entails.pure_right
        · refine ⟨by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x23,
                  by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx24_toNat,
                  hptLt,
                  by dsimp +zetaDelta only [r2pb_stOf, fsp]; (try simp only [wp_norm, arm64_norm]); (try rw [hsp0]); (try dsimp only [runFsp]); (try bv_omega),
                  by dsimp +zetaDelta only [r2pb_stOf, fsp]; (try simp only [wp_norm, arm64_norm]); (try rw [hsp0]); (try dsimp only [runFsp]); (try bv_omega),
                  by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); rw [hd.x19],
                  by dsimp only [r2pb_stOf]; simp only [sessVtPlaced, lsρ, cliSessionVtSym, wp_norm, arm64_norm],
                  by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x19,
                  by dsimp only [r2pb_stOf]; simp only [idVtPlaced, lsρ, cliIdentityVtSym, wp_norm, arm64_norm],
                  by dsimp +zetaDelta only [r2pb_stOf, fsp]; (try simp only [wp_norm, arm64_norm]); (try rw [hsp0]); (try dsimp only [runFsp]); (try bv_omega),
                  by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hfs0,
                  by rw [hpeer_val, hme_val]; exact hfilesOk,
                  by rw [hpeer_val]; exact hencOk,
                  by rw [hsp_enc]; exact hspb_enc,
                  hmeA_ne,
                  hfits_enc⟩
        · refine Entails.trans ?_ (Entails.of_eq (hassoc_coins _ _ _ _))
          exact Entails.pure_right hcoinsLt
            (Entails.of_eq (by dsimp +zetaDelta only [fsp, runFsp]; sep_ac_rfl))
    · dsimp +zetaDelta only [encG, r2EncGhost]
      apply r2pb_peel_tc; intro evs_enc
      apply r2pb_peel_tc; intro g'
      apply r2pb_peel_tc; intro e
      apply r2pb_peel_pure_tc; rintro ⟨henc_ev, hst, hout, hpkBound⟩
      have hhist_ret : RunHistOk g.i s0 s_ret :=
        r2p_histOk_of_slotTrace (r2p_histOk_of_trace_files hhist0 (by r2pb_eq) (by r2pb_eq)) hst
      have htr_ret : s0.trace <+: s_ret.trace :=
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.trace :
          s0.trace <+: (r2pb_stOf hinv_enc).trace).trans hst.1
      have hcs_r := r2p_cs_regs hcs_ret
      have hin_ret : InRunPlaced r2p_CodeOk s0 s_ret 1308 :=
        r2p_inRun_mk hd.base hpcm_ret hrun_ret (hsp_ret.trans (by r2pb_eq))
          (hcs_r.2.2.2.2.2.2.2.2.2.2.1.trans (by r2pb_eq)) hinv_ret
          (hcs_r.2.2.2.2.2.2.2.2.2.2.2.trans (by r2pb_eq))
      have hx19_r : s_ret.readReg64 (.gpr 19#5) = g.stores := by
        rw [hcs_r.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x19
      have hx20_r : s_ret.readReg64 (.gpr 20#5) = g.res := by
        rw [hcs_r.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x20
      have hx21_r : s_ret.readReg64 (.gpr 21#5) = meG.name.cap := by
        rw [hcs_r.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx21
      have hx22_r : s_ret.readReg64 (.gpr 22#5) = fsp + 0x4d0#64 := by
        rw [hcs_r.2.2.2.1]; dsimp only [r2pb_stOf]; simp only [wp_norm, arm64_norm]; rw [hsp0]
      have hx26_r : s_ret.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 := by
        rw [hcs_r.2.2.2.2.2.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x26
      have hx27_r : s_ret.readReg64 (.gpr 27#5) = fsp + 0x1750#64 := by
        rw [hcs_r.2.2.2.2.2.2.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x27
      have hx28_r : s_ret.readReg64 (.gpr 28#5) = meG.name.ptr := by
        rw [hcs_r.2.2.2.2.2.2.2.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx28
      clear hcs_ret hcs_r
      let st_enc := M.stepEvents evs_enc st
      refine sepWPp_weaken_pre (P' :=
          encResAt A.repAlloc (fsp + 0x4d0#64) e ∗ addrNameHeap A.repAlloc meG ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
            ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool lim st_enc s_ret ∗ anyHeap) ?_ ?_
      · have hnow_post :
            nowCellAt (r2pb_stOf hinv_enc).sp unixEpoch ⊢ memRegion fsp 16 :=
          Entails.trans (Entails.of_eq (congrArg (nowCellAt · unixEpoch) hsp_enc))
            (r2_now_to_mem16 fsp)
        have hstk_post :
            stackAt (r2pb_stOf hinv_enc).sp (resStack - runFrame) ⊢
              stackAt fsp (resStack - runFrame) :=
          Entails.of_eq (congrArg (stackAt · (resStack - runFrame)) hsp_enc)
        have hinp_post :
            (g.inp ↦ₛ g.i.stdin) ⊢ (g.inp ↦ₛ inputOf g.i g.c) :=
          Entails.of_eq (congrArg (g.inp ↦ₛ ·) (show g.i.stdin = inputOf g.i g.c by rw [hcall]; rfl))
        have hpeer_split :
            protocolAddressAt A.repAlloc peerG (fsp + 0x320#64) ⊢
              ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion (fsp + 0x330#64) 16 ∗ addrNameHeap A.repAlloc peerG := by
          rw [protocolAddressAt_eq_parts A.repAlloc peerG (fsp + 0x320#64)]
          (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
          exact sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left
              (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                addrUpperAt_entails_memRegion (fsp + 0x330#64) peerG)))
        refine Entails.trans (Entails.of_eq (Q :=
            protocolAddressAt A.repAlloc peerG (fsp + 0x320#64) ∗
              protocolAddressAt A.repAlloc meG (fsp + 0x23b0#64) ∗
              nowCellAt (r2pb_stOf hinv_enc).sp unixEpoch ∗
              stackAt (r2pb_stOf hinv_enc).sp (resStack - runFrame) ∗
              (g.inp ↦ₛ g.i.stdin) ∗
              (lsLogOff ∗ anyHeap ∗ anyHeap) ∗
              (encResAt A.repAlloc (fsp + 0x4d0#64) e ∗ memRegion g.res runResSize ∗
                memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗
                runSaved s0 ∗
                memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
                memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
                r2_localGaps fsp ∗ A.pool lim st_enc s_ret))
          (by dsimp +zetaDelta only [st_enc, fsp, runFsp]; sep_ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono hpeer_split
            (sepConj_mono (r2_protocolAddress_to_mem32_heap A.repAlloc meG (fsp + 0x23b0#64))
              (sepConj_mono hnow_post
                (sepConj_mono hstk_post
                  (sepConj_mono hinp_post (sepConj_mono_left (entails_anyHeap _)))))))
          (Entails.of_eq (by dsimp +zetaDelta only [st_enc, fsp, runFsp]; sep_ac_rfl))
      rw [hpeer_val, hme_val] at hout
      cases e with
      | error err =>
        have hneStore : err ≠ .store () := slotOut_err_ne_store hout
        have hans_err : g.a = some none := by rw [hansLink, hout.2.2]; rfl
        have henv_err : ∀ evs_drop : List AllocEvent, FreeOnlyEvs evs_drop →
            ∃ evs, SendEnv g (.some meV meG) peerV evs ∧
              M.stepEvents (evs_drop ++ r2pbFreeMePeerEvs meG peerG) st_enc = M.stepEvents evs st :=
          fun evs_drop hfo =>
            ⟨evs_enc ++ (evs_drop ++ r2pbFreeMePeerEvs meG peerG),
              h_err g meV meG peerV peerG fsp evs_enc (evs_drop ++ r2pbFreeMePeerEvs meG peerG)
                hpeer_val henc_ev (FreeOnlyEvs.append hfo (r2pbFreeMePeerEvs_freeOnly meG peerG)),
              (M.stepEvents_append evs_enc _ st).symm⟩
        exact r2pb_err_arm (peerG := peerG) (meG := meG) hh hdrop hdropNeed hextNeed hsub64
          hin_ret hx19_r hx20_r hx21_r hx22_r hx28_r htr_ret hhist_ret hneStore hans_err
          henv_err hrej
      | ok msg =>
        rcases hout.2.2 with ⟨hans_ok, hwr⟩
        cases msg with
        | signalMessage m =>
          have hans_sig : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)) := by
            rw [hansLink, hans_ok]; rfl
          have hfits_cat : FitsEvents M lim st_enc (cliConcat2Events [2#8] m.serialized) :=
            ((fitsEvents_append M lim evs_enc (cliConcat2Events [2#8] m.serialized) st).mp
              (hfits _ (h_sig_cat g meV meG peerV peerG fsp evs_enc g' m
                hpeer_val hans_ok henc_ev))).2
          have henv_sig : ∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f →
              ∃ evs, SendEnv g (.some meV meG) peerV evs ∧
                M.stepEvents evs_f (M.stepEvents (cliConcat2Events [2#8] m.serialized) st_enc) =
                  M.stepEvents evs st :=
            fun evs_f hfo =>
              ⟨evs_enc ++ (cliConcat2Events [2#8] m.serialized ++ evs_f),
                h_sig_ok g meV meG peerV peerG fsp evs_enc g' m evs_f
                  hpeer_val hans_ok henc_ev hfo,
                by simp [st_enc, AllocCostModel.stepEvents_append]⟩
          exact r2pb_sig_arm (peerG := peerG) (meG := meG) hh hcatNeed hextNeed hsub64 hin_ret
            hx19_r hx20_r hx21_r hx22_r hx26_r hx27_r hx28_r
            htr_ret hhist_ret hans_sig hwr hfits_cat henv_sig hjoin
        | preKeySignalMessage m =>
          have hans_pk : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)) := by
            rw [hansLink, hans_ok]; rfl
          have hfits_cat : FitsEvents M lim st_enc (cliConcat2Events [3#8] m.serialized) :=
            ((fitsEvents_append M lim evs_enc (cliConcat2Events [3#8] m.serialized) st).mp
              (hfits _ (h_pk_cat g meV meG peerV peerG fsp evs_enc g' m
                hpeer_val hans_ok henc_ev))).2
          have henv_pk : ∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f →
              ∃ evs, SendEnv g (.some meV meG) peerV evs ∧
                M.stepEvents evs_f (M.stepEvents (cliConcat2Events [3#8] m.serialized) st_enc) =
                  M.stepEvents evs st :=
            fun evs_f hfo =>
              ⟨evs_enc ++ (cliConcat2Events [3#8] m.serialized ++ evs_f),
                h_pk_ok g meV meG peerV peerG fsp evs_enc g' m evs_f
                  hpeer_val hans_ok henc_ev hfo,
                by simp [st_enc, AllocCostModel.stepEvents_append]⟩
          exact r2pb_pk_arm (peerG := peerG) (meG := meG) hh hcatNeed hdpkNeed hextNeed hsub64
            hin_ret hx19_r hx20_r hx21_r hx22_r hx26_r hx27_r hx28_r
            htr_ret hhist_ret hans_pk hwr (hpkBound m rfl) hfits_cat henv_pk hjoin

/-- Budget-threaded Arm `R2` hop proof (`R+0x214` → Join/Reject) on Block `579` (`runProgPlaced H`),
instantiated with `R2SendEnv sEnvs S` for any address-pointer-invariant `sEnvs.encrypt`. -/
theorem run_hop_send_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (henc_addr : ∀ g peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) =
        sEnvs.encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64) := by
      intros; rfl) :
    RunHopSendPlaced (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs sEnvs (R2SendEnv sEnvs S) H B S needs resStack :=
  run_hop_send_placed_ok_of_env
    (fun _ _ peerG => r2pbFreePeerEvs_freeOnly peerG)
    (fun g _ meG peerV peerG fsp _ hp h => by
      rw [henc_addr g peerV peerG meG fsp hp] at h
      exact SeqEnv.inl h)
    (fun g _ meG peerV peerG fsp _ _ hp h hfo => by
      rw [henc_addr g peerV peerG meG fsp hp] at h
      exact SeqEnv.append h (Or.inl hfo))
    (fun g meV meG peerV peerG fsp _ g' m hp hans h => by
      rw [henc_addr g peerV peerG meG fsp hp] at h
      refine SeqEnv.append h (Or.inr ?_)
      simp [hans])
    (fun g meV meG peerV peerG fsp _ g' m evs_f hp hans h hfo => by
      rw [henc_addr g peerV peerG meG fsp hp] at h
      refine SeqEnv.append h (Or.inr ?_)
      simp only [hans]
      exact Or.inr ⟨evs_f, hfo, rfl⟩)
    (fun g meV meG peerV peerG fsp _ g' m hp hans h => by
      rw [henc_addr g peerV peerG meG fsp hp] at h
      refine SeqEnv.append h (Or.inr ?_)
      simp [hans])
    (fun g meV meG peerV peerG fsp _ g' m evs_f hp hans h hfo => by
      rw [henc_addr g peerV peerG meG fsp hp] at h
      refine SeqEnv.append h (Or.inr ?_)
      simp only [hans]
      exact Or.inr ⟨evs_f, hfo, rfl⟩)


set_option maxHeartbeats 1600000 in
theorem run_hop_send_of_slots_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : CryptoVerification.SignalSession.Cli.RunSkeleton.RunSlots} {resStack : Nat}
    (hneed_eq : CryptoVerification.SignalSession.Cli.RunSkeleton.runNeed B slots =
      CryptoVerification.SignalSession.Cli.RunSkeleton.runNeed B (slotsOfPlaced A lim sEnvs S needs))
    (henc_eq : slots.encrypt = (slotsOfPlaced A lim sEnvs S needs).encrypt)
    (henc_addr : ∀ g peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) =
        sEnvs.encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64) := by
      intros; rfl) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2PlacedBudget.RunHopSendPlacedOf
      (LibsignalCodeRoLoaded lsmpl) A lim cEnvs (R2SendEnv sEnvs S) H B S slots resStack := by
  have h_none : ∀ g peerV peerG,
      R2SendEnv sEnvs S g .none peerV (r2pbFreePeerEvs peerG) :=
    fun _ _ peerG => r2pbFreePeerEvs_freeOnly peerG
  have h_pre : ∀ g meV meG peerV peerG fsp evs,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) evs →
      R2SendEnv sEnvs S g (.some meV meG) peerV evs :=
    fun g _ meG peerV peerG fsp _ hp h => by
      rw [henc_addr g peerV peerG meG fsp hp] at h
      exact SeqEnv.inl h
  have h_err : ∀ g meV meG peerV peerG fsp evs_enc evs_f,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) evs_enc →
      FreeOnlyEvs evs_f →
      R2SendEnv sEnvs S g (.some meV meG) peerV (evs_enc ++ evs_f) :=
    fun g _ meG peerV peerG fsp _ _ hp h hfo => by
      rw [henc_addr g peerV peerG meG fsp hp] at h
      exact SeqEnv.append h (Or.inl hfo)
  have h_sig_cat : ∀ g meV meG peerV peerG fsp evs_enc g' m,
      peerG.val = addrValOf peerV →
      S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV) g.i.stdin (coinsOf g.i) =
        some (some (g', .signalMessage m)) →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) evs_enc →
      R2SendEnv sEnvs S g (.some meV meG) peerV (evs_enc ++ cliConcat2Events [2#8] m.serialized) :=
    fun g meV meG peerV peerG fsp _ g' m hp hans h => by
      rw [henc_addr g peerV peerG meG fsp hp] at h
      refine SeqEnv.append h (Or.inr ?_)
      simp [hans]
  have h_sig_ok : ∀ g meV meG peerV peerG fsp evs_enc g' m evs_f,
      peerG.val = addrValOf peerV →
      S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV) g.i.stdin (coinsOf g.i) =
        some (some (g', .signalMessage m)) →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) evs_enc →
      FreeOnlyEvs evs_f →
      R2SendEnv sEnvs S g (.some meV meG) peerV
        (evs_enc ++ (cliConcat2Events [2#8] m.serialized ++ evs_f)) :=
    fun g meV meG peerV peerG fsp _ g' m evs_f hp hans h hfo => by
      rw [henc_addr g peerV peerG meG fsp hp] at h
      refine SeqEnv.append h (Or.inr ?_)
      simp only [hans]
      exact Or.inr ⟨evs_f, hfo, rfl⟩
  have h_pk_cat : ∀ g meV meG peerV peerG fsp evs_enc g' m,
      peerG.val = addrValOf peerV →
      S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV) g.i.stdin (coinsOf g.i) =
        some (some (g', .preKeySignalMessage m)) →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) evs_enc →
      R2SendEnv sEnvs S g (.some meV meG) peerV (evs_enc ++ cliConcat2Events [3#8] m.serialized) :=
    fun g meV meG peerV peerG fsp _ g' m hp hans h => by
      rw [henc_addr g peerV peerG meG fsp hp] at h
      refine SeqEnv.append h (Or.inr ?_)
      simp [hans]
  have h_pk_ok : ∀ g meV meG peerV peerG fsp evs_enc g' m evs_f,
      peerG.val = addrValOf peerV →
      S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV) g.i.stdin (coinsOf g.i) =
        some (some (g', .preKeySignalMessage m)) →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) evs_enc →
      FreeOnlyEvs evs_f →
      R2SendEnv sEnvs S g (.some meV meG) peerV
        (evs_enc ++ (cliConcat2Events [3#8] m.serialized ++ evs_f)) :=
    fun g meV meG peerV peerG fsp _ g' m evs_f hp hans h hfo => by
      rw [henc_addr g peerV peerG meG fsp hp] at h
      refine SeqEnv.append h (Or.inr ?_)
      simp only [hans]
      exact Or.inr ⟨evs_f, hfo, rfl⟩
  intro g st s0 s me peerV Q Qp hh hc hdrop hres_slots hres64 _hspb he hd hcall hfits hpanic hrej hjoin
  have hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack := hneed_eq ▸ hres_slots
  obtain ⟨hframeLe, hsub63, hsub64, _, _, _, _, _, _, _, _, _, _, _,
      hdropNeed, hcatNeed, hextNeed, hencNeed, _, _, _, hdpkNeed⟩ :=
    runNeed_bounds_placed hres hres64
  let fsp := runFsp s0
  have hfsp_def : runFsp s0 = fsp := rfl
  have hpc : s.pc = runPcPlaced 532 := hd.base.pc; change s.pc = (blkPl_579).base + 532#64 at hpc
  have hrun0 : s.status = .Running := hd.base.run
  have hsp_al : s.spAligned = true := hd.base.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 2#64 := by rw [hd.x8, hcall]; rfl
  have hx25 : s.readReg64 (.gpr 25#5) = g.call := hd.x25
  have hd_gt : ConditionHolds .GT (subsPState64 2#64 1#64) = true := by r2pb_cond
  have hd_le : ConditionHolds .LE (subsPState64 2#64 1#64) = false := by r2pb_cond
  have hs_ne : ConditionHolds .NE (subsPState64 2#64 2#64) = false := by r2pb_cond
  have hs_eq : ConditionHolds .EQ (subsPState64 2#64 2#64) = true := by r2pb_cond
  have hhist0 : RunHistOk g.i s0 s := ⟨hd.fs, hd.stdout⟩
  refine sepWPp_weaken_pre
    (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
      (sepConj_mono_right (entails_anyHeap emp))) ?_
  cases me with
  | none =>
    have hans_none : g.a = some none := hd.reject_of_me_none he
    have hx20 : s.readReg64 (.gpr 20#5) = g.res := hd.x20
    have hx21_none : s.readReg64 (.gpr 21#5) = 0xffffffffffffffff#64 := hd.meRegs
    have hmn_eq : ConditionHolds .EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by r2pb_cond
    have hmn_ne : ConditionHolds .NE (addsPState64 0xffffffffffffffff#64 1#64) = false := by r2pb_cond
    dsimp only [dispatchMemPlaced,
      CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced,
      dispatchMeHeap, dispatchCells]
    rw [storesAt_atState]
    change SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((memRegion g.res runResSize ∗ callAt A.repAlloc g.call g.c ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗
        tokenInitPlacedAt ∗ lsLogOff ∗ emp ∗ runSaved s0 ∗
        runLocals (runFsp s0) [] ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s) ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝)
    rw [hfsp_def, hcall, emp_sepConj, r2_locals_none_eq fsp]
    have hopen_none :
        (memRegion g.res runResSize ∗ callAt A.repAlloc g.call (.send peerV) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗
          tokenInitPlacedAt ∗ lsLogOff ∗ runSaved s0 ∗
          (memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) ∗ anyHeap ⊢
        (∃∗ r0 : BitVec 64, (g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
        (∃∗ peerG : AddrGhost, ∃∗ cw : CallW,
          ⌜peerG.val = addrValOf peerV ∧ peerG.name.cap = cw.w1 ∧ peerG.name.ptr = cw.w2 ∧
            cw.w3 = BitVec.ofNat 64 peerG.name.bytes.length ∧ cw.w4.setWidth 8 = peerG.device⌝ ∗
          ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
            ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
            ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
          addrNameHeap A.repAlloc peerG) ∗
        (∃∗ p0 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p2 : BitVec 64, ∃∗ p3 : BitVec 64,
          ((fsp + 0x320#64) ↦₆₄ p0) ∗ (((fsp + 0x320#64) + 8#64) ↦₆₄ p1) ∗
          (((fsp + 0x320#64) + 16#64) ↦₆₄ p2) ∗ (((fsp + 0x320#64) + 24#64) ↦₆₄ p3)) ∗
        (storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗
          tokenInitPlacedAt ∗ lsLogOff ∗ runSaved s0 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
          memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗
          memRegion (fsp + 0x1750#64) 248 ∗ memRegion (fsp + 0x23b0#64) 32 ∗
          r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) := by
      refine Entails.trans (Entails.of_eq (Q :=
          memRegion g.res runResSize ∗ callAt A.repAlloc g.call (.send peerV) ∗
            memRegion (fsp + 0x320#64) 32 ∗
            (storesAt A.repAlloc g.stores StoresGhost.opened ∗
              (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗
              tokenInitPlacedAt ∗ lsLogOff ∗ runSaved s0 ∗
              memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
              memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗
              memRegion (fsp + 0x1750#64) 248 ∗ memRegion (fsp + 0x23b0#64) 32 ∗
              r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗
              A.pool lim st s ∗ anyHeap)) (by sep_ac_rfl)) ?_
      exact sepConj_mono (r2_res_open g.res)
        (sepConj_mono (r2_callAt_send_unpack A.repAlloc g.call peerV)
          (sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x320#64))))
    refine sepWPp_weaken_pre hopen_none ?_
    apply r2pb_peel_tc; intro _r0; apply r2pb_peel_tc; intro peerG; apply r2pb_peel_tc; intro cw
    apply r2pb_peel_tc; intro _p0; apply r2pb_peel_tc; intro _p1
    apply r2pb_peel_tc; intro _p2; apply r2pb_peel_tc; intro _p3
    apply r2pb_peel_pure_tc; rintro ⟨_, hw1, hw2, _, _⟩
    simp only [emp_sepConj, sepConj_assoc]
    apply r2pb_seq_step (mid := runPcPlaced 2984) hd.base.inv
    · rw [← r2_hold_eq (memRegion (g.res + 8#64) (runResSize - 8)),
          ← r2_hold_eq (addrNameHeap A.repAlloc peerG),
          ← r2_hold_eq (storesAt A.repAlloc g.stores StoresGhost.opened ∗ _),
          runPcPlaced_eq]
      dsimp +zetaDelta only [fsp]; rw [← hd.base.sp]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ⟨hvm, ⟨_, rfl⟩, rfl⟩⟩
      )
    intro _m_none hvm1 hinv1
    change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
    rw [hd.base.sp, r2_hold_eq, r2_hold_eq, r2_hold_eq]
    have hin1 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv1) 2984 :=
      r2p_inRun_mk hd.base (by r2pb_pc_done)
        (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
        (by r2pb_eq) (by r2pb_eq) hinv1 (by r2pb_eq)
    have hp16 :
        ((fsp + 0x330#64) ↦₆₄ cw.w3) ∗ ((fsp + 0x338#64) ↦₆₄ cw.w4) ⊢
          memRegion (fsp + 0x330#64) 16 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x330#64) (n := 8) (k := 8)
            (b' := fsp + 0x338#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    let postNone : SepProp :=
      runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st (r2pb_stOf hinv1) ∗ anyHeap
    refine sepWPp_weaken_pre (P' := postNone) ?_ ?_
    · dsimp +zetaDelta only [postNone]; rw [hcall]
      have hres_n := r2_res_write_none A.repAlloc g.res 0xffffffffffffffff#64 rfl
      have hcw_m := r2_callWords_to_memRegion56 g.call cw
      have hpool_n : A.pool lim st s ⊢ A.pool lim st (r2pb_stOf hinv1) :=
        Entails.of_eq (A.pool_transport lim st s (r2pb_stOf hinv1) hvm1).symm
      refine Entails.trans (Entails.of_eq (Q :=
          (((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
            ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
              ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
              ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
            (((fsp + 0x330#64) ↦₆₄ cw.w3) ∗ ((fsp + 0x338#64) ↦₆₄ cw.w4)) ∗
            (coinsInstalledPlaced g.coins (coinsOf g.i) ∗
              tokenInitPlacedAt ∗ lsLogOff ∗ anyHeap) ∗
            A.pool lim st s ∗
            (storesAt A.repAlloc g.stores StoresGhost.opened ∗
              (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
              addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
              memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
              memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
              memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
              stackAt fsp (resStack - runFrame)))) ?_) ?_
      · rw [← hw1, ← hw2]; dsimp +zetaDelta only [fsp]; sep_ac_rfl
      · refine Entails.trans (sepConj_mono hres_n (sepConj_mono hcw_m (sepConj_mono hp16
          (sepConj_mono (entails_anyHeap _) (sepConj_mono_left hpool_n)))))
          (Entails.of_eq (by sep_ac_rfl))
    · exact r2pb_free_peer_reject (peerG := peerG) hh hextNeed hsub64 hin1
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x19)
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.trace)
        (r2p_histOk_of_trace_files hhist0 (by r2pb_eq) (by r2pb_eq))
        hans_none
        ⟨r2pbFreePeerEvs peerG, h_none g peerV peerG, rfl⟩
        hrej
  | some meV meG =>
    obtain ⟨hptLt, hcoinsLt, hfs0, hfilesOk, hencOk, hansLink⟩ := hd.send_facts he hcall
    rcases hd.meRegs with ⟨hx21, hx28, hme_bytes, _, hme_dev⟩
    have hme_val : meG.val = addrValOf meV := by
      unfold AddrGhost.val addrValOf; simp [hme_bytes, hme_dev]
    dsimp only [dispatchMemPlaced,
      CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced,
      dispatchMeHeap, dispatchCells]
    rw [storesAt_atState]
    change SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((memRegion g.res runResSize ∗ callAt A.repAlloc g.call g.c ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗
        tokenInitPlacedAt ∗ lsLogOff ∗ addrNameHeap A.repAlloc meG ∗ runSaved s0 ∗
        runLocals (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s) ∗ anyHeap)
      Q Qp (fun _ => ⌜False⌝)
    rw [hfsp_def, hcall, r2_locals_some_eq fsp]
    have hopen_some :
        (memRegion g.res runResSize ∗ callAt A.repAlloc g.call (.send peerV) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗
          tokenInitPlacedAt ∗ lsLogOff ∗
          addrNameHeap A.repAlloc meG ∗ runSaved s0 ∗
          (memRegion fsp 16 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion (fsp + 0x208#64) 24 ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) ∗ anyHeap ⊢
        (∃∗ peerG : AddrGhost, ∃∗ cw : CallW,
          ⌜peerG.val = addrValOf peerV ∧ peerG.name.cap = cw.w1 ∧ peerG.name.ptr = cw.w2 ∧
            cw.w3 = BitVec.ofNat 64 peerG.name.bytes.length ∧ cw.w4.setWidth 8 = peerG.device⌝ ∗
          ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
            ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
            ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
          addrNameHeap A.repAlloc peerG) ∗
        (⌜meG.name.cap.toNat < 2 ^ 63⌝ ∗ addrNameHeap A.repAlloc meG) ∗
        (∃∗ n0 : BitVec 64, ∃∗ n1 : BitVec 32,
          (fsp ↦₆₄ n0) ∗ ((fsp + 8#64) ↦₃₂ n1) ∗ memRegion (fsp + 12#64) 4) ∗
        (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
          ⌜∀ dst, (dst ↦₆₄ u0) ∗ ((dst + 8#64) ↦₆₄ u1) ⊢ addrUpperAt dst meG⌝ ∗
            ((fsp + 0x1d0#64) ↦₆₄ u0) ∗ (((fsp + 0x1d0#64) + 8#64) ↦₆₄ u1)) ∗
        (∃∗ p0 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p2 : BitVec 64, ∃∗ p3 : BitVec 64,
          ((fsp + 0x320#64) ↦₆₄ p0) ∗ (((fsp + 0x320#64) + 8#64) ↦₆₄ p1) ∗
          (((fsp + 0x320#64) + 16#64) ↦₆₄ p2) ∗ (((fsp + 0x320#64) + 24#64) ↦₆₄ p3)) ∗
        (∃∗ m0 : BitVec 64, ∃∗ m1 : BitVec 64, ∃∗ m2 : BitVec 64, ∃∗ m3 : BitVec 64,
          ((fsp + 0x23b0#64) ↦₆₄ m0) ∗ (((fsp + 0x23b0#64) + 8#64) ↦₆₄ m1) ∗
          (((fsp + 0x23b0#64) + 16#64) ↦₆₄ m2) ∗ (((fsp + 0x23b0#64) + 24#64) ↦₆₄ m3)) ∗
        (memRegion g.res runResSize ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
          (g.inp ↦ₛ g.i.stdin) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗
          tokenInitPlacedAt ∗ lsLogOff ∗ runSaved s0 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
          r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗
          A.pool lim st s ∗ anyHeap) := by
      have hinp : inputOf g.i (.send peerV) = g.i.stdin := rfl
      rw [hinp]
      refine Entails.trans (Entails.of_eq (Q :=
          callAt A.repAlloc g.call (.send peerV) ∗ addrNameHeap A.repAlloc meG ∗
            memRegion fsp 16 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗
            memRegion (fsp + 0x320#64) 32 ∗ memRegion (fsp + 0x23b0#64) 32 ∗
            (memRegion g.res runResSize ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
              (g.inp ↦ₛ g.i.stdin) ∗
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗
              tokenInitPlacedAt ∗ lsLogOff ∗ runSaved s0 ∗
              memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
              memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
              r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗
              A.pool lim st s ∗ anyHeap)) (by sep_ac_rfl)) ?_
      exact sepConj_mono (r2_callAt_send_unpack A.repAlloc g.call peerV)
        (sepConj_mono (r2_addrNameHeap_cap_lt A.repAlloc meG)
          (sepConj_mono (r2_now_open fsp)
            (sepConj_mono (r2_addrUpperAt_reloc (fsp + 0x1d0#64) meG)
              (sepConj_mono (r2_memRegion32_words4 (fsp + 0x320#64))
                (sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x23b0#64)))))))
    refine sepWPp_weaken_pre hopen_some ?_
    apply r2pb_peel_tc; intro peerG; apply r2pb_peel_tc; intro cw
    apply r2pb_peel_tc; intro _n0; apply r2pb_peel_tc; intro _n1
    apply r2pb_peel_tc; intro u0; apply r2pb_peel_tc; intro u1
    apply r2pb_peel_tc; intro _p0; apply r2pb_peel_tc; intro _p1
    apply r2pb_peel_tc; intro _p2; apply r2pb_peel_tc; intro _p3
    apply r2pb_peel_tc; intro _m0; apply r2pb_peel_tc; intro _m1
    apply r2pb_peel_tc; intro _m2; apply r2pb_peel_tc; intro _m3
    apply r2pb_peel_pure_tc; rintro ⟨hpeer_val, hw1, hw2, hw3, hw4⟩
    apply r2pb_peel_pure_tc; intro hme_lt
    let _ := hme_lt
    apply r2pb_peel_pure_tc; intro hu_me
    simp only [emp_sepConj, sepConj_assoc]
    have hcmn_z : (meG.name.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr (by bv_omega)
    have hcmn_nz : (meG.name.cap + 1#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
    have hcmn_ne : ConditionHolds .EQ (addsPState64 meG.name.cap 1#64) = false := by
      rw [conditionHolds_eq_addsPState64]; exact hcmn_z
    have hcmn_neq : ConditionHolds .NE (addsPState64 meG.name.cap 1#64) = true := by
      rw [conditionHolds_ne_addsPState64]; exact hcmn_nz
    let _ := hcmn_z; let _ := hcmn_nz; let _ := hcmn_ne; let _ := hcmn_neq
    apply r2pb_seq_step (mid := blkPl_579.base + 1236#64) hd.base.inv
    · rw [← r2_hold_eq (addrNameHeap A.repAlloc peerG),
          ← r2_hold_eq (addrNameHeap A.repAlloc meG),
          ← r2_hold_eq (memRegion (fsp + 12#64) 4),
          ← r2_hold_eq (memRegion g.res runResSize ∗ _)]
      dsimp +zetaDelta only [fsp]; rw [← hd.base.sp]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ⟨hvm, ⟨_, rfl⟩, rfl⟩⟩
      )
    intro _m_enc1 hvm_enc1 hinv_enc1
    apply r2pb_seq_lscro_oom (mid := blkPl_579.base + 1252#64) hinv_enc1
    dsimp only [runProgPlaced, lsProg_579]
    wp_steps
    apply SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
    intro hinv_enc2
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hvm_enc2 : VmPreserved s (r2pb_stOf hinv_enc2) :=
      hvm_enc1.trans ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    apply r2pb_seq_step (mid := lsmpl.base 464) hinv_enc2
    · dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm => ⟨hvm, ⟨_, rfl⟩, rfl⟩⟩
      )
    intro _m_enc hvm_enc3 hinv_enc
    change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv_enc) _ _ _ _
    have hvm_enc : VmPreserved s (r2pb_stOf hinv_enc) := hvm_enc2.trans hvm_enc3
    have hsp0 : s.sp = fsp := hd.base.sp
    have hsp_enc : (r2pb_stOf hinv_enc).sp = fsp := by
      dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hsp0
    have hx24_toNat : (s.readReg64 (.gpr 24#5)).toNat = g.i.stdin.length := by
      rw [hd.x24, hcall]
      have hinp : (inputOf g.i (.send peerV)).length = g.i.stdin.length := rfl
      rw [hinp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    let encG : EncGhost := r2EncGhost g peerG meG fsp
    have hfits_enc : FitsEnv M lim st (sEnvs.encrypt encG) :=
      fun evs hevs => hfits evs (h_pre g meV meG peerV peerG fsp evs hpeer_val hevs)
    have hspb_enc : resStack - runFrame ≤ (runFsp s0).toNat := by
      dsimp only [runFsp]; dsimp only [runFrame] at hframeLe ⊢; bv_omega
    have hmeA_ne : fsp + 0x23b0#64 ≠ 0#64 := by
      dsimp only [fsp, runFsp]; dsimp only [runFrame] at hframeLe; bv_omega
    have henc_call : subroutine_ok (runProgPlaced H) (lsmpl.base 464)
        (encSlotSpecPlaced A lim sEnvs.encrypt S (resStack - runFrame)) :=
      (henc_eq ▸ hc.encrypt) (resStack - runFrame) hencNeed hsub63
    dsimp only [encSlotSpecPlaced] at henc_call
    refine r2pb_call (encG, st) henc_call hinv_enc
      (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
      (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hsp_al)
      (ret_pc := runPcPlaced 1308) (by r2pb_pc_done)
      (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗ runSaved s0 ∗
        memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
        memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        r2_localGaps fsp ∗ anyHeap) ?_
      (hpanic := fun sf _ _ hp => by
        dsimp +zetaDelta only [encG, r2EncGhost] at hp
        rw [sepConj_assoc, satisfies_pure_sepConj] at hp
        have hnone := hp.1
        rw [hpeer_val, hme_val] at hnone
        exact hpanic sf _ (Or.inl (by rw [hansLink, hnone]; rfl)))
      (hoom := fun _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
      (hnext := fun s_ret _ hinv_ret hpcm_ret hrun_ret hsp_ret hcs_ret => ?_)
    · have hcw_m := r2_callWords_to_memRegion56 g.call cw
      have hpeer_p := r2_peerWords_pack A.repAlloc (fsp + 0x320#64) peerG cw hw1 hw2 hw3 hw4
      have hme_p :
          ((fsp + 0x23b0#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x23b8#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x23c0#64) ↦₆₄ u0) ∗ ((fsp + 0x23c8#64) ↦₆₄ u1) ∗
            addrNameHeap A.repAlloc meG ⊢
          protocolAddressAt A.repAlloc meG (fsp + 0x23b0#64) := by
        rw [protocolAddressAt_eq_parts A.repAlloc meG (fsp + 0x23b0#64)]
        (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
        exact sepConj_mono_right (sepConj_mono_right
          (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm)
            (sepConj_mono_left
              (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                hu_me (fsp + 0x23c0#64)))))
      have hu16 :
          ((fsp + 0x1d0#64) ↦₆₄ u0) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1) ⊢
            memRegion (fsp + 0x1d0#64) 16 := by
        rw [ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 8) (k := 8)
              (b' := fsp + 0x1d8#64) rfl (by bv_omega) (by decide)]
        exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
      have hpool_e : A.pool lim st s ⊢ A.pool lim st (r2pb_stOf hinv_enc) :=
        Entails.of_eq (A.pool_transport lim st s (r2pb_stOf hinv_enc) hvm_enc).symm
      have hnow_e : nowCellAt fsp unixEpoch ⊢ nowCellAt (r2pb_stOf hinv_enc).sp unixEpoch :=
        Entails.of_eq (congrArg (nowCellAt · unixEpoch) hsp_enc.symm)
      have hstk_e :
          stackAt fsp (resStack - runFrame) ⊢
            stackAt (r2pb_stOf hinv_enc).sp (resStack - runFrame) :=
        Entails.of_eq (congrArg (stackAt · (resStack - runFrame)) hsp_enc.symm)
      have hassoc_coins : ∀ (X Y Z W : SepProp),
          X ∗ ((Y ∗ Z) ∗ W) = ((X ∗ Y) ∗ Z) ∗ W := fun X Y Z W =>
        (sepConj_assoc X (Y ∗ Z) W).symm.trans (congrArg (· ∗ W) (sepConj_assoc X Y Z).symm)
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpeer_p)
      refine Entails.trans (Entails.of_eq (Q :=
          (((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗
              ((g.call + 16#64) ↦₆₄ cw.w2) ∗
              ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
              ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
            (((fsp + 0x320#64) ↦₆₄ cw.w1) ∗ ((fsp + 0x328#64) ↦₆₄ cw.w2) ∗
              ((fsp + 0x330#64) ↦₆₄ cw.w3) ∗ ((fsp + 0x338#64) ↦₆₄ cw.w4) ∗
              addrNameHeap A.repAlloc peerG) ∗
            (((fsp + 0x23b0#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x23b8#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x23c0#64) ↦₆₄ u0) ∗ ((fsp + 0x23c8#64) ↦₆₄ u1) ∗
              addrNameHeap A.repAlloc meG) ∗
            (((fsp + 0x1d0#64) ↦₆₄ u0) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1)) ∗
            A.pool lim st s ∗
            nowCellAt fsp unixEpoch ∗
            stackAt fsp (resStack - runFrame) ∗
            (storesAt A.repAlloc g.stores StoresGhost.opened ∗
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗
              tokenInitPlacedAt ∗ lsLogOff ∗
              (g.inp ↦ₛ g.i.stdin) ∗ memRegion (fsp + 0x4d0#64) 248 ∗
              memRegion g.res runResSize ∗ runSaved s0 ∗
              memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
              memRegion (fsp + 0x1750#64) 248 ∗ r2_localGaps fsp ∗ anyHeap))) ?_) ?_
      · rw [hsp0, r2_hold_eq, r2_hold_eq, r2_hold_eq, r2_hold_eq]
        (try rw [← hw3])
        dsimp +zetaDelta only [nowCellAt, unixEpoch, fsp, runFsp]
        sep_ac_rfl
      · refine Entails.trans
          (sepConj_mono hcw_m (sepConj_mono hpeer_p (sepConj_mono hme_p
            (sepConj_mono hu16 (sepConj_mono hpool_e
              (sepConj_mono hnow_e (sepConj_mono_left hstk_e))))))) ?_
        dsimp +zetaDelta only [slotFramePlaced,
          LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
          CryptoVerification.SignalSession.Cli.RunCompose.slotFramePlaced,
          encG, r2EncGhost, CryptoVerification.SignalSession.Cli.RunCompose.EncGhost.toSlotCtx]
        refine Entails.trans ?_ (Entails.of_eq (sepConj_assoc _ _ _).symm)
        apply Entails.pure_right
        · refine ⟨by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x23,
                  by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx24_toNat,
                  hptLt,
                  by dsimp +zetaDelta only [r2pb_stOf, fsp]; (try simp only [wp_norm, arm64_norm]); (try rw [hsp0]); (try dsimp only [runFsp]); (try bv_omega),
                  by dsimp +zetaDelta only [r2pb_stOf, fsp]; (try simp only [wp_norm, arm64_norm]); (try rw [hsp0]); (try dsimp only [runFsp]); (try bv_omega),
                  by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); rw [hd.x19],
                  by dsimp only [r2pb_stOf]; simp only [sessVtPlaced, lsρ, cliSessionVtSym, wp_norm, arm64_norm],
                  by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x19,
                  by dsimp only [r2pb_stOf]; simp only [idVtPlaced, lsρ, cliIdentityVtSym, wp_norm, arm64_norm],
                  by dsimp +zetaDelta only [r2pb_stOf, fsp]; (try simp only [wp_norm, arm64_norm]); (try rw [hsp0]); (try dsimp only [runFsp]); (try bv_omega),
                  by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hfs0,
                  by rw [hpeer_val, hme_val]; exact hfilesOk,
                  by rw [hpeer_val]; exact hencOk,
                  by rw [hsp_enc]; exact hspb_enc,
                  hmeA_ne,
                  hfits_enc⟩
        · refine Entails.trans ?_ (Entails.of_eq (hassoc_coins _ _ _ _))
          exact Entails.pure_right hcoinsLt
            (Entails.of_eq (by dsimp +zetaDelta only [fsp, runFsp]; sep_ac_rfl))
    · dsimp +zetaDelta only [encG, r2EncGhost]
      apply r2pb_peel_tc; intro evs_enc
      apply r2pb_peel_tc; intro g'
      apply r2pb_peel_tc; intro e
      apply r2pb_peel_pure_tc; rintro ⟨henc_ev, hst, hout, hpkBound⟩
      have hhist_ret : RunHistOk g.i s0 s_ret :=
        r2p_histOk_of_slotTrace (r2p_histOk_of_trace_files hhist0 (by r2pb_eq) (by r2pb_eq)) hst
      have htr_ret : s0.trace <+: s_ret.trace :=
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.trace :
          s0.trace <+: (r2pb_stOf hinv_enc).trace).trans hst.1
      have hcs_r := r2p_cs_regs hcs_ret
      have hin_ret : InRunPlaced r2p_CodeOk s0 s_ret 1308 :=
        r2p_inRun_mk hd.base hpcm_ret hrun_ret (hsp_ret.trans (by r2pb_eq))
          (hcs_r.2.2.2.2.2.2.2.2.2.2.1.trans (by r2pb_eq)) hinv_ret
          (hcs_r.2.2.2.2.2.2.2.2.2.2.2.trans (by r2pb_eq))
      have hx19_r : s_ret.readReg64 (.gpr 19#5) = g.stores := by
        rw [hcs_r.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x19
      have hx20_r : s_ret.readReg64 (.gpr 20#5) = g.res := by
        rw [hcs_r.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x20
      have hx21_r : s_ret.readReg64 (.gpr 21#5) = meG.name.cap := by
        rw [hcs_r.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx21
      have hx22_r : s_ret.readReg64 (.gpr 22#5) = fsp + 0x4d0#64 := by
        rw [hcs_r.2.2.2.1]; dsimp only [r2pb_stOf]; simp only [wp_norm, arm64_norm]; rw [hsp0]
      have hx26_r : s_ret.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 := by
        rw [hcs_r.2.2.2.2.2.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x26
      have hx27_r : s_ret.readReg64 (.gpr 27#5) = fsp + 0x1750#64 := by
        rw [hcs_r.2.2.2.2.2.2.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hd.x27
      have hx28_r : s_ret.readReg64 (.gpr 28#5) = meG.name.ptr := by
        rw [hcs_r.2.2.2.2.2.2.2.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx28
      clear hcs_ret hcs_r
      let st_enc := M.stepEvents evs_enc st
      refine sepWPp_weaken_pre (P' :=
          encResAt A.repAlloc (fsp + 0x4d0#64) e ∗ addrNameHeap A.repAlloc meG ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
            ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool lim st_enc s_ret ∗ anyHeap) ?_ ?_
      · have hnow_post :
            nowCellAt (r2pb_stOf hinv_enc).sp unixEpoch ⊢ memRegion fsp 16 :=
          Entails.trans (Entails.of_eq (congrArg (nowCellAt · unixEpoch) hsp_enc))
            (r2_now_to_mem16 fsp)
        have hstk_post :
            stackAt (r2pb_stOf hinv_enc).sp (resStack - runFrame) ⊢
              stackAt fsp (resStack - runFrame) :=
          Entails.of_eq (congrArg (stackAt · (resStack - runFrame)) hsp_enc)
        have hinp_post :
            (g.inp ↦ₛ g.i.stdin) ⊢ (g.inp ↦ₛ inputOf g.i g.c) :=
          Entails.of_eq (congrArg (g.inp ↦ₛ ·) (show g.i.stdin = inputOf g.i g.c by rw [hcall]; rfl))
        have hpeer_split :
            protocolAddressAt A.repAlloc peerG (fsp + 0x320#64) ⊢
              ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion (fsp + 0x330#64) 16 ∗ addrNameHeap A.repAlloc peerG := by
          rw [protocolAddressAt_eq_parts A.repAlloc peerG (fsp + 0x320#64)]
          (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
          exact sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left
              (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                addrUpperAt_entails_memRegion (fsp + 0x330#64) peerG)))
        refine Entails.trans (Entails.of_eq (Q :=
            protocolAddressAt A.repAlloc peerG (fsp + 0x320#64) ∗
              protocolAddressAt A.repAlloc meG (fsp + 0x23b0#64) ∗
              nowCellAt (r2pb_stOf hinv_enc).sp unixEpoch ∗
              stackAt (r2pb_stOf hinv_enc).sp (resStack - runFrame) ∗
              (g.inp ↦ₛ g.i.stdin) ∗
              (lsLogOff ∗ anyHeap ∗ anyHeap) ∗
              (encResAt A.repAlloc (fsp + 0x4d0#64) e ∗ memRegion g.res runResSize ∗
                memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗
                runSaved s0 ∗
                memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
                memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
                r2_localGaps fsp ∗ A.pool lim st_enc s_ret))
          (by dsimp +zetaDelta only [st_enc, fsp, runFsp]; sep_ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono hpeer_split
            (sepConj_mono (r2_protocolAddress_to_mem32_heap A.repAlloc meG (fsp + 0x23b0#64))
              (sepConj_mono hnow_post
                (sepConj_mono hstk_post
                  (sepConj_mono hinp_post (sepConj_mono_left (entails_anyHeap _)))))))
          (Entails.of_eq (by dsimp +zetaDelta only [st_enc, fsp, runFsp]; sep_ac_rfl))
      rw [hpeer_val, hme_val] at hout
      cases e with
      | error err =>
        have hneStore : err ≠ .store () := slotOut_err_ne_store hout
        have hans_err : g.a = some none := by rw [hansLink, hout.2.2]; rfl
        have henv_err : ∀ evs_drop : List AllocEvent, FreeOnlyEvs evs_drop →
            ∃ evs, (R2SendEnv sEnvs S) g (.some meV meG) peerV evs ∧
              M.stepEvents (evs_drop ++ r2pbFreeMePeerEvs meG peerG) st_enc = M.stepEvents evs st :=
          fun evs_drop hfo =>
            ⟨evs_enc ++ (evs_drop ++ r2pbFreeMePeerEvs meG peerG),
              h_err g meV meG peerV peerG fsp evs_enc (evs_drop ++ r2pbFreeMePeerEvs meG peerG)
                hpeer_val henc_ev (FreeOnlyEvs.append hfo (r2pbFreeMePeerEvs_freeOnly meG peerG)),
              (M.stepEvents_append evs_enc _ st).symm⟩
        exact r2pb_err_arm (peerG := peerG) (meG := meG) hh hdrop hdropNeed hextNeed hsub64
          hin_ret hx19_r hx20_r hx21_r hx22_r hx28_r htr_ret hhist_ret hneStore hans_err
          henv_err hrej
      | ok msg =>
        rcases hout.2.2 with ⟨hans_ok, hwr⟩
        cases msg with
        | signalMessage m =>
          have hans_sig : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)) := by
            rw [hansLink, hans_ok]; rfl
          have hfits_cat : FitsEvents M lim st_enc (cliConcat2Events [2#8] m.serialized) :=
            ((fitsEvents_append M lim evs_enc (cliConcat2Events [2#8] m.serialized) st).mp
              (hfits _ (h_sig_cat g meV meG peerV peerG fsp evs_enc g' m
                hpeer_val hans_ok henc_ev))).2
          have henv_sig : ∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f →
              ∃ evs, (R2SendEnv sEnvs S) g (.some meV meG) peerV evs ∧
                M.stepEvents evs_f (M.stepEvents (cliConcat2Events [2#8] m.serialized) st_enc) =
                  M.stepEvents evs st :=
            fun evs_f hfo =>
              ⟨evs_enc ++ (cliConcat2Events [2#8] m.serialized ++ evs_f),
                h_sig_ok g meV meG peerV peerG fsp evs_enc g' m evs_f
                  hpeer_val hans_ok henc_ev hfo,
                by simp [st_enc, AllocCostModel.stepEvents_append]⟩
          exact r2pb_sig_arm (peerG := peerG) (meG := meG) hh hcatNeed hextNeed hsub64 hin_ret
            hx19_r hx20_r hx21_r hx22_r hx26_r hx27_r hx28_r
            htr_ret hhist_ret hans_sig hwr hfits_cat henv_sig hjoin
        | preKeySignalMessage m =>
          have hans_pk : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)) := by
            rw [hansLink, hans_ok]; rfl
          have hfits_cat : FitsEvents M lim st_enc (cliConcat2Events [3#8] m.serialized) :=
            ((fitsEvents_append M lim evs_enc (cliConcat2Events [3#8] m.serialized) st).mp
              (hfits _ (h_pk_cat g meV meG peerV peerG fsp evs_enc g' m
                hpeer_val hans_ok henc_ev))).2
          have henv_pk : ∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f →
              ∃ evs, (R2SendEnv sEnvs S) g (.some meV meG) peerV evs ∧
                M.stepEvents evs_f (M.stepEvents (cliConcat2Events [3#8] m.serialized) st_enc) =
                  M.stepEvents evs st :=
            fun evs_f hfo =>
              ⟨evs_enc ++ (cliConcat2Events [3#8] m.serialized ++ evs_f),
                h_pk_ok g meV meG peerV peerG fsp evs_enc g' m evs_f
                  hpeer_val hans_ok henc_ev hfo,
                by simp [st_enc, AllocCostModel.stepEvents_append]⟩
          exact r2pb_pk_arm (peerG := peerG) (meG := meG) hh hcatNeed hdpkNeed hextNeed hsub64
            hin_ret hx19_r hx20_r hx21_r hx22_r hx26_r hx27_r hx28_r
            htr_ret hhist_ret hans_pk hwr (hpkBound m rfl) hfits_cat henv_pk hjoin


end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
