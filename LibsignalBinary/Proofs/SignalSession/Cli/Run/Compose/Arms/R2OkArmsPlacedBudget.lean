/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

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
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded `signal_session::run` Send Arm Success Paths

Proves the budget-threaded `SignalMessage` (`0x02`, `r2pb_sig_arm`) and `PreKeySignalMessage`
(`0x03`, `r2pb_pk_arm`) post-`encrypt` success arms on Block `579` (`runProgPlaced H`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2OkArmsPlacedBudget

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
   RustCliAllocBudget SeqEnv fitsEvents_append)
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff r2_hold
attribute [local arm64_norm, local wp_norm]
  ProofLib.bv_sub_add_lit BitVec.toNat_zero r2p_vregs_0 r2p_vregs_1 r2p_vregs_2

/-! ## 1. `SignalMessage` (`0x02`) and `PreKeySignalMessage` (`0x03`) Success Arms -/

set_option maxHeartbeats 800000 in
theorem r2pb_sig_arm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {peerG meG : AddrGhost} {g' : StoresGhost}
    {m : SignalMessage} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hcatNeed : 96 + extHookStack ≤ resStack - runFrame)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1308)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hfits_cat : FitsEvents M lim st (cliConcat2Events [2#8] m.serialized))
    (henv_ok : ∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f →
      EnvAt g' ([2#8] ++ m.serialized)
        (M.stepEvents evs_f (M.stepEvents (cliConcat2Events [2#8] m.serialized) st)))
    (hjoin : JoinKPlacedEnv r2p_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (encResAt A.repAlloc (fsp + 0x4d0#64) (.ok (.signalMessage m)) ∗
        addrNameHeap A.repAlloc meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  intro fsp
  let sigTailNoOut : SepProp :=
    addrNameHeap A.repAlloc meG ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
      memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap
  let sigTailNoPool : SepProp :=
    memRegion (fsp + 0x208#64) 24 ∗ stackAt fsp (resStack - runFrame) ∗ sigTailNoOut
  rw [encResAt_ok]; dsimp only [apiEncResultAt]
  have hpull_gm :
      (((fsp + 0x4d0#64) ↦₆₄ ctSignalTag) ∗
          (∃∗ gMsg : SignalMessageGhost,
            signalMessageAt A.repAlloc gMsg ((fsp + 0x4d0#64) + 8#64) m) ∗
          memRegion ((fsp + 0x4d0#64) + 0x80#64) 120) ∗
        (addrNameHeap A.repAlloc meG ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x1750#64) 248 ∗
          memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) =
      ∃∗ gMsg : SignalMessageGhost,
        (((fsp + 0x4d0#64) ↦₆₄ ctSignalTag) ∗
          signalMessageAt A.repAlloc gMsg ((fsp + 0x4d0#64) + 8#64) m ∗
          memRegion ((fsp + 0x4d0#64) + 0x80#64) 120) ∗
        memRegion (fsp + 0x1750#64) 248 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        A.pool lim st s ∗ sigTailNoPool := by
    dsimp only [sigTailNoPool, sigTailNoOut]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    sep_ac_rfl
  rw [hpull_gm]; apply r2pb_sepWPp_exists_left; intro gMsg
  refine sepWPp_weaken_pre
    (sepConj_mono (r2_open_signalMessage A.repAlloc (fsp + 0x4d0#64) gMsg m)
      (sepConj_mono (r2_memRegion248_open (fsp + 0x1750#64))
        (sepConj_mono_left (r2_tag8_open (fsp + 0x2a0#64))))) ?_
  apply r2pb_peel_tc; intro ws; apply r2pb_peel_tc; intro _adPtr; apply r2pb_peel_tc; intro _adLen
  apply r2pb_peel_tc; intro dst0; apply r2pb_peel_tc; intro b2a0; apply r2pb_peel_pure_tc
  rintro ⟨hw0, hw1, hw2, hw4, hw5, hw6, hw7, hw12, hw13, hser_lt, _⟩
  simp only [emp_sepConj, sepConj_assoc]
  rw [← hw4, ← hw5, ← hw2, ← hw1, ← hw12, ← hw13]
  have hcopy_pre :
      r2_words31 (fsp + 0x4d0#64) ws ∗ (gMsg.serPtr ↦ₛ m.serialized) ∗
        r2_boxLive A.repAlloc gMsg.serPtr m.serialized ∗ sliceDeallocX A.repAlloc ws.w4 ws.w5 ∗
        sliceDeallocX A.repAlloc ws.w2 ws.w1 ∗ optSliceDeallocX A.repAlloc ws.w12 ws.w13 ∗
        r2_words31 (fsp + 0x1750#64) dst0 ∗ ((fsp + 0x2a0#64) ↦₈ b2a0) ∗
        memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗ A.pool lim st s ∗ sigTailNoPool =
      r2_words31 (fsp + 0x4d0#64) ws ∗ r2_words31 (fsp + 0x1750#64) dst0 ∗
        A.pool lim st s ∗
        (((fsp + 0x2a0#64) ↦₈ b2a0) ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
          (gMsg.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A.repAlloc gMsg.serPtr m.serialized ∗
          sliceDeallocX A.repAlloc ws.w4 ws.w5 ∗ sliceDeallocX A.repAlloc ws.w2 ws.w1 ∗
          optSliceDeallocX A.repAlloc ws.w12 ws.w13 ∗ sigTailNoPool) := by sep_ac_rfl
  rw [hcopy_pre]
  refine r2pb_step_chk_copy_sig hin hx22 hx26 hx27 hw0
    fun s1 htr1 hfs1 hin1 hx19_1 hx20_1 hx21_1 hx28_1 => ?_
  have htr_s1 : s0.trace <+: s1.trace := htr1 ▸ htr
  have hhist_s1 : RunHistOk g.i s0 s1 :=
    r2p_histOk_of_trace_files hhist htr1 (congrArg FsState.files hfs1)
  have hans_s1 : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)) :=
    r2_ans_of_trace_eq htr1 hans
  have hopen_4d0 :
      r2_words31 (fsp + 0x4d0#64) ws ⊢
        (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
          ((fsp + 0x4d0#64) ↦₆₄ c0) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ c1) ∗
          (((fsp + 0x4d0#64) + 16#64) ↦₆₄ c2) ∗ (((fsp + 0x4d0#64) + 24#64) ↦₆₄ c3)) ∗
        memRegion ((fsp + 0x4d0#64) + 32#64) 216 := by
    refine Entails.trans (r2_words31_to_memRegion248 (fsp + 0x4d0#64) ws) ?_
    rw [ProofLib.memRegion_split (fsp + 0x4d0#64) 32 216 (by decide)]
    exact sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x4d0#64))
  refine sepWPp_weaken_pre (sepConj_mono_left hopen_4d0) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply r2pb_sepWPp_exists_left; intro _c0; apply r2pb_sepWPp_exists_left; intro _c1
  apply r2pb_sepWPp_exists_left; intro _c2; apply r2pb_sepWPp_exists_left; intro _c3
  have hpre_1476 :
      ((fsp + 0x4d0#64) ↦₆₄ _c0) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ _c1) ∗
        (((fsp + 0x4d0#64) + 16#64) ↦₆₄ _c2) ∗ (((fsp + 0x4d0#64) + 24#64) ↦₆₄ _c3) ∗
        memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ r2_words31 (fsp + 0x1750#64) ws ∗
        A.pool lim st s1 ∗ ((fsp + 0x2a0#64) ↦₈ b2a0) ∗
        memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗ (gMsg.serPtr ↦ₛ m.serialized) ∗
        r2_boxLive A.repAlloc gMsg.serPtr m.serialized ∗
        sliceDeallocX A.repAlloc ws.w4 ws.w5 ∗ sliceDeallocX A.repAlloc ws.w2 ws.w1 ∗
        optSliceDeallocX A.repAlloc ws.w12 ws.w13 ∗ sigTailNoPool =
      ((fsp + 0x4d0#64) ↦₆₄ _c0) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ _c1) ∗
        (((fsp + 0x4d0#64) + 16#64) ↦₆₄ _c2) ∗ (((fsp + 0x4d0#64) + 24#64) ↦₆₄ _c3) ∗
        r2_words31 (fsp + 0x1750#64) ws ∗ ((fsp + 0x2a0#64) ↦₈ b2a0) ∗
        (memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
          (gMsg.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A.repAlloc gMsg.serPtr m.serialized ∗
          sliceDeallocX A.repAlloc ws.w4 ws.w5 ∗ sliceDeallocX A.repAlloc ws.w2 ws.w1 ∗
          optSliceDeallocX A.repAlloc ws.w12 ws.w13 ∗ A.pool lim st s1 ∗ sigTailNoPool) := by
    sep_ac_rfl
  rw [hpre_1476]
  have hpc : s1.pc = runPcPlaced 1476 := hin1.pc; change s1.pc = (blkPl_579).base + 1476#64 at hpc
  have hrun1 : s1.status = .Running := hin1.run
  have hsp1_al : s1.spAligned = true := hin1.spAligned_cur
  apply r2pb_seq_lscro_oom (mid := (blkPl_598).base) hin1.inv
  rw [← r2_hold_eq (memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ _)]
  unfold r2_words31; dsimp only [fsp]; rw [← hin1.sp]
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun1])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm2 hinv2 => ?_⟩
    change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv2) _ _ _ _
    clear hpc
    have hsp_cat : (r2pb_stOf hinv2).sp = fsp := by
      dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hin1.sp
    refine sepWPp_weaken_pre
      (P' := memRegion (fsp + 0x208#64) 24 ∗
        ((fsp + 0x4d0#64) ↦₆₄ (fsp + 0x2a0#64)) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ 1#64) ∗
        (((fsp + 0x4d0#64) + 16#64) ↦₆₄ gMsg.serPtr) ∗
        (((fsp + 0x4d0#64) + 24#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
        bytesAt false (fsp + 0x2a0#64) [2#8] ∗
        bytesAt false gMsg.serPtr m.serialized ∗
        A.pool lim st (r2pb_stOf hinv2) ∗ stackAt fsp (resStack - runFrame) ∗
        (memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
          r2_words31 (fsp + 0x1750#64) ws ∗ r2_boxLive A.repAlloc gMsg.serPtr m.serialized ∗
          sliceDeallocX A.repAlloc ws.w4 ws.w5 ∗ sliceDeallocX A.repAlloc ws.w2 ws.w1 ∗
          optSliceDeallocX A.repAlloc ws.w12 ws.w13 ∗ sigTailNoOut))
      (by
        rw [r2_hold_eq, ← A.pool_transport lim st s1 (r2pb_stOf hinv2) hvm2]
        generalize r2pb_stOf hinv2 = s_cat
        unfold r2_words31; dsimp only [fsp, sigTailNoPool, sigTailNoOut]
        rw [hin1.sp, hw6, hw7, bytesAt_false, bytesAt_false, ProofLib.pointsToBytes_singleton]
        (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    have hhist_cat : RunHistOk g.i s0 (r2pb_stOf hinv2) :=
      r2p_histOk_of_trace_files hhist_s1 (by r2pb_eq) (by r2pb_eq)
    have hans_cat : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)) := hans_s1
    let catG : SliceConcat2Ghost :=
      ⟨fsp + 0x208#64, fsp + 0x4d0#64, false, fsp + 0x2a0#64, [2#8], false, gMsg.serPtr,
        m.serialized⟩
    have hcat_call : subroutine_ok (runProgPlaced H) (blkPl_598).base
        (withLsCodeRoLoaded lsmpl (cliConcat2Spec M A lim (resStack - runFrame))) :=
      concat_placed_ok (callerProg := runProgPlaced H) (i := 579) hh (resStack - runFrame)
        hcatNeed hsub64
    refine r2pb_call (catG, st) hcat_call hinv2
      (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun1])
      (by dsimp only [r2pb_stOf]; simp only [wp_norm, arm64_norm]; exact hsp1_al)
      (ret_pc := runPcPlaced 1532) (by r2pb_pc_done)
      (F := memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
        r2_words31 (fsp + 0x1750#64) ws ∗ r2_boxLive A.repAlloc gMsg.serPtr m.serialized ∗
        sliceDeallocX A.repAlloc ws.w4 ws.w5 ∗ sliceDeallocX A.repAlloc ws.w2 ws.w1 ∗
        optSliceDeallocX A.repAlloc ws.w12 ws.w13 ∗ sigTailNoOut) ?_
      (hnext := fun s2 hsteps2 hinv_s2 hpcm2 hrun2 hsp2 hcs2 => ?_)
    · dsimp only [cliConcat2Spec, catG]; rw [sepConj_assoc]; apply Entails.pure_right
      · exact ⟨by dsimp only [r2pb_stOf, fsp]; (try simp only [wp_norm, arm64_norm]); (try rw [hin1.sp]); (try dsimp only [runFsp]); (try bv_omega),
               by dsimp only [r2pb_stOf, fsp]; (try simp only [wp_norm, arm64_norm]); (try rw [hin1.sp]); (try dsimp only [runFsp]); (try bv_omega),
               by r2pb_eq,
               by dsimp only [List.length]; omega,
               hfits_cat⟩
      · rw [hsp_cat]; dsimp only [List.length]; exact Entails.of_eq (by sep_ac_rfl)
    · dsimp only [cliConcat2Spec, catG]; rw [sepConj_assoc]
      apply SepWPp.pure_left; intro htr2
      have hfs2 := r2pb_files_of_trace_eq hh hsteps2 htr2
      have htr_s2 : s0.trace <+: s2.trace := by
        rw [htr2]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr_s1
      have hhist_s2 : RunHistOk g.i s0 s2 := r2p_histOk_of_trace_files hhist_cat htr2 hfs2
      have hans_s2 := r2_ans_of_trace_eq htr2 hans_cat
      have hcs2_r := r2p_cs_regs hcs2
      have hin2 : InRunPlaced r2p_CodeOk s0 s2 1532 :=
        r2p_inRun_mk hin1 hpcm2 hrun2 (hsp2.trans (by r2pb_eq))
          (hcs2_r.2.2.2.2.2.2.2.2.2.2.1.trans (by r2pb_eq)) hinv_s2
          (hcs2_r.2.2.2.2.2.2.2.2.2.2.2.trans (by r2pb_eq))
      have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := by
        rw [hcs2_r.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19_1.trans hx19
      have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := by
        rw [hcs2_r.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx20_1.trans hx20
      have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := by
        rw [hcs2_r.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx21_1.trans hx21
      have hx23_2 : s2.readReg64 (.gpr 23#5) = gMsg.serPtr := by
        rw [hcs2_r.2.2.2.2.1]; dsimp only [r2pb_stOf]; simp only [wp_norm, arm64_norm, hw6]
      have hx24_2 : s2.readReg64 (.gpr 24#5) = BitVec.ofNat 64 m.serialized.length := by
        rw [hcs2_r.2.2.2.2.2.1]; dsimp only [r2pb_stOf]; simp only [wp_norm, arm64_norm, hw7]
      have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr := by
        rw [hcs2_r.2.2.2.2.2.2.2.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx28_1.trans hx28
      clear hcs2 hcs2_r
      let st_cat := M.stepEvents (cliConcat2Events [2#8] m.serialized) st
      refine sepWPp_weaken_pre (P' :=
          r2_words31 (fsp + 0x1750#64) ws ∗ sliceDeallocX A.repAlloc ws.w4 ws.w5 ∗
            A.pool lim st_cat s2 ∗ stackAt fsp (resStack - runFrame) ∗
            (sliceDeallocX A.repAlloc ws.w2 ws.w1 ∗
              optSliceDeallocX A.repAlloc ws.w12 ws.w13 ∗
              sliceDeallocX A.repAlloc gMsg.serPtr (BitVec.ofNat 64 m.serialized.length) ∗
              vecU8 A.repAlloc (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
              memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut)) ?_ ?_
      · refine Entails.trans (Entails.of_eq (Q :=
            (((fsp + 0x4d0#64) ↦₆₄ (fsp + 0x2a0#64)) ∗
                (((fsp + 0x4d0#64) + 8#64) ↦₆₄ BitVec.ofNat 64 ([2#8] : List (BitVec 8)).length) ∗
                (((fsp + 0x4d0#64) + 16#64) ↦₆₄ gMsg.serPtr) ∗
                (((fsp + 0x4d0#64) + 24#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
                memRegion ((fsp + 0x4d0#64) + 32#64) 216) ∗
              (bytesAt false (fsp + 0x2a0#64) [2#8] ∗
                memRegion ((fsp + 0x2a0#64) + 1#64) 7) ∗
              ((gMsg.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A.repAlloc gMsg.serPtr m.serialized) ∗
              (r2_words31 (fsp + 0x1750#64) ws ∗ sliceDeallocX A.repAlloc ws.w4 ws.w5 ∗
                A.pool lim st_cat s2 ∗ stackAt fsp (resStack - runFrame) ∗
                sliceDeallocX A.repAlloc ws.w2 ws.w1 ∗
                optSliceDeallocX A.repAlloc ws.w12 ws.w13 ∗
                vecU8 A.repAlloc (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗ sigTailNoOut)) ?_) ?_
        · rw [bytesAt_false gMsg.serPtr m.serialized, hsp_cat]
          dsimp only [st_cat, fsp, runFsp]; sep_ac_rfl
        · refine Entails.trans
            (sepConj_mono (r2_words4_216_rejoin (fsp + 0x4d0#64) _ _ _ _)
              (sepConj_mono (r2_tag8_close (fsp + 0x2a0#64) 2#8)
                (sepConj_mono_left
                  (r2_boxLive_to_sliceDeallocX A.repAlloc gMsg.serPtr m.serialized (by omega)))))
            (Entails.of_eq (by sep_ac_rfl))
      refine r2pb_sig_free_ct hh hextNeed hsub64 hin2 htr_s2 hhist_s2
        fun s3 htr3 hin3 hcs3 htr_s3 hhist_s3 => ?_
      refine sepWPp_weaken_pre (P' :=
          r2_words31 (fsp + 0x1750#64) ws ∗ sliceDeallocX A.repAlloc ws.w2 ws.w1 ∗
            A.pool lim (M.stepEvents (r2pbFreeSliceEvs ws.w5) st_cat) s3 ∗
            stackAt fsp (resStack - runFrame) ∗
            (optSliceDeallocX A.repAlloc ws.w12 ws.w13 ∗
              sliceDeallocX A.repAlloc gMsg.serPtr (BitVec.ofNat 64 m.serialized.length) ∗
              vecU8 A.repAlloc (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
              memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine r2pb_sig_free_pq hh hextNeed hsub64 hin3 htr_s3 hhist_s3
        fun s4 htr4 hin4 hcs4 htr_s4 hhist_s4 => ?_
      refine sepWPp_weaken_pre (P' :=
          r2_words31 (fsp + 0x1750#64) ws ∗ optSliceDeallocX A.repAlloc ws.w12 ws.w13 ∗
            A.pool lim
              (M.stepEvents (r2pbFreeSliceEvs ws.w1)
                (M.stepEvents (r2pbFreeSliceEvs ws.w5) st_cat)) s4 ∗
            stackAt fsp (resStack - runFrame) ∗
            (sliceDeallocX A.repAlloc gMsg.serPtr (BitVec.ofNat 64 m.serialized.length) ∗
              vecU8 A.repAlloc (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
              memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine r2pb_sig_free_ad hh hextNeed hsub64 hin4 htr_s4 hhist_s4
        fun s5 htr5 hin5 hcs5 htr_s5 hhist_s5 => ?_
      refine sepWPp_weaken_pre (P' :=
          sliceDeallocX A.repAlloc gMsg.serPtr (BitVec.ofNat 64 m.serialized.length) ∗
            A.pool lim
              (M.stepEvents (r2pbFreeOptSliceEvs ws.w12 ws.w13)
                (M.stepEvents (r2pbFreeSliceEvs ws.w1)
                  (M.stepEvents (r2pbFreeSliceEvs ws.w5) st_cat))) s5 ∗
            stackAt fsp (resStack - runFrame) ∗
            (memRegion (fsp + 0x1750#64) 248 ∗
              vecU8 A.repAlloc (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
              memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut))
        (Entails.trans (sepConj_mono_left (r2_words31_to_memRegion248 (fsp + 0x1750#64) ws))
          (Entails.of_eq (by sep_ac_rfl))) ?_
      have hcs25_r := r2p_cs_regs (r2_csm_trans hcs3 (r2_csm_trans hcs4 hcs5))
      have hans_s5 := r2_ans_of_trace_eq (htr5.trans (htr4.trans htr3)) hans_s2
      have hx23_5 : s5.readReg64 (.gpr 23#5) = gMsg.serPtr := hcs25_r.2.2.2.2.1.trans hx23_2
      have hx24_5 : s5.readReg64 (.gpr 24#5) = BitVec.ofNat 64 m.serialized.length :=
        hcs25_r.2.2.2.2.2.1.trans hx24_2
      clear hcs25_r
      refine r2pb_sig_free_ser hh hextNeed hsub64 hin5 hx23_5 hx24_5 htr_s5 hhist_s5
        fun s6 htr6 hin6 hcs6 htr_s6 hhist_s6 => ?_
      have hcs26_r := r2p_cs_regs (r2_csm_trans (r2_csm_trans hcs3 (r2_csm_trans hcs4 hcs5)) hcs6)
      have hx19_6 := hcs26_r.1.trans hx19_2
      have hx20_6 := hcs26_r.2.1.trans hx20_2
      have hx21_6 := hcs26_r.2.2.1.trans hx21_2
      have hx28_6 := hcs26_r.2.2.2.2.2.2.2.2.2.1.trans hx28_2
      clear hcs3 hcs4 hcs5 hcs6 hcs26_r
      let serLen := BitVec.ofNat 64 m.serialized.length
      have hst_free :
          M.stepEvents (r2pbFreeSliceEvs serLen)
            (M.stepEvents (r2pbFreeOptSliceEvs ws.w12 ws.w13)
              (M.stepEvents (r2pbFreeSliceEvs ws.w1)
                (M.stepEvents (r2pbFreeSliceEvs ws.w5) st_cat))) =
          M.stepEvents (r2pbSigFreeEvs ws serLen) st_cat := by
        simp [r2pbSigFreeEvs, r2pbSigFree3Evs,
          AllocCostModel.stepEvents_append, List.append_assoc]
      have henv6 :
          EnvAt g' ([2#8] ++ m.serialized)
            (M.stepEvents (r2pbFreeMePeerEvs meG peerG)
              (M.stepEvents (r2pbSigFreeEvs ws serLen) st_cat)) := by
        rw [← M.stepEvents_append]
        exact henv_ok (r2pbSigFreeEvs ws serLen ++ r2pbFreeMePeerEvs meG peerG)
          (FreeOnlyEvs.append (r2pbSigFreeEvs_freeOnly ws serLen)
            (r2pbFreeMePeerEvs_freeOnly meG peerG))
      refine sepWPp_weaken_pre (P' :=
          addrNameHeap A.repAlloc meG ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
            ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            vecU8 A.repAlloc (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
            stackAt fsp (resStack - runFrame) ∗
            A.pool lim (M.stepEvents (r2pbSigFreeEvs ws serLen) st_cat) s6 ∗ anyHeap)
        (by
          dsimp only [sigTailNoOut, serLen]
          rw [hst_free]
          exact Entails.of_eq (by sep_ac_rfl))
        (r2pb_free_me_peer_join (peerG := peerG) (meG := meG) hh hextNeed hsub64 hin6
          hx19_6 hx20_6 hx21_6 hx28_6
          htr_s6 hhist_s6 (r2_ans_of_trace_eq htr6 hans_s5) hwr henv6 hjoin)
  )

set_option maxHeartbeats 800000 in
theorem r2pb_pk_arm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {peerG meG : AddrGhost} {g' : StoresGhost}
    {m : PreKeySignalMessage} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hcatNeed : 96 + extHookStack ≤ resStack - runFrame)
    (hdpkNeed : 48 + extHookStack ≤ resStack - runFrame)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 1308)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hser42 : m.serialized.length < 2 ^ 42)
    (hfits_cat : FitsEvents M lim st (cliConcat2Events [3#8] m.serialized))
    (henv_ok : ∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f →
      EnvAt g' ([3#8] ++ m.serialized)
        (M.stepEvents evs_f (M.stepEvents (cliConcat2Events [3#8] m.serialized) st)))
    (hjoin : JoinKPlacedEnv r2p_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (encResAt A.repAlloc (fsp + 0x4d0#64) (.ok (.preKeySignalMessage m)) ∗
        addrNameHeap A.repAlloc meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  intro fsp
  let pkTailNoOut : SepProp :=
    addrNameHeap A.repAlloc meG ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
      memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap
  let pkTailNoPool : SepProp :=
    memRegion (fsp + 0x208#64) 24 ∗ stackAt fsp (resStack - runFrame) ∗ pkTailNoOut
  rw [encResAt_ok]; dsimp only [apiEncResultAt]
  have hpull_gp :
      (∃∗ gPk : PreKeyMsgGhost, preKeyMsgAt A.repAlloc gPk (fsp + 0x4d0#64) m) ∗
        (addrNameHeap A.repAlloc meG ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x1750#64) 248 ∗
          memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) =
      ∃∗ gPk : PreKeyMsgGhost,
        preKeyMsgAt A.repAlloc gPk (fsp + 0x4d0#64) m ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x2a0#64) 8 ∗ A.pool lim st s ∗ pkTailNoPool := by
    dsimp only [pkTailNoPool, pkTailNoOut]
    simp only [sepExists_sepConj_left]
    sep_ac_rfl
  rw [hpull_gp]; apply r2pb_sepWPp_exists_left; intro gPk
  refine sepWPp_weaken_pre
    (sepConj_mono (r2_open_preKeyMessage A.repAlloc (fsp + 0x4d0#64) gPk m)
      (sepConj_mono (r2_memRegion248_open (fsp + 0x1750#64))
        (sepConj_mono_left (r2_tag8_open (fsp + 0x2a0#64))))) ?_
  apply r2pb_peel_tc; intro ws; apply r2pb_peel_tc; intro Hrel; apply r2pb_peel_tc; intro dst0
  apply r2pb_peel_tc; intro b2a0; apply r2pb_peel_pure_tc
  rintro ⟨hw0_lt, hw16, hw17, _, _hser_lt, hclose_pk⟩
  simp only [emp_sepConj, sepConj_assoc]
  have hcopy_pre :
      r2_words31 (fsp + 0x4d0#64) ws ∗ (gPk.serPtr ↦ₛ m.serialized) ∗ Hrel ∗
        r2_words31 (fsp + 0x1750#64) dst0 ∗ ((fsp + 0x2a0#64) ↦₈ b2a0) ∗
        memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗ A.pool lim st s ∗ pkTailNoPool =
      r2_words31 (fsp + 0x4d0#64) ws ∗ r2_words31 (fsp + 0x1750#64) dst0 ∗
        A.pool lim st s ∗
        (((fsp + 0x2a0#64) ↦₈ b2a0) ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
          (gPk.serPtr ↦ₛ m.serialized) ∗ Hrel ∗ pkTailNoPool) := by sep_ac_rfl
  rw [hcopy_pre]
  refine r2pb_step_chk_copy_pk hin hx22 hx26 hx27 hw0_lt
    fun s1 htr1 hfs1 hin1 hx19_1 hx20_1 hx21_1 hx28_1 => ?_
  have htr_s1 : s0.trace <+: s1.trace := htr1 ▸ htr
  have hhist_s1 : RunHistOk g.i s0 s1 :=
    r2p_histOk_of_trace_files hhist htr1 (congrArg FsState.files hfs1)
  have hans_s1 : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)) :=
    r2_ans_of_trace_eq htr1 hans
  have hopen_4d0 :
      r2_words31 (fsp + 0x4d0#64) ws ⊢
        (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
          ((fsp + 0x4d0#64) ↦₆₄ c0) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ c1) ∗
          (((fsp + 0x4d0#64) + 16#64) ↦₆₄ c2) ∗ (((fsp + 0x4d0#64) + 24#64) ↦₆₄ c3)) ∗
        memRegion ((fsp + 0x4d0#64) + 32#64) 216 := by
    refine Entails.trans (r2_words31_to_memRegion248 (fsp + 0x4d0#64) ws) ?_
    rw [ProofLib.memRegion_split (fsp + 0x4d0#64) 32 216 (by decide)]
    exact sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x4d0#64))
  refine sepWPp_weaken_pre (sepConj_mono_left hopen_4d0) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply r2pb_sepWPp_exists_left; intro _c0; apply r2pb_sepWPp_exists_left; intro _c1
  apply r2pb_sepWPp_exists_left; intro _c2; apply r2pb_sepWPp_exists_left; intro _c3
  have hpre_3792 :
      ((fsp + 0x4d0#64) ↦₆₄ _c0) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ _c1) ∗
        (((fsp + 0x4d0#64) + 16#64) ↦₆₄ _c2) ∗ (((fsp + 0x4d0#64) + 24#64) ↦₆₄ _c3) ∗
        memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ r2_words31 (fsp + 0x1750#64) ws ∗
        A.pool lim st s1 ∗ ((fsp + 0x2a0#64) ↦₈ b2a0) ∗
        memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗ (gPk.serPtr ↦ₛ m.serialized) ∗ Hrel ∗
        pkTailNoPool =
      ((fsp + 0x4d0#64) ↦₆₄ _c0) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ _c1) ∗
        (((fsp + 0x4d0#64) + 16#64) ↦₆₄ _c2) ∗ (((fsp + 0x4d0#64) + 24#64) ↦₆₄ _c3) ∗
        r2_words31 (fsp + 0x1750#64) ws ∗ ((fsp + 0x2a0#64) ↦₈ b2a0) ∗
        (memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
          (gPk.serPtr ↦ₛ m.serialized) ∗ Hrel ∗ A.pool lim st s1 ∗ pkTailNoPool) := by
    sep_ac_rfl
  rw [hpre_3792]
  have hpc : s1.pc = runPcPlaced 3792 := hin1.pc; change s1.pc = (blkPl_579).base + 3792#64 at hpc
  have hrun1 : s1.status = .Running := hin1.run
  have hsp1_al : s1.spAligned = true := hin1.spAligned_cur
  apply r2pb_seq_lscro_oom (mid := (blkPl_598).base) hin1.inv
  rw [← r2_hold_eq (memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ _)]
  unfold r2_words31; dsimp only [fsp]; rw [← hin1.sp]
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun1])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm2 hinv2 => ?_⟩
    change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv2) _ _ _ _
    clear hpc
    have hsp_cat : (r2pb_stOf hinv2).sp = fsp := by
      dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hin1.sp
    refine sepWPp_weaken_pre
      (P' := memRegion (fsp + 0x208#64) 24 ∗
        ((fsp + 0x4d0#64) ↦₆₄ (fsp + 0x2a0#64)) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ 1#64) ∗
        (((fsp + 0x4d0#64) + 16#64) ↦₆₄ gPk.serPtr) ∗
        (((fsp + 0x4d0#64) + 24#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
        bytesAt false (fsp + 0x2a0#64) [3#8] ∗
        bytesAt false gPk.serPtr m.serialized ∗
        A.pool lim st (r2pb_stOf hinv2) ∗ stackAt fsp (resStack - runFrame) ∗
        (memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
          r2_words31 (fsp + 0x1750#64) ws ∗ Hrel ∗ pkTailNoOut))
      (by
        rw [r2_hold_eq, ← A.pool_transport lim st s1 (r2pb_stOf hinv2) hvm2]
        generalize r2pb_stOf hinv2 = s_cat
        unfold r2_words31; dsimp only [fsp, pkTailNoPool, pkTailNoOut]
        rw [hin1.sp, hw16, hw17, bytesAt_false, bytesAt_false, ProofLib.pointsToBytes_singleton]
        (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    have hhist_cat : RunHistOk g.i s0 (r2pb_stOf hinv2) :=
      r2p_histOk_of_trace_files hhist_s1 (by r2pb_eq) (by r2pb_eq)
    have hans_cat : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)) := hans_s1
    let catG : SliceConcat2Ghost :=
      ⟨fsp + 0x208#64, fsp + 0x4d0#64, false, fsp + 0x2a0#64, [3#8], false, gPk.serPtr,
        m.serialized⟩
    have hcat_call : subroutine_ok (runProgPlaced H) (blkPl_598).base
        (withLsCodeRoLoaded lsmpl (cliConcat2Spec M A lim (resStack - runFrame))) :=
      concat_placed_ok (callerProg := runProgPlaced H) (i := 579) hh (resStack - runFrame)
        hcatNeed hsub64
    refine r2pb_call (catG, st) hcat_call hinv2
      (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun1])
      (by dsimp only [r2pb_stOf]; simp only [wp_norm, arm64_norm]; exact hsp1_al)
      (ret_pc := runPcPlaced 3848) (by r2pb_pc_done)
      (F := memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
        r2_words31 (fsp + 0x1750#64) ws ∗ Hrel ∗ pkTailNoOut) ?_
      (hnext := fun s2 hsteps2 hinv_s2 hpcm2 hrun2 hsp2 hcs2 => ?_)
    · dsimp only [cliConcat2Spec, catG]; rw [sepConj_assoc]; apply Entails.pure_right
      · exact ⟨by dsimp only [r2pb_stOf, fsp]; (try simp only [wp_norm, arm64_norm]); (try rw [hin1.sp]); (try dsimp only [runFsp]); (try bv_omega),
               by dsimp only [r2pb_stOf, fsp]; (try simp only [wp_norm, arm64_norm]); (try rw [hin1.sp]); (try dsimp only [runFsp]); (try bv_omega),
               by r2pb_eq,
               by dsimp only [List.length]; omega,
               hfits_cat⟩
      · rw [hsp_cat]; dsimp only [List.length]; exact Entails.of_eq (by sep_ac_rfl)
    · dsimp only [cliConcat2Spec, catG]; rw [sepConj_assoc]
      apply SepWPp.pure_left; intro htr2
      have hfs2 := r2pb_files_of_trace_eq hh hsteps2 htr2
      have htr_s2 : s0.trace <+: s2.trace := by
        rw [htr2]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr_s1
      have hhist_s2 : RunHistOk g.i s0 s2 := r2p_histOk_of_trace_files hhist_cat htr2 hfs2
      have hans_s2 := r2_ans_of_trace_eq htr2 hans_cat
      have hcs2_r := r2p_cs_regs hcs2
      have hin2 : InRunPlaced r2p_CodeOk s0 s2 3848 :=
        r2p_inRun_mk hin1 hpcm2 hrun2 (hsp2.trans (by r2pb_eq))
          (hcs2_r.2.2.2.2.2.2.2.2.2.2.1.trans (by r2pb_eq)) hinv_s2
          (hcs2_r.2.2.2.2.2.2.2.2.2.2.2.trans (by r2pb_eq))
      have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := by
        rw [hcs2_r.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19_1.trans hx19
      have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := by
        rw [hcs2_r.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx20_1.trans hx20
      have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := by
        rw [hcs2_r.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx21_1.trans hx21
      have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr := by
        rw [hcs2_r.2.2.2.2.2.2.2.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx28_1.trans hx28
      clear hcs2 hcs2_r
      let st_cat := M.stepEvents (cliConcat2Events [3#8] m.serialized) st
      refine sepWPp_weaken_pre (P' :=
          preKeyMsgAt A.repAlloc gPk (fsp + 0x1750#64) m ∗
            A.pool lim st_cat s2 ∗ stackAt fsp (resStack - runFrame) ∗
            (vecU8 A.repAlloc (fsp + 0x208#64) ([3#8] ++ m.serialized) ∗
              memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗ pkTailNoOut)) ?_ ?_
      · refine Entails.trans (Entails.of_eq (Q :=
            (r2_words31 (fsp + 0x1750#64) ws ∗ (gPk.serPtr ↦ₛ m.serialized) ∗ Hrel) ∗
              (((fsp + 0x4d0#64) ↦₆₄ (fsp + 0x2a0#64)) ∗
                (((fsp + 0x4d0#64) + 8#64) ↦₆₄ BitVec.ofNat 64 ([3#8] : List (BitVec 8)).length) ∗
                (((fsp + 0x4d0#64) + 16#64) ↦₆₄ gPk.serPtr) ∗
                (((fsp + 0x4d0#64) + 24#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
                memRegion ((fsp + 0x4d0#64) + 32#64) 216) ∗
              (bytesAt false (fsp + 0x2a0#64) [3#8] ∗
                memRegion ((fsp + 0x2a0#64) + 1#64) 7) ∗
              (A.pool lim st_cat s2 ∗ stackAt fsp (resStack - runFrame) ∗
                vecU8 A.repAlloc (fsp + 0x208#64) ([3#8] ++ m.serialized) ∗ pkTailNoOut)) ?_) ?_
        · rw [bytesAt_false gPk.serPtr m.serialized, hsp_cat]
          dsimp only [st_cat, fsp, runFsp]; sep_ac_rfl
        · refine Entails.trans
            (sepConj_mono (hclose_pk (fsp + 0x1750#64))
              (sepConj_mono (r2_words4_216_rejoin (fsp + 0x4d0#64) _ _ _ _)
                (sepConj_mono_left (r2_tag8_close (fsp + 0x2a0#64) 3#8))))
            (Entails.of_eq (by sep_ac_rfl))
      have hpc : s2.pc = runPcPlaced 3848 := hin2.pc; change s2.pc = (blkPl_579).base + 3848#64 at hpc
      have hsp2_al : s2.spAligned = true := hin2.spAligned_cur
      apply r2pb_seq_lscro_oom (mid := (blkPl_555).base) hin2.inv
      rw [← r2_hold_eq (preKeyMsgAt A.repAlloc gPk (fsp + 0x1750#64) m ∗ _)]
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun2])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm3 hinv3 => ?_⟩
        change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv3) _ _ _ _
        rw [r2_hold_eq]; clear hpc
        rw [← A.pool_transport lim st_cat s2 (r2pb_stOf hinv3) hvm3]
        have hsp_dpk : (r2pb_stOf hinv3).sp = fsp := by
          dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hin2.sp
        have hdpk_call :=
          dropPreKeyMsg_placed_ok (callerProg := runProgPlaced H) (i := 579) hh
            (resStack - runFrame)
            (Nat.le_trans (by decide : 32 + extHookStack ≤ 48 + extHookStack) hdpkNeed) hsub64
        refine r2pb_call (DropPreKeyMsgGhost.mk (fsp + 0x1750#64) gPk m, st_cat) hdpk_call hinv3
          (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun2])
          (by dsimp only [r2pb_stOf]; simp only [wp_norm, arm64_norm]; exact hsp2_al)
          (ret_pc := runPcPlaced 3860) (by r2pb_pc_done)
          (F := vecU8 A.repAlloc (fsp + 0x208#64) ([3#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗ pkTailNoOut) ?_
          (hnext := fun s3 hsteps3 hinv_s3 hpcm3 hrun3 hsp3 hcs3 => ?_)
        · dsimp only [dropPreKeyMsgSpec]; rw [sepConj_assoc]
          refine Entails.pure_right
            ⟨by dsimp only [r2pb_stOf, fsp]; (try simp only [wp_norm, arm64_norm]); (try rw [hin2.sp]),
             by dsimp only [r2pb_stOf]; simp (config := { decide := true }) only [wp_norm, arm64_norm, runPcPlaced_eq]⟩ ?_
          rw [hsp_dpk]; exact Entails.of_eq (by sep_ac_rfl)
        · dsimp only [dropPreKeyMsgSpec]
          apply r2pb_peel_tc; intro evs_dpk
          apply r2pb_peel_pure_tc; rintro ⟨htr3, hfo_dpk_raw⟩
          simp only [emp_sepConj, sepConj_assoc]
          have hfo_dpk : FreeOnlyEvs evs_dpk := r2pb_freeOnlyEvs_of_forall hfo_dpk_raw
          have hfs3 := r2pb_files_of_trace_eq hh hsteps3 htr3
          have htr_s3 : s0.trace <+: s3.trace := by
            rw [htr3]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr_s2
          have hhist_s3 : RunHistOk g.i s0 s3 :=
            r2p_histOk_of_trace_files
              (r2p_histOk_of_trace_files hhist_s2 (by r2pb_eq) (by r2pb_eq)) htr3 hfs3
          have hans_s3 := r2_ans_of_trace_eq htr3 hans_s2
          have hcs3_r := r2p_cs_regs hcs3
          have hin3 : InRunPlaced r2p_CodeOk s0 s3 3860 :=
            r2p_inRun_mk hin2 hpcm3 hrun3 (hsp3.trans (by r2pb_eq))
              (hcs3_r.2.2.2.2.2.2.2.2.2.2.1.trans (by r2pb_eq)) hinv_s3
              (hcs3_r.2.2.2.2.2.2.2.2.2.2.2.trans (by r2pb_eq))
          have hx19_3 : s3.readReg64 (.gpr 19#5) = g.stores := by
            rw [hcs3_r.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19_2
          have hx20_3 : s3.readReg64 (.gpr 20#5) = g.res := by
            rw [hcs3_r.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx20_2
          have hx21_3 : s3.readReg64 (.gpr 21#5) = meG.name.cap := by
            rw [hcs3_r.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx21_2
          have hx28_3 : s3.readReg64 (.gpr 28#5) = meG.name.ptr := by
            rw [hcs3_r.2.2.2.2.2.2.2.2.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx28_2
          clear hcs3 hcs3_r
          have hpc : s3.pc = runPcPlaced 3860 := hin3.pc; change s3.pc = (blkPl_579).base + 3860#64 at hpc
          apply r2pb_seq_lscro_oom (mid := runPcPlaced 3940) hin3.inv
          rw [← r2_hold_eq (memRegion (fsp + 0x1750#64) 248 ∗ _), runPcPlaced_eq]
          dsimp only [runProgPlaced, lsProg_579]
          by_vm_open (
            wp_steps
            refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun3])
              ⟨by simp only [wp_norm, arm64_norm], fun hvm4 hinv4 => ?_⟩
            change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv4) _ _ _ _
            rw [r2_hold_eq]; clear hpc
            rw [← A.pool_transport lim (M.stepEvents evs_dpk st_cat) s3 (r2pb_stOf hinv4) hvm4]
            have hin4 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv4) 3940 :=
              r2p_inRun_mk hin3 (by r2pb_pc_done)
                (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun3])
                (by r2pb_eq) (by r2pb_eq) hinv4 (by r2pb_eq)
            have henv4 :
                EnvAt g' ([3#8] ++ m.serialized)
                  (M.stepEvents (r2pbFreeMePeerEvs meG peerG) (M.stepEvents evs_dpk st_cat)) := by
              rw [← M.stepEvents_append]
              exact henv_ok (evs_dpk ++ r2pbFreeMePeerEvs meG peerG)
                (FreeOnlyEvs.append hfo_dpk (r2pbFreeMePeerEvs_freeOnly meG peerG))
            refine sepWPp_weaken_pre (P' :=
                addrNameHeap A.repAlloc meG ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                  storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                  addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
                  ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
                  memRegion (fsp + 0x330#64) 16 ∗ memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
                  vecU8 A.repAlloc (fsp + 0x208#64) ([3#8] ++ m.serialized) ∗
                  memRegion (fsp + 0x2a0#64) 8 ∗
                  memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
                  memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
                  stackAt fsp (resStack - runFrame) ∗
                  A.pool lim (M.stepEvents evs_dpk st_cat) (r2pb_stOf hinv4) ∗ anyHeap)
              (by
                rw [hsp_dpk]
                dsimp only [pkTailNoOut, fsp, runFsp]
                exact Entails.of_eq (by sep_ac_rfl))
              (r2pb_free_me_peer_join (peerG := peerG) (meG := meG) hh hextNeed hsub64 hin4
                (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19_3)
                (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx20_3)
                (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx21_3)
                (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx28_3)
                (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr_s3)
                (r2p_histOk_of_trace_files hhist_s3 (by r2pb_eq) (by r2pb_eq))
                hans_s3 hwr henv4 hjoin)
          )
      )
  )


end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2OkArmsPlacedBudget
