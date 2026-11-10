/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Msg
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB5PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlaced
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsBPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsCPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5AuxPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlaced
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5V1PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2TransPlaced
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsAPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrBPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrCPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch

/-!
# Budget-Threaded Stage P2 Bad-KEM Rejection Arms

Composes the budget-threaded Stage P2 store-error and bad-KEM rejection arms under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (p2_a90_err45_to_288 p2_cells8_a90_to_cells6_2 p2_coro398_bytes_words4_entails_96 p2_coro4b0_byte_bytes_entails_65 p2_coro658_298_rejoin p2_drop_frame_mid p2_fp80_to_memRegion9 p2_processPrekeyActive10At_eq p2_sessionRecordEmptyHeaderAt_eq p2_sp3b0_48_split_8_40 p2_sp3e0_arm5_to_368 p2_sp80_11words_entails_88 p2_stack_split_alloc p2_stack_split_dropSs3 stageP1EntryPlaced stageP1ProgPlaced)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (sessionAt_entails_sessionStateAt)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput WellSizedAcceptKeysInput bytesToBv8)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved decryptPrekeySavedRegsAt opkPresentTag opkUnusedFieldAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (KyberPreKeyStoreSpec LibsignalCodeRoLoaded PreKeyStoreSpec SignedPreKeyStoreSpec speWordsAt)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (dropSessionStructureLocal2Stack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost protocolAddressAt)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsCPlacedBudget (p2Arm5ErrEvents)

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsPlacedBudget

open Arm64 ProofLib SepProp ProofLib.ProgramReflection ProofLib.Variant
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (dropSessionStructureLocal2Spec)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  signalMessageRestVerAt signalMessageAt_eq_ver_sep memRegion_4_eq_exists_pointsTo32
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To4Env P2Sub1To4OkEnv P2Sub1To3Arm1Env P2Sub1To3Arm2Env P2Sub1To4Arm3Env
  stageP2_sub1_to_4_kits_ext_placed_ofEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlacedBudget (
  p2Sub5FramePlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget (
  p2_entails_frame_v1 p2_call_nopanic_rocl_sub5 p2_bind_sepWP_steps_cro_sub5_state
  isSameAccountDistinctSpec_to_at_placed p2_stageP2bStack_le_bobV1 p2_isSameAccount_le_bobV1
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2V1Arm4Env P2V1Arm5EnvOfAcceptErr
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsAPlacedBudget (
  p2OverSub5FramePlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrBPlacedBudget (
  p2_over_arm4_err_hooks_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrCPlacedBudget (
  p2_over_arm5_err_hooks_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2PlacedBudget (
  P2OverSub1To3Arm1Env P2OverSub1To3Arm2Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget (
  P2OverSub1To4Env P2OverSub1To4OkEnv P2OverSub1To4Arm3Env
  stageP2_over_sub1_to_4_kits_ext_placed_ofEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget (
  P2OverV1Arm4Env P2OverV1Arm5EnvOfAcceptErr
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget (
  AcceptBadKemEnv initializeBobSessionBadKemErrOwnedInnerPlacedSpec
  initializeBobSessionBadKemErrOwnedPlacedSpec initializeBobSessionBadKemErrOwnedFrozenPlacedSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget (
  p2BadKemSub1To4Frame p2BadKemErrFrameAtPlaced stageP2BadKemPreAtPlaced
  stageP2OverBadKemPreAtPlaced p2_initBobBadKemErrOwnedAt_unpack
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget (
  p2_badKem_entry_to_sub1To4_placed p2_over_badKem_entry_to_sub1To4_placed
  p2_badKem_sub4_to_sub5_placed p2_over_badKem_sub4_to_sub5_placed
  p2_badKem_arm5_err_payload_pull_placed
  p2_badKem_arm1_entails_placed p2_badKem_arm2_entails_placed p2_badKem_arm3_entails_placed
)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem eq_of_sep_emp {P Q : SepProp} (h : P = Q ∗ emp) : P = Q :=
  h.trans (sepConj_emp Q)

export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsAPlacedBudget (mkBadKemHdr hdrOpkIdBv?_mkBadKemHdr mkBadKemHdr_ikAPk_len mkBadKemHdr_ekAPk_len)
export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsAPlacedBudget (mkBadKemHdr_kemCt_len bytesToBv8_mkBadKemHdr_ekAPk bytesToBv8_mkBadKemHdr_ikAPk boxU8_payload_split_d3)
export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsAPlacedBudget (badKemMsgRemInnerAt badKemMsgRemInnerAt_dup_kyber preKeyMsgAt_unpack_badKem p2BadKemMsgFields_reassemble)
export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsAPlacedBudget (p2_badKem_arm4_hooks_placed_ok p2_over_badKem_arm4_hooks_placed_ok)

private theorem p2_finish_err_arm_drop_state {prog : Program} {ret : BitVec 64} {s : State}
    {P ArmPre Rest Drop : SepProp} {ArmOut Keep : State → SepProp}
    {Q Qp : State → SepProp → Prop} {Φ : State → Prop}
    (hArm : SepWPp prog ret s ArmPre
      (fun sf P_f => sf.trace = s.trace ∧ (P_f ⊢ ArmOut sf) ∧ Φ sf)
      (fun _ _ => False))
    (hP : P = ArmPre ∗ Rest)
    (hSplit : ∀ sf : State, ArmOut sf ∗ Rest ⊢ Drop ∗ Keep sf)
    (hQ : ∀ sf P_f,
      Steps prog s sf → sf.pc = ret → sf.status = .Running →
      sf.trace = s.trace → (P_f ⊢ Keep sf) → Φ sf → Q sf P_f) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps,
      ⟨hpcf, hrunf, P_f, hmf, htrf, hentf, hΦ⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hArm (Rest ∗ R) hm hL
  · have hmf1 : sf.mem ⊨ (ArmOut sf ∗ Rest) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hentf) hmf
    have hmf2 : sf.mem ⊨ Drop ∗ (Keep sf ∗ R) := by
      rw [← sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left (hSplit sf)) hmf1
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, Keep sf, Satisfies.of_sep_right hmf2,
      hQ sf (Keep sf) hsteps hpcf hrunf htrf (Entails.refl _) hΦ⟩⟩
  · exact False.elim hpan
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 800000 in

private theorem p2_finish_err_arm_evs_drop {prog : Program} {ret : BitVec 64} {s : State}
    {P ArmPre Rest Drop : SepProp}
    {ArmOut Keep : List AllocEvent → State → SepProp}
    {Φ : List AllocEvent → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hArm : SepWPp prog ret s ArmPre
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ sf.trace = s.trace ∧ (P_f ⊢ ArmOut evs sf) ∧ Φ evs sf)
      (fun _ _ => False))
    (hP : P = ArmPre ∗ Rest)
    (hSplit : ∀ evs sf, ArmOut evs sf ∗ Rest ⊢ Drop ∗ Keep evs sf)
    (hQ : ∀ sf P_f evs,
      FreeOnlyEvs evs →
      Steps prog s sf → sf.pc = ret → sf.status = .Running →
      sf.trace = s.trace → (P_f ⊢ Keep evs sf) → Φ evs sf → Q sf P_f) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps,
      ⟨hpcf, hrunf, P_f, hmf, evs, hfree, htrf, hentf, hΦ⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hArm (Rest ∗ R) hm hL
  · have hmf1 : sf.mem ⊨ (ArmOut evs sf ∗ Rest) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hentf) hmf
    have hmf2 : sf.mem ⊨ Drop ∗ (Keep evs sf ∗ R) := by
      rw [← sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left (hSplit evs sf)) hmf1
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, Keep evs sf, Satisfies.of_sep_right hmf2,
      hQ sf (Keep evs sf) evs hfree hsteps hpcf hrunf htrf (Entails.refl _) hΦ⟩⟩
  · exact False.elim hpan
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 800000 in
theorem p2_badKem_arm5_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (hH : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.StageP2ClosureHooksPlaced A lim ext)
    (s0 sf5 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90
     errTag w2 w3 w4 w5 w6 v_a8' v_b8' v_d0' u_b90' : BitVec 64)
    (inp : AcceptKeysInput) (ctBytes : List (BitVec 8)) (ikBPk spkBPk : List UInt8)
    (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 b_b98' : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp)
    (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hkyberPub_len : kyberPubBytes.length = 1568)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (herr_ne_ok : errTag ≠ 0xfffffffffffffffe#64)
    (herr_ne_pend : errTag ≠ 0xfffffffffffffffd#64)
    (hstk_alloc : allocHookStack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hCode : LibsignalCodeRoLoaded lsmpl sf5.mem)
    (hpc : sf5.pc = stageP1EntryPlaced + 0x125c#64)
    (hrun : sf5.status = .Running) (hsp : sf5.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : sf5.readReg64 .x19 = coroPtr)
    (hx25 : sf5.readReg64 .x25 = sp + 0x210#64)
    (hx28 : sf5.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs sf5 = calleeSavedVRegs s0)
    (hCont : ∀ (sf : State) (P_f : SepProp),
      Steps (stageP1ProgPlaced ext) sf5 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = sf5.trace → sf.sp = sp + 0xcd0#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
        spkKit.storeAt spkStorePtr stSpk' ∗
        kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗
        ikit.identityAt idStorePtr stId ∗
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim (M.stepEvents (p2Arm5ErrEvents 0#64) st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 inp.hdr ctBytes msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf5
      (((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
       memRegion (sp + 0x418#64) 288 ∗
       bobParamsBadKemFieldsAt (coroPtr + 0x658#64) skBuf (msgPtr + 0x90#64) ctBufPtr
         (coroPtr + 0x398#64) inp ctBytes ikBPk spkBPk 0#8 ∗
       ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       cells (coroPtr + 0x4f8#64) 2 ∗
       ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
       ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
       ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
       opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
       memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
       ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       protocolAddressAt A.repAlloc gMe localAddrPtr ∗
       protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
       memRegion (sp + 0x3c8#64) 7 ∗ cells (sp + 0x560#64) 4 ∗
       cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
       cells (sp + 0xa90#64) 8 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ anyHeap ∗ A.pool lim st sf5 ∗ stackAt sp stk ∗
       p2Sub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
         remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
         pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
         msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
         stSpk' stKpk' stPk' Frame)
      Q Qp := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  refine p2_drop_frame_mid (Drop := anyHeap) (by sep_focus) ?_
  dsimp only [p2Sub5FramePlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Sub5FramePlaced,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame
    (p2_bobParamsBadKemFieldsAt_err_weaken coroPtr msgPtr skBuf ctBufPtr inp ctBytes ikBPk spkBPk hwell)
    (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame
    (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len)
    (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (p2_fp80_to_memRegion9 fp u_b90' b_b98') (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq (p2_cells8_a90_to_cells6_2 sp)) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq (p2_stack_split_alloc sp stk hstk_alloc hstk64))
    (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_eq coroPtr))
    (by sep_focus) ?_
  have hif0 : (if (0#64 : BitVec 64) = 0 then emp
      else A.live 8#64 ((0#64 : BitVec 64).toNat * 24) 8 ∗
           memRegion 8#64 ((0#64 : BitVec 64).toNat * 24)) = emp := by simp
  have harm5 := LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsCPlacedBudget.p2_arm5_err_hooks_placed_ok (st := st) (Qp := fun _ _ => False) hH s0 sf5
    sp coroPtr outPtr 0#64 8#64 pkBuf skBuf
    errTag w2 w3 w4 w5 w6 u_88 v_a8' v_b8' v_d0'
    b_2c0 b_390 b_4f2 (by decide) herr_ne_pend herr_ne_ok
    hCode hsp hpc hrun (hsp ▸ hsp_align)
    hx19 hx25 hx28 hvregs
  rw [hif0, emp_sepConj] at harm5
  refine p2_finish_err_arm_drop_state (Drop := emp) harm5 (by sep_focus) (fun sf => ?_)
    (fun sf P_f hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hinvf, _hlive⟩ =>
      hCont sf P_f hst hpcf hrunf htrf hspf hcsf hvregsf hinvf hent)
  rw [emp_sepConj]
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced, p2CoroScratchTailAt, p2BadKemMsgFieldsAt]
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (Entails.of_eq (p2_stack_split_alloc sp stk hstk_alloc hstk64).symm) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (p2_sp3e0_arm5_to_368 sp errTag w2 w3 w4 w5 w6) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_48_split_8_40 sp).symm) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1 (Entails.of_eq (p2_a90_err45_to_288 sp)) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 errTag v90 (coroPtr + 0x398#64)
      (coroPtr + 0x4f2#64) w5 (coroPtr + 0x390#64) w3 ctxPtr outPtr w4) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (p2_coro658_298_rejoin coroPtr msgPtr pkBuf skBuf inp ikBPk spkBPk opkPkBytes opkSkBytes
      hwell hikBPk_len hspkBPk_len hopkPk_len hopkSk_len hopkSk_eq) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (p2_coro398_bytes_words4_entails_96 coroPtr (bytesToBv8 spkBPk) (bytesToBv8 inp.spkBSk)
      pkBuf 0x620#64 skBuf 0xc60#64
      (by simp [bytesToBv8, hspkBPk_len]) (by simp [bytesToBv8, hwell.2.2.1]))
    (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
    (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (pointsTo64_entails_memRegion (coroPtr + 0x488#64) (msgPtr + 0x90#64)) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (p2_coro4b0_byte_bytes_entails_65 coroPtr (opkPresentTag inp.opkBSk?) opkPkBytes opkSkBytes
      hopkPk_len hopkSk_len) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (Entails.of_eq (p2_coro4f8_2cells_328_eq_344 coroPtr)) (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 800000 in
theorem p2_over_badKem_arm5_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (hH : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (s0 sf5 : State) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     pkBuf skBuf v_330 v_388 u_80 u_88 v90
     errTag w2 w3 w4 w5 w6 v_a8' v_b8' v_d0' u_b90' : BitVec 64)
    (inp : AcceptKeysInput) (ctBytes : List (BitVec 8)) (ikBPk spkBPk : List UInt8)
    (kyberPubBytes opkPkBytes opkSkBytes : List (BitVec 8))
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (msgVerByte b_2c0 b_390 b_4f2 b_b98' : BitVec 8)
    (stSpk' : spkKit.SpkState) (stKpk' : kpkKit.KpkState)
    (stPk' : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp)
    (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hkyberPub_len : kyberPubBytes.length = 1568)
    (hopkPk_len : opkPkBytes.length = 32) (hopkSk_len : opkSkBytes.length = 32)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (herr_ne_ok : errTag ≠ 0xfffffffffffffffe#64)
    (herr_ne_pend : errTag ≠ 0xfffffffffffffffd#64)
    (hstk_drop : dropSessionStructureLocal2Stack ≤ stk) (hstk_lt : stk ≤ sp.toNat)
    (hCode : LibsignalCodeRoLoaded lsmpl sf5.mem)
    (hpc : sf5.pc = stageP1EntryPlaced + 0x125c#64)
    (hrun : sf5.status = .Running) (hsp : sf5.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : sf5.readReg64 .x19 = coroPtr)
    (hx25 : sf5.readReg64 .x25 = sp + 0x210#64)
    (hx28 : sf5.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs sf5 = calleeSavedVRegs s0)
    (hCont : ∀ (sf : State) (P_f : SepProp) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      Steps (stageP1ProgPlaced ext) sf5 sf →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = sf5.trace → sf.sp = sp + 0xcd0#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
        spkKit.storeAt spkStorePtr stSpk' ∗
        kpkKit.storeAt kyberStorePtr stKpk' ∗
        pkKit.storeAt preKeyStorePtr stPk' ∗
        ikit.identityAt idStorePtr stId ∗
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 inp.hdr ctBytes msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf5
      (((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
       memRegion (sp + 0x418#64) 288 ∗
       bobParamsBadKemFieldsAt (coroPtr + 0x658#64) skBuf (msgPtr + 0x90#64) ctBufPtr
         (coroPtr + 0x398#64) inp ctBytes ikBPk spkBPk 0#8 ∗
       ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       cells (coroPtr + 0x4f8#64) 2 ∗
       ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
       ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
       ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
       opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
       memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
       ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       protocolAddressAt A.repAlloc gMe localAddrPtr ∗
       protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
       memRegion (sp + 0x3c8#64) 7 ∗ cells (sp + 0x560#64) 4 ∗
       cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
       cells (sp + 0xa90#64) 8 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ anyHeap ∗ A.pool lim st sf5 ∗ stackAt sp stk ∗
       p2OverSub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
         remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
         pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
         msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
         stSpk' stKpk' stPk' g recG sess Frame)
      Q Qp := by
  have hstk64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat := Nat.le_trans hstk_drop hstk_lt
  refine p2_drop_frame_mid (Drop := anyHeap) (by sep_focus) ?_
  dsimp only [p2OverSub5FramePlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2OverSub5FramePlaced]
  rw [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame
    (sessionAt_entails_sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG sess) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame
    (p2_bobParamsBadKemFieldsAt_err_weaken coroPtr msgPtr skBuf ctBufPtr inp ctBytes ikBPk spkBPk hwell)
    (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame
    (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyberPub_len)
    (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (p2_fp80_to_memRegion9 fp u_b90' b_b98') (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq (p2_cells8_a90_to_cells6_2 sp)) (by sep_focus) ?_
  refine CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.weaken_frame (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64))
    (by sep_focus) ?_
  have harm5 := p2_over_arm5_err_hooks_placed_ok (st := st) (Qp := fun _ _ => False)
    hH hDropSs3 s0 sf5
    sp coroPtr outPtr pkBuf skBuf
    errTag w2 w3 w4 w5 w6 u_88 v_a8' v_b8' v_d0'
    b_2c0 b_390 b_4f2 g recG sess.state herr_ne_pend herr_ne_ok
    hCode hsp hsp_lt hpc hrun (hsp ▸ hsp_align)
    hx19 hx25 hx28 hvregs
  refine p2_finish_err_arm_evs_drop (Drop := emp) harm5 (by sep_focus) (fun evs sf => ?_)
    (fun sf P_f evs hfree hst hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hCodef, _⟩ =>
      hCont sf P_f evs hfree hst hpcf hrunf htrf hspf hcsf hvregsf hCodef hent)
  rw [emp_sepConj]
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced, p2CoroScratchTailAt, p2BadKemMsgFieldsAt]
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (Entails.of_eq (p2_stack_split_dropSs3 sp stk hstk_drop hstk64).symm) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (p2_sp3e0_arm5_to_368 sp errTag w2 w3 w4 w5 w6) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1 (Entails.of_eq (p2_sp3b0_48_split_8_40 sp).symm) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1 (Entails.of_eq (p2_a90_err45_to_288 sp)) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (p2_sp80_11words_entails_88 sp u_80 errTag v90 (coroPtr + 0x398#64)
      (coroPtr + 0x4f2#64) w5 (coroPtr + 0x390#64) w3 ctxPtr outPtr w4) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (p2_coro658_298_rejoin coroPtr msgPtr pkBuf skBuf inp ikBPk spkBPk opkPkBytes opkSkBytes
      hwell hikBPk_len hspkBPk_len hopkPk_len hopkSk_len hopkSk_eq) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (p2_coro398_bytes_words4_entails_96 coroPtr (bytesToBv8 spkBPk) (bytesToBv8 inp.spkBSk)
      pkBuf 0x620#64 skBuf 0xc60#64
      (by simp [bytesToBv8, hspkBPk_len]) (by simp [bytesToBv8, hwell.2.2.1]))
    (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
    (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (pointsTo64_entails_memRegion (coroPtr + 0x488#64) (msgPtr + 0x90#64)) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (p2_coro4b0_byte_bytes_entails_65 coroPtr (opkPresentTag inp.opkBSk?) opkPkBytes opkSkBytes
      hopkPk_len hopkSk_len) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_entails_frame_v1
    (Entails.of_eq (p2_coro4f8_2cells_328_eq_344 coroPtr)) (by sep_focus) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsPlacedBudget
