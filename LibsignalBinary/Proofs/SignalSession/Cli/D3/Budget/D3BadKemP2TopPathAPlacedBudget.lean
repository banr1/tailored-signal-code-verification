/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget
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
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlaced
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5V1PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2TransPlaced
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsAPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrBPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrCPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch

/-!
# Budget-Threaded Stage P2 Path-A Bad-KEM Composition

Proves the Stage P2 Path-A (`opt = none`) `SepWPp` composition (`+0x0868 → s0.readReg64 .x30`) for
`v4` `PreKeySignalMessage`s with bad KEM payloads under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (PublicKey ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (OpkOkWitness StageP2MemInv hdrOpkIdBv? hdr_opkId?_isSome_eq_opkOkSkBytes? mkP2AcceptKeysInput_pqspkBSk mkP2AcceptKeysInput_spkBSk opkOkEvs opkOkKeyBytes opkOkRel opkOkSkBytes?_eq_of_some opkOkUpdate opkOptTag8_eq_opkPresentTag p2_allocHookStack_le_stageP2 p2_bobStack_le_v1CallStack p2_callStack_le_v1CallStack p2_envOk_id p2_mono_pre p2_sepWPp_weaken_eq p2_sub56_le_stageP2 p2_toU8_bytesToBv8 stageP1EntryPlaced stageP1ProgPlaced stageP2CallStack stageP2EnvOk stageP2Quiet stageP2Sub56Stack stageP2V1CallStack wellSized_mkP2AcceptKeysInput)
open CryptoVerification.E2E (toU8)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput DRKey HandshakeHdr Primitives WellSizedAcceptKeysInput bytesToBv8 pqxdhEntryStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved decryptPrekeySavedRegsAt)
open CryptoVerification.E2E.Pqxdh.ResponderCore (bytesToBv8_toU8 withBobMemInv)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsAt IdentitySelfVtablesPlacedOk KyberPreKeyStoreSpec KyberPreKeyVtablesPlacedOk PreKeyStoreSpec PreKeyVtablesPlacedOk SignedPreKeyStoreSpec SignedPreKeyVtablesPlacedOk speErrAt speWordsAt)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf (IdentitySelfStoreSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt uuidTryParse)
open CryptoVerification.RecordCodecs (IdentityKeyPair KyberPreKeyRecord PreKeyRecord SignedPreKeyRecord)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget (isSameAccountDistinctAtSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsBPlacedBudget (p2Arm4ErrEvents p2Arm4ErrEvents_freeOnly)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsCPlacedBudget (p2Arm5ErrEvents p2Arm5ErrEvents_freeOnly)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (IdentitySelfStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (KyberPreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (IdentitySelfStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOk SignedPreKeyStoreKitPlacedOk)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (PreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (SignedPreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsAPlacedBudget (p2_badKem_arm4_hooks_placed_ok)

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPathAPlacedBudget

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

open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsPlacedBudget (
  p2_badKem_arm4_hooks_placed_ok
  p2_badKem_arm5_hooks_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget (
  p2_badKem_entry_le_stageP2bStack
  of_cro_badKem_errOwned_placed
  of_full_badKem_errOwned_placed
  stageP2_sub5_badKem_kits_memInv_at_placed
)

set_option maxHeartbeats 1200000 in
/-- Memory-invariant-parameterized Stage P2 Path-A bad-KEM composition
(`+0x0868 → s0.readReg64 .x30`) under `[LibsignalPlacement]`. -/
theorem stageP2_pathA_badKem_kits_memInv_at_placed [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ)
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.StageP2ClosureHooksPlaced A lim ext)
    (hPure : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    {sameStk : Nat}
    (hSameAcct : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A.repAlloc uuidTryParse sameStk)))
    (hInitBobBadKemErrOwned : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withBobMemInv Φ (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv))))
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64) (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (stk : Nat) (hstk_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk)
    (hsame_le : sameStk ≤ stk) (herr_le : 768 + pqxdhEntryStack ≤ stk)
    (st : M.σ) {Qp : State → SepProp → Prop}
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ctBytes : List (BitVec 8)) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (hfits14 : FitsEnv M lim st
      (P2Sub1To4Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)))
    (hfitsKp : ∀ evs14,
      P2Sub1To4OkEnv spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr) evs14 →
      FitsEnv M lim (M.stepEvents evs14 st) (senv.kpPollEnv stId))
    (hfitsBobErr : ∀ spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp evs14 evsKp,
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes → spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes → kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk → opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes → skit.kpRel stId (.ok kp) →
      P2Sub1To4OkEnv spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr) evs14 →
      senv.kpPollEnv stId evsKp →
      FitsEnv M lim (M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8) (M.stepEvents evs14 st))
        (AcceptErrEnv (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes)))
    (hctBuf_nz : ctBufPtr ≠ 0#64) (hstk_lt : stk ≤ sp.toNat)
    (hikBSk_len : ikBSk.length = 32) (hikBPk_len : ikBPk.length = 32)
    (hikAPk_len : hdr.ikAPk.length = 32) (hekAPk_len : hdr.ekAPk.length = 32) (hkemCt_len : hdr.kemCt.length = 1568)
    (hct_bd : ctBytes.length < 2 ^ 63) (hbadKem : pkVecTag? 8#8 1568 ctBytes = none) (hCode : Φ s.mem)
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit) (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s)
    (hid_spk : spkKit.idOk signedPreKeyId)
    (hspk_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) → spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8), spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hkpk_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8), kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧ r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopk_word : ∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → opkIdWord = id)
    (hid_pk : ∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → pkKit.getIdOk id)
    (hpk_wf : ∀ (id : BitVec 32) (r : PreKeyRecord), hdrOpkIdBv? hdr = some id →
      pkKit.getRel stPk id (.ok r) → pkKit.RecOk r →
      ∃ opkPubBytes opkPrivBytes : List (BitVec 8), opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
        r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes)
    (hkp_sk : ∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) → kp.privateKey.bytes.toList = bytesToBv8 ikBSk)
    (hkp_pk : ∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) → kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk)
    (hneq : bytesToBv8 ikBPk ≠ bytesToBv8 hdr.ikAPk ∨ DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64) (hrun : s.status = .Running) (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr) (hx10 : s.readReg64 .x10 = kpkKit.kpk_vt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr) (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = pkKit.pk_vt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr) (hx16 : s.readReg64 .x16 = ikit.id_vt)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 224#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) (hx29 : s.readReg64 .x29 = fp)
    (hErrSpk : ∀ (e : spkKit.GetErr) (evs : List AllocEvent) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.error e) →
      P2Sub1To3Arm1Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) → sf.sp = sp + 3280#64 →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt spkKit.getErr outPtr e ∗ spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
        kpkKit.storeAt kyberStorePtr stKpk ∗ pkKit.storeAt preKeyStorePtr stPk ∗ ikit.identityAt idStorePtr stId ∗
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f)
    (hErrKpk : ∀ (spkRec : SignedPreKeyRecord) (e : kpkKit.GetErr) (evs : List AllocEvent) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec → kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      P2Sub1To3Arm2Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++ kpkKit.getEvs kyberPreKeyId (.error e) →
      sf.sp = sp + 3280#64 → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt kpkKit.getErr outPtr e ∗ spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
        pkKit.storeAt preKeyStorePtr stPk ∗ ikit.identityAt idStorePtr stId ∗
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f)
    (hErrPk : ∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord) (opkId : BitVec 32) (e : pkKit.GetErr)
        (evs : List AllocEvent) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec → kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) →
      kpkKit.RecOk kpkRec → hdrOpkIdBv? hdr = some opkId → pkKit.getRel stPk opkId (.error e) →
      P2Sub1To4Arm3Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) (some opkId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++ kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ pkKit.getEvs opkId (.error e) →
      sf.sp = sp + 3280#64 → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt pkKit.getErr outPtr e ∗ spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗ ikit.identityAt idStorePtr stId ∗
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f)
    (hErrKp : ∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord) (wOpk : OpkOkWitness (hdrOpkIdBv? hdr))
        (e : skit.KpErr) (evs : List AllocEvent) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec → kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) →
      kpkKit.RecOk kpkRec → opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk → skit.kpRel stId (.error e) →
      P2V1Arm4Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
        (senv.kpPollEnv stId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++ kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++
        opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++ skit.kpEvs (.error e) →
      sf.sp = sp + 3280#64 → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speErrAt skit.kpErr outPtr e ∗ spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗ ikit.identityAt idStorePtr stId ∗
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f)
    (hErrBob : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (errTag w2 w3 w4 w5 w6 : BitVec 64)
        (evs : List AllocEvent) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec → spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes → spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec → kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes → kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk → opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes → skit.kpRel stId (.ok kp) →
      P2V1Arm5EnvOfAcceptErr spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
        (senv.kpPollEnv stId)
        (AcceptErrEnv (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes))
        evs →
      errTag ≠ -2#64 → errTag ≠ -3#64 →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++ kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++
        opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++ skit.kpEvs (.ok kp) →
      sf.sp = sp + 3280#64 → ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢ speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗ pqxdhBadKemErrPayloadAt A.repAlloc errTag w2 w3 w4 ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗ ikit.identityAt idStorePtr stId ∗
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
          preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt v_330 v_388 hdr ctBytes msgVerByte opkIdWord
          kyberPreKeyId remoteRegId signedPreKeyId gMe gPeer stk Frame) → Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced A lim spkKit kpkKit pkKit ikit st s0 s
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
        hdr ctBytes msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        stSpk stKpk stPk stId gMe gPeer stk Frame) Q Qp := by
  have hstk_le64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hstk_sub56 : stageP2Sub56Stack skit ≤ stk := Nat.le_trans (p2_sub56_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2
  have hstk_alloc : allocHookStack ≤ stk := Nat.le_trans (p2_allocHookStack_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2
  let baseKey : PublicKey := ⟨⟨bytesToBv8 hdr.ekAPk, by simpa [bytesToBv8] using hekAPk_len⟩⟩
  refine p2_mono_pre
    (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget.p2_badKem_entry_to_sub1To4_placed A lim spkKit kpkKit pkKit ikit st s0 s
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 hdr ctBytes msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId stSpk stKpk stPk stId gMe gPeer stk Frame) ?_
  refine stageP2_sub1_to_4_kits_ext_placed_ofEnv ext hH hPure
    ikit skit senv hskitVt hskitOk spkKit spkEnv hspkVt hspkOk
    kpkKit kpkEnv hkpkVt hkpkOk pkKit pkEnv hpkVt hpkOk
    stk hstk_p2 hstk_le64 st s0 s
    (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemSub1To4Frame A ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr v_330 v_388 u_80 u_88 stId hdr ctBytes msgVerByte remoteRegId gMe gPeer Frame)
    Q sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr ctBufPtr
    (coroPtr + 0x390#64) u_90 u_a8 u_b8 u_d0 u_488
    baseKey signedPreKeyId kyberPreKeyId opkIdWord (hdrOpkIdBv? hdr)
    stSpk stKpk stPk b_2c0 b_390 b_4b0 b_4f1 b_4f2
    hfits14 hctBuf_nz (hInv.toCodeRo hCode) hfs
    hid_spk hspk_wf hid_kpk hkpk_wf hopk_word hid_pk hpk_wf
    hpc hrun hsp_eq hsp_align htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
    (fun e spkFutPtr evs sf P_f hrel hevs hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
      hErrSpk e evs sf P_f hrel hevs hpcf hrunf htrf hspf hcsf hvregsf hinvf
        (Entails.trans hent
          (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget.p2_badKem_arm1_entails_placed A lim spkKit kpkKit pkKit ikit
            (M.stepEvents evs st) s0 sf
            sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
            (coroPtr + 0x390#64) v_330 v_388 u_488 u_80 u_88 spkFutPtr
            b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr ctBytes
            stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes e kyberFutPtr evs sf P_f
        hspk_rel hspk_ok hpub_len hpriv_len _ _ hkpk_rel hevs
        hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
      hErrKpk spkRec e evs sf P_f hspk_rel hspk_ok hkpk_rel hevs
        hpcf hrunf htrf hspf hcsf hvregsf hinvf
        (Entails.trans hent
          (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget.p2_badKem_arm2_entails_placed A lim spkKit kpkKit pkKit ikit
            (M.stepEvents evs st) s0 sf
            sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
            (coroPtr + 0x390#64) v_330 v_388 u_488 u_80 u_88 kyberFutPtr
            b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr ctBytes
            spkRec spkPubBytes spkPrivBytes hpub_len hpriv_len
            stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes kpkRec _ _ opkId e pkBuf skBuf opkFutPtr v90 evs sf P_f
        hspk_rel hspk_ok hpub_len hpriv_len _ _ hkpk_rel hkpk_ok _ _ _ _ hopk_some hpk_rel hevs
        hpcf hrunf htrf hspf hcsf hvregsf hinvf hent =>
      hErrPk spkRec kpkRec opkId e evs sf P_f
        hspk_rel hspk_ok hkpk_rel hkpk_ok hopk_some hpk_rel (hopk_some ▸ hevs)
        hpcf hrunf htrf hspf hcsf hvregsf hinvf
        (Entails.trans hent
          (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget.p2_badKem_arm3_entails_placed A lim spkKit kpkKit pkKit ikit
            (M.stepEvents evs st) s0 sf
            sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
            (coroPtr + 0x390#64) v_330 v_388 u_80 u_88 pkBuf skBuf opkFutPtr v90
            b_4b0 msgVerByte opkId opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr ctBytes
            spkRec kpkRec spkPubBytes spkPrivBytes hpub_len hpriv_len
            stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes pkBuf skBuf idKpFutPtr v90 v_a8' v_b8' v_d0' evs14 s4
        hst_s4 hfs4 hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
        hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
        hopk_rel hopkPk_len hopkSk_len hopk_kb hevs14
        _ _ _ _
        hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4
        hx29_4 hvregs4 _hCode4 => ?_)
  let inp := mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes
  let spkBPk : SignalPqxdh.Bytes := toU8 spkPubBytes
  have hspkBPk_len : spkBPk.length = 32 := by simp [spkBPk, toU8, hspkPub_len]
  have hwell : WellSizedAcceptKeysInput inp :=
    wellSized_mkP2AcceptKeysInput hikBSk_len hikBPk_len hspkPub_len hspkPriv_len hkyberPub_len hkyberPriv_len hopkSk_len hikAPk_len hekAPk_len hkemCt_len
  have hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk := fun _ h => opkOkSkBytes?_eq_of_some h
  refine p2_mono_pre
    (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget.p2_badKem_sub4_to_sub5_placed A lim spkKit kpkKit pkKit skit
      (M.stepEvents evs14 st) s0 s4
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0'
      inp hdr ctBytes spkBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkPkBytes opkSkBytes
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId msgVerByte b_2c0 b_390 b_4f2
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId gMe gPeer stk Frame
      rfl (bytesToBv8_toU8 spkPubBytes)
      (mkP2AcceptKeysInput_spkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes)
      (mkP2AcceptKeysInput_pqspkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes)
      (opkOptTag8_eq_opkPresentTag (hdrOpkIdBv? hdr) opkSkBytes).symm hkyberPriv_len) ?_
  refine SepWPp.exists_elim fun u_b90 => SepWPp.exists_elim fun b_b98 => ?_
  exact LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget.stageP2_sub5_badKem_kits_memInv_at_placed hInv ext skit senv hH hskitOk hskitVt
    hSameAcct hInitBobBadKemErrOwned (st := M.stepEvents evs14 st) (Qp := Qp)
    inp ctBytes spkBPk opkPkBytes opkSkBytes gMe gPeer stId s0 s4 Q
    sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr idStorePtr idKpFutPtr pkBuf skBuf ctBufPtr fp
    v_a8' v_b8' v_d0' u_b90 opkIdWord 1#8 b_b98 stk
    (p2Sub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
      remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
      msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) Frame)
    rfl rfl (hdr_opkId?_isSome_eq_opkOkSkBytes? hdr opkSkBytes)
    hwell hspkBPk_len hct_bd hbadKem hopkPk_len hopkSk_len hopkSk_eq
    (fun kp hkp => hkp_sk kp hkp) (fun kp hkp => by rw [hkp_pk kp hkp]; exact hneq)
    hsame_le herr_le hstk_sub56 hstk_lt
    (hfitsKp evs14 hevs14)
    (fun kp evsKp hkp_rel hevsKp =>
      hfitsBobErr spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp evs14 evsKp
        hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
        hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
        hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hevs14 hevsKp)
    (hInv.of_keepsFrozen hCode hst_s4.keepsFrozen)
    hpc4 hrun4 hsp4 hsp_align hvregs4
    (fun s1 htr1 hst1 => p2_envOk_id hfs4 hst1 htr1)
    hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4 hx26_4 hx27_4 hx28_4 (hx29_4.trans hx29)
    (fun kp evsKp evsErr errTag w2 w3 w4 w5 w6 sf5 v_a8'' v_b8'' v_d0'' u_b90' b_b98'
        hkp_rel hevsKp hevsErr herr_ne_ok herr_ne_pend _ hpc5 hrun5 hsp5 htr5
        hx19_5 _ _ _ _ hx25_5 _ hx28_5 _ hvregs5 hCode5 => by
      have hikBPk_eq : toU8 kp.identityKey.publicKey.bytes.toList = ikBPk := by
        rw [hkp_pk kp hkp_rel, p2_toU8_bytesToBv8]
      conv => arg 4; rw [hikBPk_eq]
      let evsArm5 :=
        evs14 ++ (evsKp ++ (rustDeallocEvents skit.kpBoxSize 8 ++ (evsErr ++ p2Arm5ErrEvents 0#64)))
      have hevsArm5 : P2V1Arm5EnvOfAcceptErr spkKit.getBoxSize
          (spkEnv.getPollEnv stSpk signedPreKeyId)
          kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
          pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
          (senv.kpPollEnv stId) (AcceptErrEnv inp) evsArm5 :=
        LibsignalBinary.Heap.SeqEnv.append hevs14
          (LibsignalBinary.Heap.SeqEnv.append hevsKp
            (LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 skit.kpBoxSize)
              (LibsignalBinary.Heap.SeqEnv.append hevsErr (p2Arm5ErrEvents_freeOnly 0#64))))
      have harm5 :=
        p2_badKem_arm5_hooks_placed_ok
          (st := M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8 ++ evsErr) (M.stepEvents evs14 st))
          (Qp := Qp) ext spkKit kpkKit pkKit ikit hH s0 sf5 Q
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          pkBuf skBuf v_330 v_388 u_80 u_88 v90
          errTag w2 w3 w4 w5 w6 v_a8'' v_b8'' v_d0'' u_b90'
          inp ctBytes ikBPk spkBPk kyberPubBytes opkPkBytes opkSkBytes
          opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          msgVerByte b_2c0 b_390 b_4f2 b_b98'
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
          gMe gPeer stk (pqxdhBadKemErrPayloadAt A.repAlloc errTag w2 w3 w4 ∗ Frame)
          hwell hikBPk_len hspkBPk_len hkyberPub_len hopkPk_len hopkSk_len hopkSk_eq
          herr_ne_ok herr_ne_pend hstk_alloc hstk_lt
          hCode5 hpc5 hrun5 hsp5 hsp_align hx19_5 (hx25_5.trans hx25_4) hx28_5 hvregs5
          (fun sf P_f _ hpcf hrunf htrf hspf hcsf hvregsf hinvf hent => by
            have hst_arm5 :
                M.stepEvents (p2Arm5ErrEvents 0#64)
                  (M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8 ++ evsErr)
                    (M.stepEvents evs14 st)) =
                M.stepEvents evsArm5 st := by
              simp only [evsArm5, M.stepEvents_append]
            rw [hst_arm5] at hent
            exact hErrBob spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
              wOpk opkPkBytes opkSkBytes kp errTag w2 w3 w4 w5 w6 evsArm5 sf P_f
              hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
              hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
              hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hevsArm5
              herr_ne_ok herr_ne_pend
              hpcf hrunf (by rw [htrf, htr5, htr4]) hspf hcsf hvregsf hinvf
              (Entails.trans hent
                (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget.p2_badKem_arm5_err_payload_pull_placed A lim
                  (M.stepEvents evsArm5 st) s0 sf
                  sp fp coroPtr outPtr msgPtr ctBufPtr
                  remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt
                  kyberStorePtr kpkKit.kpk_vt v_330 v_388 errTag w2 w3 w4 w5 w6
                  inp.hdr ctBytes msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
                  (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)))
                  (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)))
                  (pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk))
                  (ikit.identityAt idStorePtr stId)
                  gMe gPeer stk Frame)))
      dsimp only [p2Sub5FramePlaced,
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Sub5FramePlaced] at harm5 ⊢
      exact p2_sepWPp_weaken_eq harm5 (by sep_focus))
    (fun e evsKp s2 hkp_err hevsKp _ hpc2 hrun2 hsp2 htr2
        hx19_2 hx21_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs2 hCode2 => by
      let evsArm4 := evs14 ++ (evsKp ++ p2Arm4ErrEvents skit.kpBoxSize 0#64)
      have hevsArm4 : P2V1Arm4Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
          kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
          pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
          (senv.kpPollEnv stId) evsArm4 :=
        LibsignalBinary.Heap.SeqEnv.append hevs14
          (LibsignalBinary.Heap.SeqEnv.append hevsKp (p2Arm4ErrEvents_freeOnly skit.kpBoxSize 0#64))
      have harm4 := p2_badKem_arm4_hooks_placed_ok
        (st := M.stepEvents evsKp (M.stepEvents evs14 st)) (Qp := Qp)
        ext spkKit kpkKit pkKit skit hH hskitOk s0 s2 Q
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90
        v_a8' v_b8' v_d0' u_b90
        inp ctBytes spkBPk kyberPubBytes opkPkBytes opkSkBytes
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        msgVerByte b_2c0 b_390 b_4f2 b_b98
        (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
        (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
        (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
        e gMe gPeer stk Frame
        hwell hspkBPk_len hkyberPub_len hopkPk_len hopkSk_len hstk_alloc hstk_lt
        hCode2 hpc2 hrun2 hsp2 hsp_align
        hx19_2 hx21_2 hx23_2 hx24_2 (hx25_2.trans hx25_4) hx26_2 hx27_2 hx28_2 hx29_2 hvregs2
        (fun sf P_f _ hpcf hrunf htrf hspf hcsf hvregsf hinvf hent => by
          have hst_arm4 :
              M.stepEvents (p2Arm4ErrEvents skit.kpBoxSize 0#64)
                (M.stepEvents evsKp (M.stepEvents evs14 st)) =
              M.stepEvents evsArm4 st := by
            simp only [evsArm4, M.stepEvents_append]
          rw [hst_arm4] at hent
          exact hErrKp spkRec kpkRec wOpk e evsArm4 sf P_f
            hspk_rel hspk_ok hkpk_rel hkpk_ok hopk_rel hkp_err hevsArm4
            hpcf hrunf (by rw [htrf, htr2, htr4]) hspf hcsf hvregsf hinvf hent)
      exact p2_sepWPp_weaken_eq harm4 (by sep_focus))

abbrev stageP2_pathA_badKem_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.StageP2ClosureHooksPlaced A lim ext)
    (hPure : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (hInitBobBadKemErrOwned : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedPlacedSpec A lim AcceptErrEnv))
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64) (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (stk : Nat) (hstk : stageP2V1CallStack spkKit kpkKit pkKit skit ≤ stk) :=
  stageP2_pathA_badKem_kits_memInv_at_placed CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2MemInv.codeRoLoaded ext
    hH hPure.to_4K (isSameAccountDistinctSpec_to_at_placed hPure.isSameAccount)
    (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget.of_cro_badKem_errOwned_placed hInitBobBadKemErrOwned)
    ikit skit senv hskitVt hskitOk spkKit spkEnv hspkVt hspkOk kpkKit kpkEnv hkpkVt hkpkOk pkKit pkEnv hpkVt hpkOk stk
    (Nat.le_trans (p2_callStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk)
    (Nat.le_trans LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_isSameAccount_le_bobV1 (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk))
    (Nat.le_trans LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget.p2_badKem_entry_le_stageP2bStack
      (Nat.le_trans LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_stageP2bStack_le_bobV1 (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk)))

abbrev stageP2_pathA_badKem_kits_full_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.StageP2ClosureHooksPlaced A lim ext)
    (hPure : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (hInitBobBadKemErrOwned : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim AcceptErrEnv))
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64) (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (stk : Nat) (hstk : stageP2V1CallStack spkKit kpkKit pkKit skit ≤ stk) :=
  stageP2_pathA_badKem_kits_memInv_at_placed CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2MemInv.frozen ext
    hH hPure.to_4K (isSameAccountDistinctSpec_to_at_placed hPure.isSameAccount)
    (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget.of_full_badKem_errOwned_placed hInitBobBadKemErrOwned)
    ikit skit senv hskitVt hskitOk spkKit spkEnv hspkVt hspkOk kpkKit kpkEnv hkpkVt hkpkOk pkKit pkEnv hpkVt hpkOk stk
    (Nat.le_trans (p2_callStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk)
    (Nat.le_trans LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_isSameAccount_le_bobV1 (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk))
    (Nat.le_trans LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget.p2_badKem_entry_le_stageP2bStack
      (Nat.le_trans LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_stageP2bStack_le_bobV1 (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit) hstk)))

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPathAPlacedBudget
