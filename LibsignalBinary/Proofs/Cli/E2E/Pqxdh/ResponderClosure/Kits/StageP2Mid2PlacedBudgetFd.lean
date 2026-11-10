/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2CalleesPlacedBudgetFd

/-!
# Descriptor-Threaded Relocatable Stage P2 Substages 1–3 Composition

Lifts placed budget-threaded Substages P2.1–P2.3 composition (`+0x0868 → +0x0d5c` or Arms 1–2) to
preserve `FdsGe3Closed` via `AllocWithFds.withFds A`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2PlacedBudgetFd

open Arm64 Arm64.Process
open CryptoGames.LibsignalSession (PublicKey ShaCompress)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord SignedPreKeyRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  IdentitySelfStoreSpec IdentityStoreSpec KyberPreKeyStoreSpec KyberPreKeyVtablesPlacedOk
  PreKeyStoreSpec SignedPreKeyStoreSpec SignedPreKeyVtablesPlacedOk
)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput DRKey Primitives)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (stageP2CallStack)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustDeallocEvents
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget (
  KemKeyPairFromPubPrivEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  KyberPreKeyStoreKitPlacedOkFds SignedPreKeyStoreKitPlacedOkFds
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd (
  kpkKitFds_toWithFds
  spkKitFds_toWithFds
  stageP2ClosureHooks_toWithFds
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  withFds withFds_live withFds_pool_enforced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2CalleesPlacedBudgetFd (
  StageP2PureCalleesPlaced4KOfEnvFd StageP2PureCalleesPlacedOfEnvFd
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  P2Sub1Env p2Sub1Events
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget (
  p2SpkRecFreeEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget (
  P2Sub3TailAllocEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3PlacedBudget (
  p2Sub3PreTailEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2PlacedBudget (
  P2Sub1To3SeqEnv P2Sub1To3ThenEnv p2Sub1To2OkEvents stageP2Sub1To3KitsPlacedProp
  stageP2_sub1_to_3_kits_ext_placed stageP2_sub1_to_3_kits_seqEnv_ext_placed
  stageP2_sub1_to_3_kits_thenEnv_ext_placed
)

/-- `FdsGe3Closed`-preserving Stage P2 Substages 1–3 (`+0x0868 -> +0x0d5c` or error exit via Arms 1–2) via
`(withFds A, lim)`. -/
theorem stageP2_sub1_to_3_kits_ext_placed_fd [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnvFd P A lim F BobV1Env AcceptErrEnv ext)
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspk_fds : spkKit.fdsOk = FdsGe3Closed)
    (hspkOk : SignedPreKeyStoreKitPlacedOkFds A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpk_fds : kpkKit.fdsOk = FdsGe3Closed)
    (hkpkOk : KyberPreKeyStoreKitPlacedOkFds A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (stk : Nat) (hstk_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (st : M.σ) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
     v_b0 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hfits_sub1 : FitsEnv M lim st (P2Sub1Env spkKit.getBoxSize))
    (hfits_spk_poll : FitsEnv M lim
      (M.stepEvents (p2Sub1Events spkKit.getBoxSize) st)
      (spkEnv.getPollEnv stSpk signedPreKeyId))
    (hfits_kpk_shim : ∀ (spkRec : SignedPreKeyRecord) (evs_spk : List AllocEvent)
      (spkPubCap spkPrivCap spkSigCap : Nat),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkEnv.getPollEnv stSpk signedPreKeyId evs_spk →
      33 ≤ spkPubCap → 32 ≤ spkPrivCap →
      FitsEnv M lim
        (M.stepEvents
          (p2Sub1Events spkKit.getBoxSize ++ evs_spk ++
            p2SpkRecFreeEvents spkKit.getBoxSize spkPubCap spkPrivCap spkSigCap) st)
        (BoxAllocEnv kpkKit.getBoxSize))
    (hfits_kpk_poll : ∀ (spkRec : SignedPreKeyRecord) (evs_spk : List AllocEvent)
      (spkPubCap spkPrivCap spkSigCap : Nat),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkEnv.getPollEnv stSpk signedPreKeyId evs_spk →
      33 ≤ spkPubCap → 32 ≤ spkPrivCap →
      FitsEnv M lim
        (M.stepEvents
          (p2Sub1To2OkEvents spkKit.getBoxSize evs_spk spkPubCap spkPrivCap spkSigCap
            kpkKit.getBoxSize) st)
        (kpkEnv.getPollEnv stKpk kyberPreKeyId))
    (hfits_kem : ∀ (spkRec : SignedPreKeyRecord) (evs_spk : List AllocEvent)
      (spkPubCap spkPrivCap spkSigCap : Nat)
      (kpkRec : KyberPreKeyRecord) (evs_kpk : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkEnv.getPollEnv stSpk signedPreKeyId evs_spk →
      33 ≤ spkPubCap → 32 ≤ spkPrivCap →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_kpk →
      FitsEnv M lim
        (M.stepEvents
          (p2Sub1To2OkEvents spkKit.getBoxSize evs_spk spkPubCap spkPrivCap spkSigCap
            kpkKit.getBoxSize ++ evs_kpk ++ rustDeallocEvents kpkKit.getBoxSize 8) st)
        KemKeyPairFromPubPrivEnv)
    (hfits_tail : ∀ (spkRec : SignedPreKeyRecord) (evs_spk : List AllocEvent)
      (spkPubCap spkPrivCap spkSigCap : Nat)
      (kpkRec : KyberPreKeyRecord) (evs_kpk : List AllocEvent)
      (kpkPubCap kpkPrivCap kpkSigCap : Nat),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkEnv.getPollEnv stSpk signedPreKeyId evs_spk →
      33 ≤ spkPubCap → 32 ≤ spkPrivCap →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_kpk →
      1569 ≤ kpkPubCap → 3169 ≤ kpkPrivCap →
      FitsEnv M lim
        (M.stepEvents
          (p2Sub1To2OkEvents spkKit.getBoxSize evs_spk spkPubCap spkPrivCap spkSigCap
            kpkKit.getBoxSize ++ evs_kpk ++
            p2Sub3PreTailEvents kpkKit.getBoxSize kpkPubCap kpkPrivCap kpkSigCap) st)
        P2Sub3TailAllocEnv) :
    stageP2Sub1To3KitsPlacedProp (withFds A) lim
      ext skit spkKit spkEnv kpkKit kpkEnv pkKit
      stk st s0 s Frame Q Qp
      sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
      v_b0 u_90 u_a8 u_b8 u_d0 baseKey signedPreKeyId kyberPreKeyId
      stSpk stKpk b_2c0 b_390 b_4f1 b_4f2 :=
  stageP2_sub1_to_3_kits_ext_placed
    (A := withFds A) (lim := lim)
    (Qp := Qp) ext
    (stageP2ClosureHooks_toWithFds hH)
    (hPure.toWithFds henf)
    skit spkKit spkEnv hspkVt (spkKitFds_toWithFds henf hspk_fds hspkOk)
    kpkKit kpkEnv hkpkVt (kpkKitFds_toWithFds henf hkpk_fds hkpkOk)
    pkKit stk hstk_p2 hstk_lt st s0 s Frame Q
    sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
    v_b0 u_90 u_a8 u_b8 u_d0 baseKey signedPreKeyId kyberPreKeyId
    stSpk stKpk b_2c0 b_390 b_4f1 b_4f2
    hfits_sub1
    hfits_spk_poll
    hfits_kpk_shim
    hfits_kpk_poll
    hfits_kem
    hfits_tail

/-- `P2Sub1To3SeqEnv` specialization of `stageP2_sub1_to_3_kits_ext_placed_fd`. -/
theorem stageP2_sub1_to_3_kits_seqEnv_ext_placed_fd [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnvFd P A lim F BobV1Env AcceptErrEnv ext)
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspk_fds : spkKit.fdsOk = FdsGe3Closed)
    (hspkOk : SignedPreKeyStoreKitPlacedOkFds A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpk_fds : kpkKit.fdsOk = FdsGe3Closed)
    (hkpkOk : KyberPreKeyStoreKitPlacedOkFds A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (stk : Nat) (hstk_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (st : M.σ) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
     v_b0 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hfits : FitsEnv M lim st
      (P2Sub1To3SeqEnv spkKit spkEnv stSpk signedPreKeyId kpkKit kpkEnv stKpk kyberPreKeyId)) :
    stageP2Sub1To3KitsPlacedProp (withFds A) lim
      ext skit spkKit spkEnv kpkKit kpkEnv pkKit
      stk st s0 s Frame Q Qp
      sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
      v_b0 u_90 u_a8 u_b8 u_d0 baseKey signedPreKeyId kyberPreKeyId
      stSpk stKpk b_2c0 b_390 b_4f1 b_4f2 :=
  stageP2_sub1_to_3_kits_seqEnv_ext_placed
    (A := withFds A) (lim := lim)
    (Qp := Qp) ext
    (stageP2ClosureHooks_toWithFds hH)
    (hPure.toWithFds henf)
    skit spkKit spkEnv hspkVt (spkKitFds_toWithFds henf hspk_fds hspkOk)
    kpkKit kpkEnv hkpkVt (kpkKitFds_toWithFds henf hkpk_fds hkpkOk)
    pkKit stk hstk_p2 hstk_lt st s0 s Frame Q
    sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
    v_b0 u_90 u_a8 u_b8 u_d0 baseKey signedPreKeyId kyberPreKeyId
    stSpk stKpk b_2c0 b_390 b_4f1 b_4f2
    hfits

/-- `P2Sub1To3ThenEnv` specialization of `stageP2_sub1_to_3_kits_ext_placed_fd`. -/
theorem stageP2_sub1_to_3_kits_thenEnv_ext_placed_fd [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {TailEnv : List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnvFd P A lim F BobV1Env AcceptErrEnv ext)
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspk_fds : spkKit.fdsOk = FdsGe3Closed)
    (hspkOk : SignedPreKeyStoreKitPlacedOkFds A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpk_fds : kpkKit.fdsOk = FdsGe3Closed)
    (hkpkOk : KyberPreKeyStoreKitPlacedOkFds A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (stk : Nat) (hstk_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (st : M.σ) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
     v_b0 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hfits : FitsEnv M lim st
      (P2Sub1To3ThenEnv spkKit spkEnv stSpk signedPreKeyId kpkKit kpkEnv stKpk kyberPreKeyId
        TailEnv)) :
    stageP2Sub1To3KitsPlacedProp (withFds A) lim
      ext skit spkKit spkEnv kpkKit kpkEnv pkKit
      stk st s0 s Frame Q Qp
      sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
      v_b0 u_90 u_a8 u_b8 u_d0 baseKey signedPreKeyId kyberPreKeyId
      stSpk stKpk b_2c0 b_390 b_4f1 b_4f2 :=
  stageP2_sub1_to_3_kits_thenEnv_ext_placed
    (A := withFds A) (lim := lim)
    (Qp := Qp) (TailEnv := TailEnv) ext
    (stageP2ClosureHooks_toWithFds hH)
    (hPure.toWithFds henf)
    skit spkKit spkEnv hspkVt (spkKitFds_toWithFds henf hspk_fds hspkOk)
    kpkKit kpkEnv hkpkVt (kpkKitFds_toWithFds henf hkpk_fds hkpkOk)
    pkKit stk hstk_p2 hstk_lt st s0 s Frame Q
    sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
    v_b0 u_90 u_a8 u_b8 u_d0 baseKey signedPreKeyId kyberPreKeyId
    stSpk stKpk b_2c0 b_390 b_4f1 b_4f2
    hfits

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2PlacedBudgetFd
