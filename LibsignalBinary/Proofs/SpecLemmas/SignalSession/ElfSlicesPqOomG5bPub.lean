/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
public import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# `CliPubCalleesFrozenPlaced` and Ghost Congruences for D3 Untyped `recv`

**Checked by Lean.**

Proves `CliPubCalleesFrozenPlaced` for the D3 untyped `recv` outer Block-`579` composition
(`ReadFileRuleEnvFixed cliIo.rd`, `DecPkD3UntypedEnvOf`, `PksmTryFromEnv`), parameterized over
arbitrary or guarded `encrypt` / `decryptSignal` slot envelopes and specialized to
`binaryKitRunSlotEnvsExact`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bPub

open Arm64.Obj (MultiPlacement)
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams pqxdhSpqrModel)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall cliIo cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost DecSigGhost EncGhost InitGhost addrValOf)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliKitStk cliPollIdKitPlaced cliPollSelfKitPlaced cliPollSessKitPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (TryDecryptCliEnvOfPure tryDecryptEnvArgsToGhost)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (decBinaryIdKitPlacedBudgetFixed decBinarySessKitPlacedBudgetFixed
   realCliInitBinarySlotEnvFixed w1BinaryIdKitPlacedBudgetFixed w1BinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf (TryDecryptCliLinkedEnvOf)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot (W2RealTdEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromKeyReadyEnv FromLoadPolledEnv FromPostSomeEnv FromRegionSomeEnv FromStoreCallEnv
   FromTrustedFalseEnv FromTrustedTrueEnv LoadPollStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (LoadStepEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedEnvOf DecPkD3UntypedPollEnv PqxdhAcceptBadKemErrEnv
   StageP2BadKemRejectEnv StageP2UntypedRejectEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitBudgetEnv cliIdentityKitDefaultBudgetEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliSessionKitBudgetEnv cliSessionKitDefaultBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliPubCalleesFrozenPlaced CliRunHooksBundle cliPubCallees_d2c_frozen_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
  (cliPollSelfBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
  (StageP1OkEnv StageP1UntrustedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (CliDpPollUntrustedEnv cliIdStoreFullBudgetEnv cliPollIdBudgetEnv cliPollSessBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (decIdKitPlaced decSessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
  (CliDecryptSignalSlotEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (CliEncryptSlotEnv w1IdKitPlaced w1SessKitPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact hole3_decSigEnv_r3a_congr hole3_encEnv_r2_congr
   hole3_initEnv_r1c_congr hole3_pksmTryFromEnv_congr)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
  (FromS2GenEnv FromS3GenEnv FromS4GenEnv FromS5GenEnv FromS6GenEnv FromS7GenEnv FromS8GenEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux (s7Env vmacEvents)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (verifyMacWithAddressesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (RecordDecryptEnv TryDecryptEnvArgs recordTryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (verifyMacWithAddressesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (RecordDecryptEnv TryDecryptEnvArgs recordTryDecryptEnvArgs)

/-! ## Parametric `RunSlotEnvs` Bundles -/

def g5bp_slotEnvsOf
    (EncEnv : EncGhost → List AllocEvent → Prop)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs where
  encrypt := EncEnv
  decryptSignal := DecSigEnv
  initiate := InitEnv
  decryptPrekey := DecPkEnv

/-- Binary-kit `RunSlotEnvs` bundle parametric in `sendEnv : SpqrSendBudgetEnv`. -/
noncomputable def g5bp_binaryKitRunSlotEnvsOfSend [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets)
    (sendEnv : SpqrSendBudgetEnv)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs :=
  g5bp_slotEnvsOf
    (CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B sendEnv
      (w1BinarySessKitPlacedBudgetFixed A.repAlloc B)
      (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B))
    (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (W2RealTdEnv W.C.F W.Q.K)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B))
    InitEnv
    DecPkEnv

/-- Binary-kit `RunSlotEnvs` bundle guarding both `encrypt` (`sendEnv`) and `decryptSignal`
by `PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val`. -/
noncomputable def g5bp_binaryKitRunSlotEnvsGuardedOfSend [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets)
    (sendEnv : SpqrSendBudgetEnv)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs :=
  g5bp_slotEnvsOf
    (fun x evs =>
      PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
        CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B sendEnv
          (w1BinarySessKitPlacedBudgetFixed A.repAlloc B)
          (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B) x evs)
    (fun x evs =>
      PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
        CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (W2RealTdEnv W.C.F W.Q.K)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x evs)
    InitEnv
    DecPkEnv

/-- Binary-kit `RunSlotEnvs` bundle parametric in `sendEnv` and `maxOps`, guarding
`decryptSignal` (`TryDecryptCliLinkedEnvOf maxOps W.C W.Q.K`) by `PeerSpqrStateTight640` while
keeping `encrypt` unguarded. -/
noncomputable def g5bp_binaryKitRunSlotEnvsOfSendDecSigGuarded [LibsignalPlacement]
    {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets)
    (sendEnv : SpqrSendBudgetEnv) (maxOps : Nat := 109)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs :=
  g5bp_slotEnvsOf
    (CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B sendEnv
      (w1BinarySessKitPlacedBudgetFixed A.repAlloc B)
      (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B))
    (fun x evs =>
      PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
        CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B
          (TryDecryptCliLinkedEnvOf maxOps W.C W.Q.K)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x evs)
    InitEnv
    DecPkEnv

/-! ## Congruence Helpers -/

private theorem g5bp_seqEnv_congr {P₁ P₂ Q₁ Q₂ : List AllocEvent → Prop}
    (hP : P₁ = P₂) (hQ : Q₁ = Q₂) :
    SeqEnv P₁ Q₁ = SeqEnv P₂ Q₂ := by
  rw [hP, hQ]

private theorem g5bp_or_congr {A₁ A₂ B₁ B₂ : Prop} (hA : A₁ = A₂) (hB : B₁ = B₂) :
    (A₁ ∨ B₁) = (A₂ ∨ B₂) := by
  rw [hA, hB]

private theorem g5bp_and_congr {A₁ A₂ B₁ B₂ : Prop} (hA : A₁ = A₂) (hB : B₁ = B₂) :
    (A₁ ∧ B₁) = (A₂ ∧ B₂) := by
  rw [hA, hB]

private theorem g5bp_exists_congr {α : Sort _} {P Q : α → Prop} (h : ∀ a, P a = Q a) :
    (∃ a, P a) = (∃ a, Q a) :=
  congrArg Exists (funext h)

private theorem g5bp_ite_congr {α : Sort _} {c₁ c₂ : Prop} [d₁ : Decidable c₁] [d₂ : Decidable c₂]
    {a₁ a₂ b₁ b₂ : α} (hc : c₁ ↔ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) :
    (@ite α c₁ d₁ a₁ b₁) = (@ite α c₂ d₂ a₂ b₂) := by
  cases d₁ with
  | isFalse h1 =>
    cases d₂ with
    | isFalse _ => exact hb
    | isTrue h2 => exact False.elim (h1 (hc.mpr h2))
  | isTrue h1 =>
    cases d₂ with
    | isFalse h2 => exact False.elim (h2 (hc.mp h1))
    | isTrue _ => exact ha

private theorem g5bp_stringCloneEnv_eq {a b : AddrGhost} (h : a.val = b.val) :
    StringCloneEnv a.name = StringCloneEnv b.name := by
  have hb : a.name.bytes = b.name.bytes := congrArg AddrVal.name h
  funext evs
  unfold StringCloneEnv
  rw [hb]

private theorem g5bp_serializeAddresses_eq (l : AddrGhost) {a b : AddrGhost}
    (h : a.val = b.val) :
    CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
        (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse) l a =
      CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
        (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse) l b := by
  have hb : a.name.bytes = b.name.bytes := congrArg AddrVal.name h
  have hd : a.device = b.device := congrArg AddrVal.device h
  unfold CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
  rw [hb, hd]

private theorem g5bp_serializeAddresses_fst_eq {a b : AddrGhost} (l : AddrGhost)
    (h : a.val = b.val) :
    CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
        (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse) a l =
      CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
        (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse) b l := by
  have hb : a.name.bytes = b.name.bytes := congrArg AddrVal.name h
  have hd : a.device = b.device := congrArg AddrVal.device h
  unfold CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
  rw [hb, hd]

private theorem g5bp_otrEncryptCoreEnv_eq (P : PEParams) (sendEnv : SpqrSendBudgetEnv)
    (ot : CryptoGames.LibsignalSession.OutgoingTripleRatchet (List (BitVec 8)))
    (ptext : List (BitVec 8)) (loc : Option AddrGhost) {a b : AddrGhost}
    (rest : List (BitVec 8)) (h : a.val = b.val) :
    LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.OtrEncryptCoreEnv
        P.C (pqxdhSpqrModel P) sendEnv uuidTryParse ot ptext loc a rest =
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.OtrEncryptCoreEnv
        P.C (pqxdhSpqrModel P) sendEnv uuidTryParse ot ptext loc b rest := by
  have hsm : ∀ pqrKey pqrMsg,
      LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget.SignalMessageNewEnv uuidTryParse
          (LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.otrSignalMsgGhost
            P.C ot pqrKey pqrMsg ptext loc a) =
        LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget.SignalMessageNewEnv uuidTryParse
          (LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.otrSignalMsgGhost
            P.C ot pqrKey pqrMsg ptext loc b) := by
    intro pqrKey pqrMsg
    have haddr :
        (LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.otrSignalMsgGhost
            P.C ot pqrKey pqrMsg ptext loc a).addresses uuidTryParse =
          (LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.otrSignalMsgGhost
            P.C ot pqrKey pqrMsg ptext loc b).addresses uuidTryParse := by
      cases loc with
      | none => rfl
      | some l => exact g5bp_serializeAddresses_eq l h
    have hproto :
        (LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.otrSignalMsgGhost
            P.C ot pqrKey pqrMsg ptext loc a).protoMsg uuidTryParse =
          (LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.otrSignalMsgGhost
            P.C ot pqrKey pqrMsg ptext loc b).protoMsg uuidTryParse := by
      unfold CryptoVerification.LibsignalTripleRatchet.SignalMessageNewGhost.protoMsg
      rw [haddr]
      rfl
    funext evs
    unfold LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget.SignalMessageNewEnv
      LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget.signalMessageNewEvents
    rw [haddr, hproto]
    rfl
  funext evs
  exact congrFun
    (g5bp_seqEnv_congr rfl (funext fun evs' => by
      cases (pqxdhSpqrModel P).send ot.pqrState rest with
      | none => rfl
      | some v =>
        rcases v with ⟨_, pqrKey, pqrMsg⟩
        exact congrFun
          (g5bp_seqEnv_congr rfl
            (g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr (hsm pqrKey pqrMsg) rfl)))
          evs'))
    evs

private theorem g5bp_ppe_congr
    (C : Crypto)
    (S : CryptoVerification.LibsignalTripleRatchet.SpqrModel)
    (sess : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)))
    (otr : CryptoGames.LibsignalSession.OutgoingTripleRatchet (List (BitVec 8)))
    (items : CryptoGames.LibsignalSessionApi.PendingPreKey)
    (ptext : List (BitVec 8)) {ad₁ ad₂} (rest : List (BitVec 8))
    {C₁ C₂ : CryptoGames.LibsignalSession.OutgoingTripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop}
    (had : ad₁ = ad₂) (hC : ∀ o, C₁ o = C₂ o) (evs' : List AllocEvent) :
    (let res := CryptoGames.LibsignalSession.Mut.exec
      (CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt C
        CryptoVerification.LibsignalProtoCodec.protoSignalCodec S.spqr ptext ad₁ rest) otr
    FreeOnlyEvs evs' ∨
    match res.1 with
    | .error _ => False
    | .ok sm =>
      SeqEnv
        (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.PreKeyMsgNewRawEnv
          (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.pendingKyberPayload sess)
          sm.serialized.length
          (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.preKeyMsgFromItems
            sess items res.2 sm).serialized.length)
        (fun evs'' => FreeOnlyEvs evs'' ∨ C₁ res.2 evs'') evs') =
    (let res := CryptoGames.LibsignalSession.Mut.exec
      (CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt C
        CryptoVerification.LibsignalProtoCodec.protoSignalCodec S.spqr ptext ad₂ rest) otr
    FreeOnlyEvs evs' ∨
    match res.1 with
    | .error _ => False
    | .ok sm =>
      SeqEnv
        (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.PreKeyMsgNewRawEnv
          (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.pendingKyberPayload sess)
          sm.serialized.length
          (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.preKeyMsgFromItems
            sess items res.2 sm).serialized.length)
        (fun evs'' => FreeOnlyEvs evs'' ∨ C₂ res.2 evs'') evs') := by
  subst had
  dsimp only
  cases (CryptoGames.LibsignalSession.Mut.exec
    (CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt C
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec S.spqr ptext ad₁ rest) otr).1 with
  | error _ => rfl
  | ok _ => simp only [hC]

/-! ## Slot Ghost-Congruence Lemmas -/

/-- Ghost congruence on `CliEncryptSlotEnv` for any `sendEnv : SpqrSendBudgetEnv`. -/
theorem g5bp_encEnv_r2_congr [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (sendEnv : SpqrSendBudgetEnv)
    (gc : RunCall) (peerV : AddrV) (peerG meG : AddrGhost) (fsp : BitVec 64)
    (hp : peerG.val = addrValOf peerV) :
    CliEncryptSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets sendEnv
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (r2EncGhost gc peerG meG fsp) =
      CliEncryptSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets sendEnv
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64) := by
  let P : PEParams := ⟨W.C, W.Q⟩
  let x₁ := r2EncGhost gc peerG meG fsp
  let x₂ := r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64
  let y₁ := CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas.w1EncGhost x₁
  let y₂ := CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas.w1EncGhost x₂
  let kit₁ := w1SessKitPlaced A.repAlloc cliRunBudgets x₁.F x₁.peer
  let kit₂ := w1SessKitPlaced A.repAlloc cliRunBudgets x₂.F x₂.peer
  let ke₁ := LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsKitEnv
    (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₁.F x₁.peer)
  let ke₂ := LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsKitEnv
    (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₂.F x₂.peer)
  let ikit₁ := w1IdKitPlaced A.repAlloc cliRunBudgets x₁.F x₁.peer
  let ikit₂ := w1IdKitPlaced A.repAlloc cliRunBudgets x₂.F x₂.peer
  let ike₁ := LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsIkitEnv
    (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₁.F x₁.peer)
  let ike₂ := LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsIkitEnv
    (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₂.F x₂.peer)
  let st0 := StoresGhost.opened.sessions
  let ist0 := StoresGhost.opened.identity
  have hy_val : y₁.rem.val = y₂.rem.val := hp
  have hsc : StringCloneEnv y₁.rem.name = StringCloneEnv y₂.rem.name :=
    g5bp_stringCloneEnv_eq hy_val
  have hload : ke₁.loadPollEnv st0 y₁.rem.val = ke₂.loadPollEnv st0 y₂.rem.val :=
    congrArg (ke₂.loadPollEnv st0) hy_val
  have hscope : ∀ r, kit₁.ScopeAt scopeKit st0 y₁.rem.val r = kit₂.ScopeAt scopeKit st0 y₂.rem.val r :=
    fun r => congrFun (congrArg (kit₂.ScopeAt scopeKit st0) hy_val) r
  have htrust : ∀ k, ike₁.trustPollEnv ist0 y₁.rem.val k .sending =
      ike₂.trustPollEnv ist0 y₂.rem.val k .sending :=
    fun k => congrArg (fun v => ike₂.trustPollEnv ist0 v k .sending) hy_val
  have hsave : ∀ k, ike₁.savePollEnv (ikit₁.trustUpdate ist0 y₁.rem.val k .sending (.ok true)) y₁.rem.val k =
      ike₂.savePollEnv (ikit₂.trustUpdate ist0 y₂.rem.val k .sending (.ok true)) y₂.rem.val k :=
    fun k => congrArg (fun v => ike₂.savePollEnv ist0 v k) hy_val
  have hstore : ∀ r, ke₁.storePollEnv st0 y₁.rem.val r = ke₂.storePollEnv st0 y₂.rem.val r :=
    fun r => congrArg (fun v => ke₂.storePollEnv st0 v r) hy_val
  have htrust_step : ∀ k,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.TrustStepEnv
          ikit₁ ike₁ ist0 y₁.rem.val k =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.TrustStepEnv
          ikit₂ ike₂ ist0 y₂.rem.val k :=
    fun k => g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr (htrust k) rfl)
  have hsave_step : ∀ k,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SaveStepEnv
          ikit₁ ike₁ (ikit₁.trustUpdate ist0 y₁.rem.val k .sending (.ok true)) y₁.rem.val k =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SaveStepEnv
          ikit₂ ike₂ (ikit₂.trustUpdate ist0 y₂.rem.val k .sending (.ok true)) y₂.rem.val k :=
    fun k => g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr (hsave k) rfl)
  have happly : ∀ sess otr' taken,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromApplyEnv
          kit₁ ke₁ st0 y₁ sess otr' taken =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromApplyEnv
          kit₂ ke₂ st0 y₂ sess otr' taken :=
    fun _ _ _ => g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr (hstore _) rfl))
  have hfromSave : ∀ sess otr' taken k,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromSaveEnv
          kit₁ ke₁ st0 ikit₁ ike₁
          (ikit₁.trustUpdate ist0 y₁.rem.val k .sending (.ok true)) y₁ sess otr' taken k =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromSaveEnv
          kit₂ ke₂ st0 ikit₂ ike₂
          (ikit₂.trustUpdate ist0 y₂.rem.val k .sending (.ok true)) y₂ sess otr' taken k :=
    fun sess otr' taken k =>
      g5bp_seqEnv_congr (hsave_step k)
        (funext fun evs => g5bp_or_congr rfl (congrFun (happly sess otr' taken) evs))
  have hcm : ∀ sess otr' taken k,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromCmEnv
          kit₁ ke₁ st0 ikit₁ ike₁ ist0 y₁ sess otr' taken k =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromCmEnv
          kit₂ ke₂ st0 ikit₂ ike₂ ist0 y₂ sess otr' taken k :=
    fun sess otr' taken k =>
      g5bp_seqEnv_congr (htrust_step k)
        (funext fun evs =>
          g5bp_or_congr rfl
            (g5bp_or_congr
              (congrFun (g5bp_seqEnv_congr hsc rfl) evs)
              (congrFun (hfromSave sess otr' taken k) evs)))
  have hppe : ∀ sess otr taken k items,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.PreKeyPostEncryptEnv
          P.C (pqxdhSpqrModel P) uuidTryParse kit₁ ke₁ st0 ikit₁ ike₁ ist0 y₁ sess otr taken k items =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.PreKeyPostEncryptEnv
          P.C (pqxdhSpqrModel P) uuidTryParse kit₂ ke₂ st0 ikit₂ ike₂ ist0 y₂ sess otr taken k items :=
    fun sess otr taken k items => funext fun evs' =>
      g5bp_ppe_congr P.C (pqxdhSpqrModel P) sess otr items y₁.ptext y₁.rest
        (g5bp_serializeAddresses_eq y₁.loc hy_val) (fun o => hcm sess o taken k) evs'
  have hkey : ∀ sess otr taken k,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromKeyEnv
          P.C (pqxdhSpqrModel P) sendEnv uuidTryParse kit₁ ke₁ st0 ikit₁ ike₁ ist0 y₁ sess otr taken k =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromKeyEnv
          P.C (pqxdhSpqrModel P) sendEnv uuidTryParse kit₂ ke₂ st0 ikit₂ ike₂ ist0 y₂ sess otr taken k :=
    fun sess otr taken k => funext fun evs =>
      g5bp_or_congr
        (g5bp_and_congr rfl
          (congrFun
            (g5bp_seqEnv_congr
              (g5bp_otrEncryptCoreEnv_eq P sendEnv otr y₁.ptext none y₁.rest hy_val)
              (funext fun evs' => g5bp_or_congr rfl (congrFun (hcm sess _ taken k) evs')))
            evs))
        (g5bp_exists_congr fun items =>
          g5bp_and_congr rfl
            (g5bp_or_congr
              (congrFun (g5bp_seqEnv_congr hsc rfl) evs)
              (congrFun
                (g5bp_seqEnv_congr rfl
                  (g5bp_seqEnv_congr
                    (g5bp_otrEncryptCoreEnv_eq P sendEnv otr y₁.ptext (some y₁.loc) y₁.rest hy_val)
                    (hppe sess otr taken k items)))
                evs)))
  have hotr : ∀ sess otr taken,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromOtrEnv
          P.C (pqxdhSpqrModel P) sendEnv uuidTryParse kit₁ ke₁ st0 ikit₁ ike₁ ist0 y₁ sess otr taken =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromOtrEnv
          P.C (pqxdhSpqrModel P) sendEnv uuidTryParse kit₂ ke₂ st0 ikit₂ ike₂ ist0 y₂ sess otr taken :=
    fun sess otr taken => funext fun evs =>
      g5bp_or_congr rfl
        (g5bp_exists_congr fun k =>
          g5bp_and_congr rfl (congrFun (hkey sess otr taken k) evs))
  funext evs
  exact congrFun
    (g5bp_seqEnv_congr
      (g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr hload rfl))
      (funext fun evs₁ =>
        g5bp_or_congr rfl
          (g5bp_or_congr
            (congrFun (g5bp_seqEnv_congr hsc rfl) evs₁)
            (congrFun
              (g5bp_seqEnv_congr rfl
                (funext fun evs' =>
                  g5bp_or_congr rfl
                    (g5bp_exists_congr fun r =>
                      g5bp_exists_congr fun sess =>
                        g5bp_exists_congr fun otr =>
                          g5bp_exists_congr fun taken =>
                            g5bp_and_congr (hscope r)
                              (g5bp_and_congr rfl
                                (g5bp_and_congr rfl
                                  (congrFun (hotr sess otr taken) evs'))))))
              evs₁))))
    evs

/-- Lifts `r2` ghost congruence across any `(FsFiles → AddrVal → Prop)` guard. -/
theorem g5bp_guardedEncEnv_r2_congr
    (G : FsFiles → AddrVal → Prop)
    (EncEnv : EncGhost → List AllocEvent → Prop)
    (henc : ∀ gc peerV peerG meG fsp, peerG.val = addrValOf peerV →
      EncEnv (r2EncGhost gc peerG meG fsp) =
        EncEnv (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64))
    (gc : RunCall) (peerV : AddrV) (peerG meG : AddrGhost) (fsp : BitVec 64)
    (hp : peerG.val = addrValOf peerV) :
    (fun (x : EncGhost) evs => G x.F x.peer.val → EncEnv x evs)
        (r2EncGhost gc peerG meG fsp) =
      (fun (x : EncGhost) evs => G x.F x.peer.val → EncEnv x evs)
        (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64) := by
  have hf : (r2EncGhost gc peerG meG fsp).F =
      (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64).F := rfl
  have hval : (r2EncGhost gc peerG meG fsp).peer.val =
      (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64).peer.val := hp
  funext evs
  dsimp only
  rw [hf, hval, henc gc peerV peerG meG fsp hp]

/-- Ghost congruence on `CliDecryptSignalSlotEnv` at `W2RealTdEnv`. -/
theorem g5bp_decSigEnv_r3a_congr [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M)
    (gc : RunCall) (fsp : BitVec 64)
    (w) (peerV : AddrV) (meG : AddrGhost) (msgG) (m) :
    CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets (W2RealTdEnv W.C.F W.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets (W2RealTdEnv W.C.F W.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (r3aDecSigGhost0 gc peerV meG m) := by
  let P : PEParams := ⟨W.C, W.Q⟩
  let x₁ := r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m
  let x₂ := r3aDecSigGhost0 gc peerV meG m
  let z₁ := CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.toDecryptGhost x₁
  let z₂ := CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.toDecryptGhost x₂
  let kit₁ := decSessKitPlaced A.repAlloc x₁.F x₁.peer cliRunBudgets
  let kit₂ := decSessKitPlaced A.repAlloc x₂.F x₂.peer cliRunBudgets
  let ke₁ := decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₁.F x₁.peer
  let ke₂ := decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₂.F x₂.peer
  let ikit₁ := decIdKitPlaced A.repAlloc x₁.F x₁.peer cliRunBudgets
  let ikit₂ := decIdKitPlaced A.repAlloc x₂.F x₂.peer cliRunBudgets
  let ike₁ := decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₁.F x₁.peer
  let ike₂ := decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₂.F x₂.peer
  let st0 := StoresGhost.opened.sessions
  let ist0 := StoresGhost.opened.identity
  have hload_step : LoadPollStepEnv kit₁ ke₁ st0 z₁.rem.val = LoadPollStepEnv kit₂ ke₂ st0 z₂.rem.val :=
    g5bp_seqEnv_congr rfl rfl
  have htrust_step : ∀ k,
      TrustStepEnv ikit₁ ike₁ ist0 z₁.rem.val k .receiving =
        TrustStepEnv ikit₂ ike₂ ist0 z₂.rem.val k .receiving :=
    fun _ => g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr rfl rfl)
  have hsave_step : ∀ k,
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.SaveStepEnv
          ikit₁ ike₁ (ikit₁.trustUpdate ist0 z₁.rem.val k .receiving (.ok true)) z₁.rem.val k =
        LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.SaveStepEnv
          ikit₂ ike₂ (ikit₂.trustUpdate ist0 z₂.rem.val k .receiving (.ok true)) z₂.rem.val k :=
    fun _ => g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr rfl rfl)
  have hstore_call : ∀ rec',
      FromStoreCallEnv kit₁ ke₁ st0 z₁.rem.val rec' = FromStoreCallEnv kit₂ ke₂ st0 z₂.rem.val rec' :=
    fun _ => g5bp_seqEnv_congr (g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr rfl rfl)) rfl
  have htf : FromTrustedFalseEnv z₁ = FromTrustedFalseEnv z₂ :=
    g5bp_seqEnv_congr (g5bp_stringCloneEnv_eq rfl) rfl
  have htt : ∀ rec' k,
      FromTrustedTrueEnv kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec' k =
        FromTrustedTrueEnv kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec' k :=
    fun rec' k =>
      g5bp_seqEnv_congr (hsave_step k)
        (funext fun evs => g5bp_or_congr rfl (congrFun (hstore_call rec') evs))
  have hkr : ∀ rec' k,
      FromKeyReadyEnv kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec' k =
        FromKeyReadyEnv kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec' k :=
    fun rec' k =>
      g5bp_seqEnv_congr (htrust_step k)
        (funext fun evs =>
          g5bp_or_congr rfl (g5bp_or_congr (congrFun htf evs) (congrFun (htt rec' k) evs)))
  have hdecRec : ∀ rec,
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.decryptRecord
          P.C (pqxdhSpqrModel P) uuidTryParse z₁ rec =
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.decryptRecord
          P.C (pqxdhSpqrModel P) uuidTryParse z₂ rec := by
    intro rec
    unfold CryptoVerification.LibsignalPublicApi.MessageDecrypt.decryptRecord
    rfl
  have hps : ∀ rec,
      FromPostSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec =
        FromPostSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec :=
    fun rec => funext fun evs =>
      g5bp_or_congr rfl
        (g5bp_exists_congr fun pt =>
          g5bp_exists_congr fun rec' =>
            g5bp_exists_congr fun _ =>
              g5bp_exists_congr fun k =>
                g5bp_and_congr (congrArg (· = .ok (pt, rec')) (hdecRec rec))
                  (g5bp_and_congr rfl
                    (g5bp_and_congr rfl (congrFun (hkr rec' k) evs))))
  have hrd : ∀ G ses_st,
      LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.RecordDecryptEnv
          (W2RealTdEnv W.C.F W.Q.K)
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₁ 0#64 G ses_st) =
        LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.RecordDecryptEnv
          (W2RealTdEnv W.C.F W.Q.K)
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₂ 0#64 G ses_st) := by
    intro G ses_st
    funext evs
    unfold LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.RecordDecryptEnv
      LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.FromVEnv W2RealTdEnv
    rfl
  have hrs : ∀ rec G ses_st,
      FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse (W2RealTdEnv W.C.F W.Q.K)
          kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec G ses_st =
        FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse (W2RealTdEnv W.C.F W.Q.K)
          kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec G ses_st :=
    fun rec G ses_st => g5bp_seqEnv_congr (hrd G ses_st) (hps rec)
  have hlp :
      FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse (W2RealTdEnv W.C.F W.Q.K)
          kit₁ ke₁ st0 ikit₁ ike₁ ist0 scopeKit z₁ =
        FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse (W2RealTdEnv W.C.F W.Q.K)
          kit₂ ke₂ st0 ikit₂ ike₂ ist0 scopeKit z₂ :=
    g5bp_seqEnv_congr rfl
      (funext fun evs =>
        g5bp_or_congr rfl
          (g5bp_or_congr (congrFun htf evs)
            (g5bp_or_congr rfl
              (g5bp_exists_congr fun rec =>
                g5bp_exists_congr fun ses =>
                  g5bp_exists_congr fun G =>
                    g5bp_and_congr rfl
                      (g5bp_and_congr rfl
                        (g5bp_and_congr rfl
                          (congrFun (hrs rec G ses.state) evs)))))))
  funext evs
  exact congrFun (g5bp_seqEnv_congr hload_step hlp) evs

/-- `tdEnv`-parametric `r3a` ghost congruence on `CliDecryptSignalSlotEnv`. -/
theorem g5bp_decSigEnv_of_tdEnv_r3a_congr [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (htd : ∀ a₁ a₂ : TryDecryptEnvArgs,
      a₁.G = a₂.G → a₁.st = a₂.st → a₁.rem.val = a₂.rem.val →
      a₁.loc = a₂.loc → a₁.msg = a₂.msg → a₁.msgType = a₂.msgType → a₁.rest = a₂.rest →
      tdEnv a₁ = tdEnv a₂)
    (gc : RunCall) (fsp : BitVec 64)
    (w) (peerV : AddrV) (meG : AddrGhost) (msgG) (m) :
    CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets tdEnv
        (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets tdEnv
        (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (r3aDecSigGhost0 gc peerV meG m) := by
  let P : PEParams := ⟨W.C, W.Q⟩
  let x₁ := r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m
  let x₂ := r3aDecSigGhost0 gc peerV meG m
  let z₁ := CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.toDecryptGhost x₁
  let z₂ := CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.toDecryptGhost x₂
  let kit₁ := decSessKitPlaced A.repAlloc x₁.F x₁.peer cliRunBudgets
  let kit₂ := decSessKitPlaced A.repAlloc x₂.F x₂.peer cliRunBudgets
  let ke₁ := decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₁.F x₁.peer
  let ke₂ := decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₂.F x₂.peer
  let ikit₁ := decIdKitPlaced A.repAlloc x₁.F x₁.peer cliRunBudgets
  let ikit₂ := decIdKitPlaced A.repAlloc x₂.F x₂.peer cliRunBudgets
  let ike₁ := decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₁.F x₁.peer
  let ike₂ := decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₂.F x₂.peer
  let st0 := StoresGhost.opened.sessions
  let ist0 := StoresGhost.opened.identity
  have hload_step : LoadPollStepEnv kit₁ ke₁ st0 z₁.rem.val = LoadPollStepEnv kit₂ ke₂ st0 z₂.rem.val :=
    g5bp_seqEnv_congr rfl rfl
  have htrust_step : ∀ k,
      TrustStepEnv ikit₁ ike₁ ist0 z₁.rem.val k .receiving =
        TrustStepEnv ikit₂ ike₂ ist0 z₂.rem.val k .receiving :=
    fun _ => g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr rfl rfl)
  have hsave_step : ∀ k,
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.SaveStepEnv
          ikit₁ ike₁ (ikit₁.trustUpdate ist0 z₁.rem.val k .receiving (.ok true)) z₁.rem.val k =
        LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.SaveStepEnv
          ikit₂ ike₂ (ikit₂.trustUpdate ist0 z₂.rem.val k .receiving (.ok true)) z₂.rem.val k :=
    fun _ => g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr rfl rfl)
  have hstore_call : ∀ rec',
      FromStoreCallEnv kit₁ ke₁ st0 z₁.rem.val rec' = FromStoreCallEnv kit₂ ke₂ st0 z₂.rem.val rec' :=
    fun _ => g5bp_seqEnv_congr (g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr rfl rfl)) rfl
  have htf : FromTrustedFalseEnv z₁ = FromTrustedFalseEnv z₂ :=
    g5bp_seqEnv_congr (g5bp_stringCloneEnv_eq rfl) rfl
  have htt : ∀ rec' k,
      FromTrustedTrueEnv kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec' k =
        FromTrustedTrueEnv kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec' k :=
    fun rec' k =>
      g5bp_seqEnv_congr (hsave_step k)
        (funext fun evs => g5bp_or_congr rfl (congrFun (hstore_call rec') evs))
  have hkr : ∀ rec' k,
      FromKeyReadyEnv kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec' k =
        FromKeyReadyEnv kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec' k :=
    fun rec' k =>
      g5bp_seqEnv_congr (htrust_step k)
        (funext fun evs =>
          g5bp_or_congr rfl (g5bp_or_congr (congrFun htf evs) (congrFun (htt rec' k) evs)))
  have hdecRec : ∀ rec,
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.decryptRecord
          P.C (pqxdhSpqrModel P) uuidTryParse z₁ rec =
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.decryptRecord
          P.C (pqxdhSpqrModel P) uuidTryParse z₂ rec := by
    intro rec
    unfold CryptoVerification.LibsignalPublicApi.MessageDecrypt.decryptRecord
    rfl
  have hps : ∀ rec,
      FromPostSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec =
        FromPostSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec :=
    fun rec => funext fun evs =>
      g5bp_or_congr rfl
        (g5bp_exists_congr fun pt =>
          g5bp_exists_congr fun rec' =>
            g5bp_exists_congr fun _ =>
              g5bp_exists_congr fun k =>
                g5bp_and_congr (congrArg (· = .ok (pt, rec')) (hdecRec rec))
                  (g5bp_and_congr rfl
                    (g5bp_and_congr rfl (congrFun (hkr rec' k) evs))))
  have hrd : ∀ G ses_st,
      RecordDecryptEnv tdEnv
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₁ 0#64 G ses_st) =
        RecordDecryptEnv tdEnv
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₂ 0#64 G ses_st) := by
    intro G ses_st
    funext evs
    unfold RecordDecryptEnv LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.FromVEnv
    exact g5bp_ite_congr Iff.rfl
      (g5bp_exists_congr fun G₁ =>
        g5bp_and_congr rfl
          (congrFun
            (g5bp_seqEnv_congr rfl
              (g5bp_seqEnv_congr
                (htd
                  (recordTryDecryptEnvArgs
                    (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₁ 0#64 G ses_st) G₁)
                  (recordTryDecryptEnvArgs
                    (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₂ 0#64 G ses_st) G₁)
                  rfl rfl rfl rfl rfl rfl rfl)
                rfl))
            evs))
      rfl
  have hrs : ∀ rec G ses_st,
      FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse tdEnv
          kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec G ses_st =
        FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse tdEnv
          kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec G ses_st :=
    fun rec G ses_st => g5bp_seqEnv_congr (hrd G ses_st) (hps rec)
  have hlp :
      FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse tdEnv
          kit₁ ke₁ st0 ikit₁ ike₁ ist0 scopeKit z₁ =
        FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse tdEnv
          kit₂ ke₂ st0 ikit₂ ike₂ ist0 scopeKit z₂ :=
    g5bp_seqEnv_congr rfl
      (funext fun evs =>
        g5bp_or_congr rfl
          (g5bp_or_congr (congrFun htf evs)
            (g5bp_or_congr rfl
              (g5bp_exists_congr fun rec =>
                g5bp_exists_congr fun ses =>
                  g5bp_exists_congr fun G =>
                    g5bp_and_congr rfl
                      (g5bp_and_congr rfl
                        (g5bp_and_congr rfl
                          (congrFun (hrs rec G ses.state) evs)))))))
  funext evs
  exact congrFun (g5bp_seqEnv_congr hload_step hlp) evs

/-- Ghost congruence for `TryDecryptCliEnvOfPure` across `a₁.rem.val = a₂.rem.val` and
arbitrary `msgG`. -/
theorem g5bp_tryDecryptCliEnvOfPure_congr
    (C : Crypto) (S : CryptoVerification.LibsignalTripleRatchet.SpqrModel)
    (fmtWriteEnv : List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (a₁ a₂ : TryDecryptEnvArgs)
    (hG : a₁.G = a₂.G) (hst : a₁.st = a₂.st) (hrem : a₁.rem.val = a₂.rem.val)
    (hloc : a₁.loc = a₂.loc) (hmsg : a₁.msg = a₂.msg)
    (htype : a₁.msgType = a₂.msgType) (hrest : a₁.rest = a₂.rest) :
    TryDecryptCliEnvOfPure C S fmtWriteEnv RecvBytesEnv fmtEnv a₁ =
      TryDecryptCliEnvOfPure C S fmtWriteEnv RecvBytesEnv fmtEnv a₂ := by
  rcases a₁ with ⟨G, st, rem₁, loc, msgG₁, msg, msgType, rest⟩
  rcases a₂ with ⟨G₂, st₂, rem₂, loc₂, msgG₂, msg₂, msgType₂, rest₂⟩
  dsimp only at hG hst hrem hloc hmsg htype hrest
  subst hG hst hloc hmsg htype hrest
  let x₁ := tryDecryptEnvArgsToGhost ⟨G, st, rem₁, loc, msgG₁, msg, msgType, rest⟩
  let x₂ := tryDecryptEnvArgsToGhost ⟨G, st, rem₂, loc, msgG₂, msg, msgType, rest⟩
  have hser :
      CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
          (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse) rem₁ loc =
        CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
          (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse) rem₂ loc :=
    g5bp_serializeAddresses_fst_eq loc hrem
  have hvmac : ∀ tr mks,
      vmacEvents C.F uuidTryParse x₁ tr mks = vmacEvents C.F uuidTryParse x₂ tr mks := by
    intro tr mks
    exact congrArg
      (fun sa =>
        if (CryptoGames.LibsignalSession.computeMac C.F
              tr.remoteIdentityKey tr.localIdentityKey mks.macKey
              (msg.serialized.take (msg.serialized.length - 8)) ==
            msg.serialized.drop (msg.serialized.length - 8)) &&
            msg.addresses.isSome && sa.isSome then
          LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget.computeMacEvents ++
            (LibsignalBinary.Heap.rustAllocEvents 36 1 ++
              LibsignalBinary.Heap.rustDeallocEvents 36 1)
        else
          LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget.computeMacEvents)
      hser
  have hs7 : ∀ tr mks newPqrState,
      s7Env C.F uuidTryParse x₁ tr mks newPqrState =
        s7Env C.F uuidTryParse x₂ tr mks newPqrState :=
    fun tr mks _ =>
      funext fun evs =>
        congrFun
          (g5bp_seqEnv_congr
            (g5bp_seqEnv_congr (funext fun e => congrArg (e = ·) (hvmac tr mks)) rfl)
            rfl)
          evs
  have hs7g : ∀ trG tr st1 mks newPqrState,
      FromS7GenEnv C uuidTryParse
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
        (s7Env C.F uuidTryParse)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
        x₁ trG tr st1 mks newPqrState =
      FromS7GenEnv C uuidTryParse
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
        (s7Env C.F uuidTryParse)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
        x₂ trG tr st1 mks newPqrState := by
    intro trG tr st1 mks newPqrState
    have hcond :
        msg.verifyMacWithAddresses C.F
            (CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
              (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse) rem₁ loc)
            tr.remoteIdentityKey tr.localIdentityKey mks.macKey =
          msg.verifyMacWithAddresses C.F
            (CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
              (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse) rem₂ loc)
            tr.remoteIdentityKey tr.localIdentityKey mks.macKey :=
      congrArg
        (fun sa => msg.verifyMacWithAddresses C.F sa tr.remoteIdentityKey tr.localIdentityKey mks.macKey)
        hser
    have hs8eq :
        FromS8GenEnv
            (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
            x₁ trG tr st1 mks newPqrState =
          FromS8GenEnv
            (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
            x₂ trG tr st1 mks newPqrState := rfl
    unfold FromS7GenEnv
    exact g5bp_ite_congr
      (iff_of_eq (congrArg (· = true) hcond))
      (g5bp_seqEnv_congr (hs7 tr mks newPqrState) hs8eq)
      (g5bp_seqEnv_congr (hs7 tr mks newPqrState) rfl)
  have hs6g : ∀ trG tr st1 mkg newPqrState pqrKey,
      FromS6GenEnv C uuidTryParse
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
        (s7Env C.F uuidTryParse)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
        x₁ trG tr st1 mkg newPqrState pqrKey =
      FromS6GenEnv C uuidTryParse
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
        (s7Env C.F uuidTryParse)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
        x₂ trG tr st1 mkg newPqrState pqrKey := by
    intro trG tr st1 mkg newPqrState pqrKey
    unfold FromS6GenEnv
    exact g5bp_seqEnv_congr rfl (hs7g trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState)
  have hs5g : ∀ trG tr st1 mkg,
      FromS5GenEnv C uuidTryParse S
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
        (PqRecvEnv S RecvBytesEnv fmtEnv)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
        (s7Env C.F uuidTryParse)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
        x₁ trG tr st1 mkg =
      FromS5GenEnv C uuidTryParse S
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
        (PqRecvEnv S RecvBytesEnv fmtEnv)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
        (s7Env C.F uuidTryParse)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
        x₂ trG tr st1 mkg := by
    intro trG tr st1 mkg
    unfold FromS5GenEnv
    dsimp only [x₁, x₂, tryDecryptEnvArgsToGhost]
    rcases S.recv tr.pqrState msg.pqRatchet with _ | ⟨newPqrState, pqrKey⟩
    · rfl
    · exact g5bp_seqEnv_congr rfl (hs6g trG tr st1 mkg newPqrState pqrKey)
  have hs4g : ∀ trG tr st1 ck,
      FromS4GenEnv C uuidTryParse S
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
        (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptCmkSeg4Env fmtWriteEnv)
        (PqRecvEnv S RecvBytesEnv fmtEnv)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
        (s7Env C.F uuidTryParse)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
        x₁ trG tr st1 ck =
      FromS4GenEnv C uuidTryParse S
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
        (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptCmkSeg4Env fmtWriteEnv)
        (PqRecvEnv S RecvBytesEnv fmtEnv)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
        (s7Env C.F uuidTryParse)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
        x₂ trG tr st1 ck := by
    intro trG tr st1 ck
    unfold FromS4GenEnv
    dsimp only [x₁, x₂, tryDecryptEnvArgsToGhost]
    rcases CryptoGames.LibsignalSession.Mut.exec
        (CryptoGames.LibsignalSession.RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck
          msg.counter msgType) tr.ratchet with ⟨_ | mkg, r2⟩
    · rfl
    · exact g5bp_seqEnv_congr rfl (hs5g trG { tr with ratchet := r2 } st1 mkg)
  have hs3g : ∀ trG tr st1,
      FromS3GenEnv C uuidTryParse S
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv C)
        (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptCmkSeg4Env fmtWriteEnv)
        (PqRecvEnv S RecvBytesEnv fmtEnv)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
        (s7Env C.F uuidTryParse)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
        x₁ trG tr st1 =
      FromS3GenEnv C uuidTryParse S
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv C)
        (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptCmkSeg4Env fmtWriteEnv)
        (PqRecvEnv S RecvBytesEnv fmtEnv)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
        (s7Env C.F uuidTryParse)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
        x₂ trG tr st1 := by
    intro trG tr st1
    unfold FromS3GenEnv
    dsimp only [x₁, x₂, tryDecryptEnvArgsToGhost]
    rcases CryptoGames.LibsignalSession.Mut.exec
        (CryptoGames.LibsignalSession.RatchetState.dhRatchetStep C msg.senderRatchetKey
          (CryptoVerification.LibsignalTripleRatchetRepr.coinsOf rest)) tr.ratchet with ⟨_ | ck, r1⟩
    · rfl
    · exact g5bp_seqEnv_congr rfl
        (hs4g (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.s3AfterTrGhost trG
          tr.ratchet.receiverChains.length) { tr with ratchet := r1 } st1 ck)
  have hs2g : ∀ trG tr st1,
      FromS2GenEnv C uuidTryParse S
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv C)
        (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptCmkSeg4Env fmtWriteEnv)
        (PqRecvEnv S RecvBytesEnv fmtEnv)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
        (s7Env C.F uuidTryParse)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
        x₁ trG tr st1 =
      FromS2GenEnv C uuidTryParse S
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv C)
        (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptCmkSeg4Env fmtWriteEnv)
        (PqRecvEnv S RecvBytesEnv fmtEnv)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
        (s7Env C.F uuidTryParse)
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
        x₂ trG tr st1 := by
    intro trG tr st1
    unfold FromS2GenEnv
    dsimp only [x₁, x₂, tryDecryptEnvArgsToGhost]
    rcases tr.ratchet.findReceiverChainKey msg.senderRatchetKey with _ | (_ | ck)
    · rfl
    · exact hs3g trG tr st1
    · exact hs4g trG tr st1 ck
  unfold TryDecryptCliEnvOfPure
  dsimp only
  rcases CryptoGames.LibsignalSession.Mut.exec
      CryptoGames.LibsignalSession.TripleRatchet.fromSessionState st with ⟨_ | tr0, st1⟩
  · rfl
  · exact g5bp_seqEnv_congr rfl
      (hs2g (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.s1InitTrGhost G) tr0 st1)

/-- Ghost congruence for `TryDecryptCliLinkedEnvOf maxOps C K`. -/
theorem g5bp_tryDecryptCliLinkedEnvOf_r3a_congr
    (maxOps : Nat) (C : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (a₁ a₂ : TryDecryptEnvArgs)
    (hG : a₁.G = a₂.G) (hst : a₁.st = a₂.st) (hrem : a₁.rem.val = a₂.rem.val)
    (hloc : a₁.loc = a₂.loc) (hmsg : a₁.msg = a₂.msg)
    (htype : a₁.msgType = a₂.msgType) (hrest : a₁.rest = a₂.rest) :
    TryDecryptCliLinkedEnvOf maxOps C K a₁ = TryDecryptCliLinkedEnvOf maxOps C K a₂ :=
  g5bp_tryDecryptCliEnvOfPure_congr C (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K)
    LibsignalBinary.Heap.SpecBudget.FmtWriteEnv
    (LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.SpqrRecvC07C09aBytesEnvOf maxOps C.F K)
    LibsignalBinary.Heap.SpecBudget.FormatInnerEnv a₁ a₂ hG hst hrem hloc hmsg htype hrest

/-- Ghost congruence on `CliDecryptSignalSlotEnv` at `TryDecryptCliLinkedEnvOf maxOps W.C W.Q.K`. -/
theorem g5bp_decSigEnv_linkedOf_r3a_congr [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (maxOps : Nat)
    (gc : RunCall) (fsp : BitVec 64)
    (w) (peerV : AddrV) (meG : AddrGhost) (msgG) (m) :
    CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets
        (TryDecryptCliLinkedEnvOf maxOps W.C W.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets
        (TryDecryptCliLinkedEnvOf maxOps W.C W.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (r3aDecSigGhost0 gc peerV meG m) :=
  g5bp_decSigEnv_of_tdEnv_r3a_congr W A (TryDecryptCliLinkedEnvOf maxOps W.C W.Q.K)
    (g5bp_tryDecryptCliLinkedEnvOf_r3a_congr maxOps W.C W.Q.K)
    gc fsp w peerV meG msgG m

/-- Lifts `r3a` ghost congruence across any `(FsFiles → AddrVal → Prop)` guard. -/
theorem g5bp_guardedDecSigEnv_r3a_congr
    (G : FsFiles → AddrVal → Prop)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop)
    (hdec : ∀ gc fsp w peerV meG msgG m,
      DecSigEnv (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
        DecSigEnv (r3aDecSigGhost0 gc peerV meG m))
    (gc : RunCall) (fsp : BitVec 64)
    (w) (peerV : AddrV) (meG : AddrGhost) (msgG) (m) :
    (fun (x : DecSigGhost) evs => G x.F x.peer.val → DecSigEnv x evs)
        (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
      (fun (x : DecSigGhost) evs => G x.F x.peer.val → DecSigEnv x evs)
        (r3aDecSigGhost0 gc peerV meG m) := by
  have hf : (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m).F =
      (r3aDecSigGhost0 gc peerV meG m).F := rfl
  have hval : (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m).peer.val =
      (r3aDecSigGhost0 gc peerV meG m).peer.val := rfl
  funext evs
  dsimp only
  rw [hf, hval, hdec gc fsp w peerV meG msgG m]

/-- Ghost congruence for `DecPkD3UntypedEnvOf`. -/
theorem g5bp_decPkD3UntypedEnvOf_ghost_congr [LibsignalPlacement]
    {A : RustAlloc} (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (AcceptErrEnv : List AllocEvent → Prop)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (_hm : x.me.val = y.me.val)
    (_hs : x.stores = y.stores)
    (_hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (_hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    DecPkD3UntypedEnvOf (A := A) B ReadEnv DeserEnv AcceptErrEnv x =
      DecPkD3UntypedEnvOf (A := A) B ReadEnv DeserEnv AcceptErrEnv y := by
  have hsc : StringCloneEnv x.peer.name = StringCloneEnv y.peer.name :=
    g5bp_stringCloneEnv_eq hp
  have hsessPoll :
      (cliPollSessBudgetEnv A x.F x.peer B ReadEnv DeserEnv).loadPollEnv
        StoresGhost.opened.sessions x.peer.val =
      (cliPollSessBudgetEnv A y.F y.peer B ReadEnv DeserEnv).loadPollEnv
        StoresGhost.opened.sessions y.peer.val := by
    unfold cliPollSessBudgetEnv cliSessionKitDefaultBudgetEnv cliSessionKitBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.cliSessionKitLoadPollEnv
    dsimp only
    rw [hf, hp]
  have hsess :
      LoadStepEnv
        (cliPollSessKitPlaced A x.F scopeKit x.peer (cliKitStk B))
        (cliPollSessBudgetEnv A x.F x.peer B ReadEnv DeserEnv)
        StoresGhost.opened.sessions x.peer.val =
      LoadStepEnv
        (cliPollSessKitPlaced A y.F scopeKit y.peer (cliKitStk B))
        (cliPollSessBudgetEnv A y.F y.peer B ReadEnv DeserEnv)
        StoresGhost.opened.sessions y.peer.val :=
    g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr hsessPoll rfl)
  have htrustPoll :
      (cliPollIdBudgetEnv A x.F x.peer B ReadEnv).trustPollEnv
        StoresGhost.opened.identity x.peer.val x.msg.identityKey .receiving =
      (cliPollIdBudgetEnv A y.F y.peer B ReadEnv).trustPollEnv
        StoresGhost.opened.identity y.peer.val y.msg.identityKey .receiving := by
    unfold cliPollIdBudgetEnv cliIdStoreFullBudgetEnv cliIdentityKitDefaultBudgetEnv
      cliIdentityKitBudgetEnv cliIdentityKitTrustPollEnv
    dsimp only
    rw [hf, hp]
  have htrust :
      TrustStepEnv
        (cliPollIdKitPlaced A x.F x.peer (cliKitStk B))
        (cliPollIdBudgetEnv A x.F x.peer B ReadEnv)
        StoresGhost.opened.identity x.peer.val x.msg.identityKey .receiving =
      TrustStepEnv
        (cliPollIdKitPlaced A y.F y.peer (cliKitStk B))
        (cliPollIdBudgetEnv A y.F y.peer B ReadEnv)
        StoresGhost.opened.identity y.peer.val y.msg.identityKey .receiving :=
    g5bp_seqEnv_congr rfl (g5bp_seqEnv_congr htrustPoll rfl)
  have hp1u :
      CliDpPollUntrustedEnv (A := A) B ReadEnv DeserEnv x =
        CliDpPollUntrustedEnv (A := A) B ReadEnv DeserEnv y :=
    g5bp_seqEnv_congr hsess (g5bp_seqEnv_congr htrust (g5bp_seqEnv_congr hsc rfl))
  have hp1ok :
      StageP1OkEnv
        (cliPollSessKitPlaced A x.F scopeKit x.peer (cliKitStk B))
        (cliPollSessBudgetEnv A x.F x.peer B ReadEnv DeserEnv)
        StoresGhost.opened.sessions
        (cliPollIdKitPlaced A x.F x.peer (cliKitStk B))
        (cliPollIdBudgetEnv A x.F x.peer B ReadEnv)
        StoresGhost.opened.identity x.peer.val x.msg.identityKey =
      StageP1OkEnv
        (cliPollSessKitPlaced A y.F scopeKit y.peer (cliKitStk B))
        (cliPollSessBudgetEnv A y.F y.peer B ReadEnv DeserEnv)
        StoresGhost.opened.sessions
        (cliPollIdKitPlaced A y.F y.peer (cliKitStk B))
        (cliPollIdBudgetEnv A y.F y.peer B ReadEnv)
        StoresGhost.opened.identity y.peer.val y.msg.identityKey :=
    g5bp_seqEnv_congr hsess htrust
  have hselfBox :
      (cliPollSelfKitPlaced A x.F x.peer (cliKitStk B)).kpBoxSize =
        (cliPollSelfKitPlaced A y.F y.peer (cliKitStk B)).kpBoxSize := rfl
  have hselfKp :
      (cliPollSelfBudgetEnv A x.F x.peer (cliKitStk B) ReadEnv).kpPollEnv
        StoresGhost.opened.identity =
      (cliPollSelfBudgetEnv A y.F y.peer (cliKitStk B) ReadEnv).kpPollEnv
        StoresGhost.opened.identity := by
    unfold cliPollSelfBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget.cliPollSelfKpPollEnv
    dsimp only
    rw [hf]
  have hp2 : ∀ opt,
      StageP2UntypedRejectEnv (A := A) B ReadEnv AcceptErrEnv x opt =
        StageP2UntypedRejectEnv (A := A) B ReadEnv AcceptErrEnv y opt := by
    intro opt
    funext evs
    unfold StageP2UntypedRejectEnv StageP2BadKemRejectEnv
    dsimp only
    rw [hselfBox, hselfKp, hf, hmsg]
  funext evs
  unfold DecPkD3UntypedEnvOf DecPkD3UntypedPollEnv
  exact g5bp_or_congr (congrFun hp1u evs)
    (g5bp_exists_congr fun opt => congrFun (g5bp_seqEnv_congr hp1ok (hp2 opt)) evs)

/-! ## `CliPubCalleesFrozenPlaced` Dischargers -/

/-- Slot-body-parametric discharger for `CliPubCalleesFrozenPlaced` at
`ReadFileRuleEnvFixed cliIo.rd`, `DecPkD3UntypedEnvOf`, and `PksmTryFromEnv` for any `EncEnv` and
`DecSigEnv` satisfying `r2` and `r3a` ghost congruence. -/
theorem g5bp_cliPubCallees_of_slotEnvs_frozen_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (W : CliHooks)
    (EncEnv : EncGhost → List AllocEvent → Prop)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd))
    (henc : ∀ gc peerV peerG meG fsp, peerG.val = addrValOf peerV →
      EncEnv (r2EncGhost gc peerG meG fsp) =
        EncEnv (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64))
    (hdec : ∀ gc fsp w peerV meG msgG m,
      DecSigEnv (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
        DecSigEnv (r3aDecSigGhost0 gc peerV meG m)) :
    CliPubCalleesFrozenPlaced mmpl gh A lim
      (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (g5bp_slotEnvsOf EncEnv DecSigEnv
        (realCliInitBinarySlotEnvFixed W)
        (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets
          (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
      (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (g5bp_slotEnvsOf EncEnv DecSigEnv
          (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets
            (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        PksmTryFromEnv)
      W :=
  cliPubCallees_d2c_frozen_ok mmpl gh W hHooks
    (hole3_initEnv_r1c_congr W)
    henc
    hdec
    hole3_pksmTryFromEnv_congr
    (g5bp_decPkD3UntypedEnvOf_ghost_congr cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv)

/-- `CliPubCalleesFrozenPlaced` at `g5bp_binaryKitRunSlotEnvsOfSend W A cliRunBudgets sendEnv`. -/
theorem g5bp_cliPubCallees_of_sendEnv_frozen_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (W : CliHooks) (sendEnv : SpqrSendBudgetEnv)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd)) :
    CliPubCalleesFrozenPlaced mmpl gh A lim
      (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (g5bp_binaryKitRunSlotEnvsOfSend W A cliRunBudgets
        sendEnv
        (realCliInitBinarySlotEnvFixed W)
        (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets
          (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
      (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (g5bp_binaryKitRunSlotEnvsOfSend W A cliRunBudgets
          sendEnv
          (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets
            (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        PksmTryFromEnv)
      W :=
  g5bp_cliPubCallees_of_slotEnvs_frozen_ok mmpl gh W _ _ hHooks
    (g5bp_encEnv_r2_congr W A sendEnv)
    (g5bp_decSigEnv_r3a_congr W A)

/-- `CliPubCalleesFrozenPlaced` at `g5bp_binaryKitRunSlotEnvsGuardedOfSend`. -/
theorem g5bp_cliPubCallees_guarded_of_sendEnv_frozen_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (W : CliHooks) (sendEnv : SpqrSendBudgetEnv)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd)) :
    CliPubCalleesFrozenPlaced mmpl gh A lim
      (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (g5bp_binaryKitRunSlotEnvsGuardedOfSend W A cliRunBudgets
        sendEnv
        (realCliInitBinarySlotEnvFixed W)
        (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets
          (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
      (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (g5bp_binaryKitRunSlotEnvsGuardedOfSend W A cliRunBudgets
          sendEnv
          (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets
            (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        PksmTryFromEnv)
      W :=
  g5bp_cliPubCallees_of_slotEnvs_frozen_ok mmpl gh W _ _ hHooks
    (g5bp_guardedEncEnv_r2_congr (PeerSpqrStateTight640 W.C.F W.Q.K) _
      (g5bp_encEnv_r2_congr W A sendEnv))
    (g5bp_guardedDecSigEnv_r3a_congr (PeerSpqrStateTight640 W.C.F W.Q.K) _
      (g5bp_decSigEnv_r3a_congr W A))

/-- `CliPubCalleesFrozenPlaced` at `g5bp_binaryKitRunSlotEnvsOfSendDecSigGuarded`. -/
theorem g5bp_cliPubCallees_of_sendEnv_decSigGuarded_frozen_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (W : CliHooks) (sendEnv : SpqrSendBudgetEnv) (maxOps : Nat := 109)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd)) :
    CliPubCalleesFrozenPlaced mmpl gh A lim
      (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (g5bp_binaryKitRunSlotEnvsOfSendDecSigGuarded W A cliRunBudgets
        sendEnv maxOps
        (realCliInitBinarySlotEnvFixed W)
        (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets
          (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
      (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (g5bp_binaryKitRunSlotEnvsOfSendDecSigGuarded W A cliRunBudgets
          sendEnv maxOps
          (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets
            (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        PksmTryFromEnv)
      W :=
  g5bp_cliPubCallees_of_slotEnvs_frozen_ok mmpl gh W _ _ hHooks
    (g5bp_encEnv_r2_congr W A sendEnv)
    (g5bp_guardedDecSigEnv_r3a_congr (PeerSpqrStateTight640 W.C.F W.Q.K) _
      (g5bp_decSigEnv_linkedOf_r3a_congr W A maxOps))

/-- `CliPubCalleesFrozenPlaced` at `ElfSlicesPqOomHole3Cut.binaryKitRunSlotEnvsExact`,
`DecPkD3UntypedEnvOf`, and `PksmTryFromEnv`. -/
theorem g5bp_cliPubCallees_exact_frozen_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (W : CliHooks)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd)) :
    CliPubCalleesFrozenPlaced mmpl gh A lim
      (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (binaryKitRunSlotEnvsExact W A cliRunBudgets
        (realCliInitBinarySlotEnvFixed W)
        (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets
          (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
      (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (binaryKitRunSlotEnvsExact W A cliRunBudgets
          (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets
            (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        PksmTryFromEnv)
      W :=
  g5bp_cliPubCallees_of_slotEnvs_frozen_ok mmpl gh W _ _ hHooks
    (hole3_encEnv_r2_congr W A) (hole3_decSigEnv_r3a_congr W A)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bPub
