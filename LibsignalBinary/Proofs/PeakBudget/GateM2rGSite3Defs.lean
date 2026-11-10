/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Lower-Layer `StatesRecvE`-Parametric `W4` Slot Definitions

Mirrors the definition chain of
`GateM2rGStatesRecvTwins.m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'` using only
lower-layer imports, so `RealCliDecPkGuardedDefs.cliDecPkCanonSlotEnvExact` is definitionally
equal (`GateM2rGSite3Eq.m2rgs3_cliDecPkCanonSlotEnvExact_eq_m2rg`) without introducing a module
import cycle.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.GateM2rGSite3Defs

open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB spqrAuthApi
   spqrPolyApi spqrV1)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W4BinaryStageP2MatchedWideEnv W4CloneACDomEnv W4CloneBDomEnv)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1UntrustedEnvAllFixed
   W4BinaryStageP2PathAWideEnvAllFixed W4BinaryStageP2PathCWideEnvAllFixed
   W4BinaryStageP4MatchedWideEnvAllFixed W4BinaryStageP4PathAWideEnvAllFixed
   W4BinaryStageP4PathCWideEnvAllFixed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak (optDeallocListEvs)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (W4BoundedEvs)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4DecryptPrekeySlotParams W4StageP3WideEnv W4TryDecryptCloneFailWideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
  (VerNeTightTopEnv W4StageP3Prev1WideEnvOf)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4ArchivedTrialCmk W4BinaryCallSiteDomCmk W4BinaryRecvPrekeyParamsCmk W4FailedTryDecryptCallCmk
   W4LoopAdvEnv W4RecvPrekeyRealParamsCmk W4TrialDecCmkEnv W4TrialDropCmkEnv
   w4c_SpqrRecvC07TightLinkedEnvOf w4c_TryDecryptCliEnvOfPure w4c_TryDecryptCliFailEnvOfPure
   w4c_defaultDecodeMaxOps)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv TryDecryptEnvArgs)

/-- `(maxOps, StatesRecvE)`-parametric `SpqrRecvC07C09aTightLinkedEnvOf`, matching
`GateM2rGStatesRecvTwins.m2rg_SpqrRecvC07C09aTightLinkedEnvOf'`. -/
def m2rgs3_SpqrRecvC07C09aTightLinkedEnvOf' (F : ShaCompress) (K : MlKem) (maxOps : Nat)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  w4c_SpqrRecvC07TightLinkedEnvOf F K maxOps StatesRecvE
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-- `(maxOps, StatesRecvE)`-parametric existentially lifted 12-ghost linked `spqr::recv`
byte-slice envelope, matching `GateM2rGStatesRecvTwins.m2rg_SpqrRecvC07C09aBytesEnvOf'`. -/
def m2rgs3_SpqrRecvC07C09aBytesEnvOf' (F : ShaCompress) (K : MlKem) (maxOps : Nat)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBs _msgBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
    m2rgs3_SpqrRecvC07C09aTightLinkedEnvOf' F K maxOps StatesRecvE
      stBs pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-- `(LoopAdvEnv, maxOps, StatesRecvE)`-parametric linked Block-`507` `try_decrypt_with_state` CLI
envelope, matching `GateM2rGStatesRecvTwins.m2rg_TryDecryptCliLinkedEnvOf'`. -/
abbrev m2rgs3_TryDecryptCliLinkedEnvOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  w4c_TryDecryptCliEnvOfPure LoopAdvEnv C (spqrV1 C.F K)
    FmtWriteEnv (m2rgs3_SpqrRecvC07C09aBytesEnvOf' C.F K maxOps StatesRecvE) FormatInnerEnv

/-- `(LoopAdvEnv, maxOps, StatesRecvE)`-parametric failed-trial linked `try_decrypt_with_state`
envelope, matching `GateM2rGStatesRecvTwins.m2rg_TryDecryptCliLinkedFailEnvOf'`. -/
abbrev m2rgs3_TryDecryptCliLinkedFailEnvOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  w4c_TryDecryptCliFailEnvOfPure LoopAdvEnv C (spqrV1 C.F K)
    FmtWriteEnv (m2rgs3_SpqrRecvC07C09aBytesEnvOf' C.F K maxOps StatesRecvE) FormatInnerEnv

/-- `(F, K)`-indexed `States.recv` protocol envelope family, matching
`GateM2rGStatesRecvTwins.m2rg_StatesRecvEnvFam`. -/
abbrev m2rgs3_StatesRecvEnvFam : Type :=
  ∀ (F : ShaCompress), MlKem →
    States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi → List AllocEvent → Prop

/-- Failed-trial `try_decrypt` and drop-cancellation envelope twin. -/
def m2rgs3_W4FailedTdCancelCmkEnvOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (fc : W4FailedTryDecryptCallCmk) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    ConcatEnv (m2rgs3_TryDecryptCliLinkedFailEnvOf' LoopAdvEnv maxOps C K StatesRecvE fc.td.a)
      (· = optDeallocListEvs fc.failDropPairs) evs

/-- Archived-trial version-mismatch or cloned-session failed `try_decrypt_pq` envelope twin. -/
def m2rgs3_W4TrialRunWideCmkEnvOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem)
    (StatesRecvE : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (x : W4ArchivedTrialCmk) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    W4TryDecryptCloneFailWideEnv (SegCloneEnv x.G_tr x.ses_tr.state)
      (m2rgs3_W4FailedTdCancelCmkEnvOf' LoopAdvEnv maxOps C K StatesRecvE x.fc_tr)
      (· = dropClonedSessionEvents x.G_tr x.ses_tr.state) evs

/-- `W4DecryptPrekeySlotParams` twin parameterized by `StatesRecvFK`. -/
def m2rgs3_mkW4RecvPrekeyWideCmkSlotParamsOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (R : W4RecvPrekeyRealParamsCmk) :
    W4DecryptPrekeySlotParams W4ArchivedTrialCmk where
  rd := R.rd
  DeserEnv := RecordDeserializeCancelEnv
  files := R.files
  ownDir := StoresGhost.opened.identity.own
  peersDir := StoresGhost.opened.identity.peers
  spkDir := StoresGhost.opened.signed
  kpkDir := R.kpkDir
  opkDir := StoresGhost.opened.oneTime
  sessDir := StoresGhost.opened.sessions
  peer := R.peer
  hasOpk := R.hasOpk
  spkId := R.spkId
  kpkId := R.kpkId
  opkId := R.opkId
  kpkMarkName := R.kpkMarkName
  ownKeyName := R.ownKeyName
  ownRegName := R.ownRegName
  F := R.C.F
  x_res := R.x_res
  x_spqr := R.x_spqr
  G_cur := R.G_cur
  st_cur := R.st_cur
  CurTrialFailEnv :=
    if R.hasCurSession then
      m2rgs3_W4FailedTdCancelCmkEnvOf' LoopAdvEnv maxOps R.C R.K (StatesRecvFK R.C.F R.K) R.fc_cur
    else fun _ => False
  DecEnv := W4TrialDecCmkEnv
  TrialEnv := m2rgs3_W4TrialRunWideCmkEnvOf' LoopAdvEnv maxOps R.C R.K (StatesRecvFK R.C.F R.K)
  DropEnv := W4TrialDropCmkEnv
  archivedTrials := R.archivedTrials
  g_arch := R.g_arch
  r_arch := R.r_arch
  VecPushEnv := W4BoundedEvs 1 192
  TryDecEnv :=
    if R.isPathB then
      m2rgs3_TryDecryptCliLinkedEnvOf' LoopAdvEnv maxOps R.C R.K (StatesRecvFK R.C.F R.K) R.td_B.a
    else fun _ => False
  g_out0 := R.g_out0
  r_out0 := R.r_out0
  G_out1 := R.G_out1
  sess_out1 := R.sess_out1
  enc_prev1 := R.enc_prev1

/-- Path A / Path C Stage-P3 `try_decrypt` envelope twin. -/
def m2rgs3_W4RecvPrekeyTryDecACCmkEnvOf' (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (R : W4RecvPrekeyRealParamsCmk) (evs : List AllocEvent) : Prop :=
  if R.isPathAC then
    m2rgs3_TryDecryptCliLinkedEnvOf' LoopAdvEnv maxOps R.C R.K (StatesRecvFK R.C.F R.K) R.td_AC.a evs
  else False

/-- 4-arm `P3PathCEnv`-parametric binary-kit W4 (`recv-prekey`) slot envelope twin (`AllFixed`). -/
def m2rgs3_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := m2rgs3_mkW4RecvPrekeyWideCmkSlotParamsOf' LoopAdvEnv maxOps StatesRecvFK w.base
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
              w.base.g_arch w.base.r_arch))
          (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneBDomEnv P.TryDecEnv))
            (OptStageEnv
              (W4BinaryStageP4MatchedWideEnvAllFixed w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.g_out0 w.base.r_out0)))) e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files
              w.base.spkId w.base.kpkId w.base.opkId w.base.C.F w.base.x_res w.base.x_spqr))
          (SeqEnv
            (OptStageEnv
              (W4StageP3WideEnv W4CloneACDomEnv
                (m2rgs3_W4RecvPrekeyTryDecACCmkEnvOf' LoopAdvEnv maxOps StatesRecvFK w.base)))
            (OptStageEnv
              (W4BinaryStageP4PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.g_out0 w.base.r_out0)))) e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathCWideEnvAllFixed w.base.G_cur w.base.st_cur P.CurTrialFailEnv
              P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
              w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
              w.base.C.F w.base.x_res w.base.x_spqr))
          (SeqEnv (P3PathCEnv w)
            (OptStageEnv
              (W4BinaryStageP4PathCWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) e)
    FreeOnlyEvs evs

/-- `(LoopAdvEnv, maxOps, StatesRecvFK, P3PathCEnv)`-parametric unguarded W4 slot envelope twin. -/
abbrev m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf' [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
    W4BinaryCallSiteDomCmk W.C W.Q.K x.msg.message.ciphertext.length x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      m2rgs3_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv w4 evs

theorem m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'_ghost_congr [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (_hm : x.me.val = y.me.val)
    (_hs : x.stores = y.stores)
    (_hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (_hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv X W x =
      m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv X W y := by
  funext evs
  simp only [m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf', hp, hf, hmsg]

/-- `(LoopAdvEnv, maxOps, StatesRecvFK, P3PathCEnv)`-parametric `PeerSpqrStateTight640`-guarded
binary-kit W4 (`decrypt_prekey`) slot envelope twin. -/
abbrev m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf' [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
    m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'
      LoopAdvEnv maxOps StatesRecvFK P3PathCEnv X W x evs

theorem m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf'_ghost_congr [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv X W x =
      m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv X W y := by
  funext evs
  dsimp [m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf']
  rw [hf, hp,
    m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'_ghost_congr
      LoopAdvEnv maxOps StatesRecvFK P3PathCEnv X W x y hp hm hs hcp hf hc hmsg]

/-- Path-C Stage-P3 step envelope twin with `W4StageP3Prev1WideEnvOf verNeEnv`. -/
def m2rgs3_verNePrev1P3PathCEnvOf'
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (w : W4BinaryRecvPrekeyParamsCmk) : List AllocEvent → Prop :=
  OptStageEnv
    (W4StageP3Prev1WideEnvOf verNeEnv W4CloneACDomEnv
      (m2rgs3_W4RecvPrekeyTryDecACCmkEnvOf' LoopAdvEnv maxOps StatesRecvFK w.base) w.base.enc_prev1)

/-- `(verNeEnv, LoopAdvEnv, maxOps, StatesRecvFK)`-parametric unguarded `Cmk + VerNe-prev1`
binary-kit W4 slot envelope twin. -/
abbrev m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf' [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf' LoopAdvEnv maxOps StatesRecvFK
    (m2rgs3_verNePrev1P3PathCEnvOf' verNeEnv LoopAdvEnv maxOps StatesRecvFK) X W x evs

/-- Default `(VerNeTightTopEnv, CmkLoopAdvanceEvs, 109)` unguarded `Cmk + VerNe-prev1` W4 slot
envelope twin parametric in `StatesRecvFK`. -/
abbrev m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed' [LibsignalPlacement]
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'
    VerNeTightTopEnv CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps StatesRecvFK X W x evs

/-- `(verNeEnv, LoopAdvEnv, maxOps, StatesRecvFK)`-parametric `PeerSpqrStateTight640`-guarded
`Cmk + VerNe-prev1` binary-kit W4 (`decrypt_prekey`) slot envelope twin. -/
abbrev m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf' [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf' LoopAdvEnv maxOps StatesRecvFK
    (m2rgs3_verNePrev1P3PathCEnvOf' verNeEnv LoopAdvEnv maxOps StatesRecvFK) X W x evs

/-- Default `(VerNeTightTopEnv, CmkLoopAdvanceEvs, 109)` `PeerSpqrStateTight640`-guarded
`Cmk + VerNe-prev1` W4 slot envelope twin parametric in `StatesRecvFK`. -/
abbrev m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed' [LibsignalPlacement]
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
    VerNeTightTopEnv CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps StatesRecvFK X W x evs

theorem m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'_ghost_congr [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X W x =
      m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'
        verNeEnv LoopAdvEnv maxOps StatesRecvFK X W y :=
  m2rgs3_realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf'_ghost_congr
    LoopAdvEnv maxOps StatesRecvFK
    (m2rgs3_verNePrev1P3PathCEnvOf' verNeEnv LoopAdvEnv maxOps StatesRecvFK)
    X W x y hp hm hs hcp hf hc hmsg

theorem m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'_ghost_congr [LibsignalPlacement]
    (StatesRecvFK : m2rgs3_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed' StatesRecvFK X W x =
      m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed' StatesRecvFK X W y :=
  m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixedOf'_ghost_congr
    VerNeTightTopEnv CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps StatesRecvFK
    X W x y hp hm hs hcp hf hc hmsg

end LibsignalBinary.Proofs.PeakBudget.GateM2rGSite3Defs
