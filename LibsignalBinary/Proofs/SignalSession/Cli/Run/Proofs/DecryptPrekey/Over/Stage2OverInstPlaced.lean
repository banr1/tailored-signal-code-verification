/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeams
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlaced
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCallee
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromote
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SelfSpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedB
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs

/-!
# Relocatable CLI Poll Stage P2 Over-Path (`Path C`) Instantiation

Relocatable `[LibsignalPlacement]` instantiation of Stage P2 on overwrite path `Path C`,
defining `StageP2PathCOverModelRejPlaced`, `StageP2PathCOverErrPlaced`, kit-event simplifications
for `cliPoll*KitPlaced`, and `StageP2PathCOverQpanCliPlacedStmt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.CliHandshake.RespClosurePlaced

/-! ## 1. Placed Stage P2 Over-Path (`Path C`) Error & Kit Event Simplifications -/

/-- Pure model-rejection witness discharged on all 6 Stage P2 error arms on Path C (`Over`)
under `[LibsignalPlacement]`: either a store-key / identity lookup fails
(`pkStoreKeys = none ∨ keyPair =.error () ∨ regId =.error ()`) or PQXDH `acceptKeys`
rejects for every local registration ID. -/
def StageP2PathCOverModelRejPlaced [LibsignalPlacement] (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S)) : Prop :=
  ∃ (m : PreKeyMessageFields) (i : SignalMessage),
    pkToE? y.g.msg = some m ∧
    SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i ∧
    y.g.msg = pmOfE m i ∧
    ((pkStoreKeys y.g.F m = none ∨
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .error () ∨
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .error ()) ∨
     (∃ (k : ResponderPreKeySecrets) (kp : RecordCodecs.IdentityKeyPair),
       pkStoreKeys y.g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp ∧
       ∀ reg : BitVec 32,
         SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
           (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none))

/-- Exit postcondition of all 6 Stage P2 store-error and PQXDH-rejection arms on Path C (`Over`)
under `[LibsignalPlacement]`. -/
def StageP2PathCOverErrPlaced [LibsignalPlacement] (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s1 sf : State) (sp : BitVec 64) (Pf : SepProp) : Prop :=
  ∃ err : ApiError AddrVal Unit,
    err ≠ .panic ∧
    err ≠ .store () ∧
    sf.trace = s1.trace ∧
    StageP2PathCOverModelRejPlaced X W y ∧
    (Pf ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      decResAt E2E.HooksE.A0 y.out (.error err) ∗
      storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      stackAt sp (dpClosSubStack B) ∗
      anyHeap)

/-! ## 2. Placed Kit Event Simplifications (`cliPoll*KitPlaced`) -/

theorem p2Over_cliPollSpk_getEvs_placed [LibsignalPlacement] {A : RustAlloc} {F : FsFiles}
    {sid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollSpkKitPlaced A F sid σ).GetErr SignedPreKeyRecord) :
    (cliPollSpkKitPlaced A F sid σ).getEvs id ans = [] := rfl

theorem p2Over_cliPollKpk_getEvs_placed [LibsignalPlacement] {A : RustAlloc} {F : FsFiles}
    {kid sid id : BitVec 32} {kbk : PublicKey} {σ : DpKitStk}
    (ans : Except (cliPollKpkKitPlaced A F kid sid kbk σ).GetErr KyberPreKeyRecord) :
    (cliPollKpkKitPlaced A F kid sid kbk σ).getEvs id ans = [] := rfl

theorem p2Over_cliPollPk_getEvs_placed [LibsignalPlacement] {A : RustAlloc} {F : FsFiles}
    {pid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollPkKitPlaced A F pid σ).GetErr PreKeyRecord) :
    (cliPollPkKitPlaced A F pid σ).getEvs id ans = [] := rfl

theorem p2Over_cliPollPk_opkOkEvs_placed [LibsignalPlacement] {A : RustAlloc} {F : FsFiles}
    {pid : BitVec 32} {σ : DpKitStk}
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkEvs (cliPollPkKitPlaced A F pid σ) opt wOpk = [] := by
  cases opt <;> rfl

theorem p2Over_cliPollPk_opkOkUpdate_placed [LibsignalPlacement] (A : RustAlloc) (F : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk)
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkUpdate (cliPollPkKitPlaced A F pid σ) StoresGhost.opened.oneTime opt wOpk =
      StoresGhost.opened.oneTime := by
  cases opt <;> rfl

theorem p2Over_cliPollSelf_kpEvs_placed [LibsignalPlacement] {A : RustAlloc} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKitPlaced A F peer σ).KpErr IdentityKeyPair) :
    (cliPollSelfKitPlaced A F peer σ).kpEvs ans = [] := rfl

theorem p2Over_cliPollSelf_regIdEvs_placed [LibsignalPlacement] {A : RustAlloc} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKitPlaced A F peer σ).RegIdErr (BitVec 32)) :
    (cliPollSelfKitPlaced A F peer σ).regIdEvs ans = [] := rfl

/-- Memory-invariant-parameterized (`Φ : Memory → Prop`) Placed Stage P2 Path C (`Over`) CPS
contract statement at `dpPollEntryPlaced + 0x0868#64` under `[LibsignalPlacement]`, parameterized
over `Over.PromoteMatchingMissGenPlacedProp` and `Over.PromoteOverGenPlacedProp`. -/
def StageP2PathCOverQpanCliMemInvPlacedStmt (Φ : Memory → Prop) [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (g1 : StoresGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    Over.PromoteMatchingMissGenPlacedProp E2E.HooksE.A0
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    Over.PromoteOverGenPlacedProp E2E.HooksE.A0
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → Slots.scopeIn r') →
    Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
    r.currentSession = some sess →
    Slots.scopeIn r →
    ¬ DecPkS0.SessMatchesPm sess y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 →
    Φ s1.mem →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    dpClosSubStack B ≤ sp.toNat →
    s1.pc = dpPollEntryPlaced + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qpan sf Pf) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2PathCOverErrPlaced X W B S y s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (G_bob : SessionGhost)
      (prevCap' prevPtr' : BitVec 64)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      prevCap' ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel G_bob
        (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = dpPollEntryPlaced + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      Φ s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         genP3PrePlaced E2E.HooksE.A0 s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
           whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           G_bob (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         p2StageP3Sub5ExtraPrePrev1 E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
           (E2E.Record.encSession (OverP2.clearPending sess)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt E2E.HooksE.A0 y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut (some r) ∗
       preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
       protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt E2E.HooksE.A0 y.g.stores g1 ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

/-- Placed Stage P2 Path C (`Over`) CPS contract statement at `dpPollEntryPlaced + 0x0868#64`
under `[LibsignalPlacement]`. -/
abbrev StageP2PathCOverQpanCliPlacedStmt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  StageP2PathCOverQpanCliMemInvPlacedStmt (StoreKit.LibsignalCodeRoLoaded lsmpl) mmpl gh W

/-- `LibsignalFrozen`-guarded Stage P2 Path C (`Over`) CPS contract statement at
`dpPollEntryPlaced + 0x0868#64`. -/
abbrev StageP2PathCOverQpanCliFrozenPlacedStmt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  StageP2PathCOverQpanCliMemInvPlacedStmt (LibsignalFrozen lsmpl) mmpl gh W

/-- Memory-invariant-parameterized continuation/postcondition telescope of
`Over.stageP2_over_v1_kits_memInv_ext_placed` on `dpPollProgPlaced ext` (`b := 0#64`). -/
abbrev stageP2OverV1KitsMemInvAtPlacedProp (Φ : Memory → Prop) (P : Primitives) (A : RustAlloc)
    (F : ShaCompress) [LibsignalPlacement] (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64) (stk : Nat) : Prop :=
  ∀ (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (_hpan : ∀ sf Pf, ResponderClosure.PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (_hPromMiss : Over.PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess 4#8
      (5#8 :: bytesToBv8 hdr.ekAPk))
    (_hPromoteOver : Over.PromoteOverAtPlacedProp A ext coroPtr g recG sess)
    (_hctBuf_nz : ctBufPtr ≠ 0#64)
    (_hpqr_ne : sp - 576#64 ≠ 0#64) (_hstk_lt : stk ≤ sp.toNat)
    (_hikBSk_len : ikBSk.length = 32) (hikBPk_len : ikBPk.length = 32)
    (hikAPk_len : hdr.ikAPk.length = 32) (_hekAPk_len : hdr.ekAPk.length = 32)
    (_hkemCt_len : hdr.kemCt.length = 1568)
    (_hCode : Φ s.mem)
    (_hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (dpPollProgPlaced ext) s)
    (_hid_spk : spkKit.idOk signedPreKeyId)
    (_hspk_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) →
      spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
        spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (_hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (_hkpk_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (_hopk_word : ∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → opkIdWord = id)
    (_hid_pk : ∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → pkKit.getIdOk id)
    (_hpk_wf : ∀ (id : BitVec 32) (r : PreKeyRecord), hdrOpkIdBv? hdr = some id →
      pkKit.getRel stPk id (.ok r) → pkKit.RecOk r →
      ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
        opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
        r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes)
    (_hkp_sk : ∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.privateKey.bytes.toList = bytesToBv8 ikBSk)
    (_hkp_pk : ∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk)
    (_hneq : bytesToBv8 ikBPk ≠ bytesToBv8 hdr.ikAPk ∨
      DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes)
    (_hpc : s.pc = dpPollEntryPlaced + 0x868#64)
    (_hrun : s.status = .Running) (_hsp_eq : s.sp = sp)
    (_hsp_align : (sp &&& 15#64 == 0#64) = true)
    (_htr : s0.trace <+: s.trace) (_hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (_hx8 : s.readReg64 .x8 = kyberStorePtr) (_hx9 : s.readReg64 .x9 = msgPtr)
    (_hx10 : s.readReg64 .x10 = kpkKit.kpk_vt) (_hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (_hx12 : s.readReg64 .x12 = remoteAddrPtr) (_hx13 : s.readReg64 .x13 = pkKit.pk_vt)
    (_hx14 : s.readReg64 .x14 = localAddrPtr) (_hx15 : s.readReg64 .x15 = idStorePtr)
    (_hx16 : s.readReg64 .x16 = ikit.id_vt) (_hx19 : s.readReg64 .x19 = coroPtr)
    (_hx22 : s.readReg64 .x22 = spkStorePtr) (_hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (_hx24 : s.readReg64 .x24 = spkKit.spk_vt) (_hx29 : s.readReg64 .x29 = fp)
    (_hErrSpk : ∀ (e : spkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt spkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
        kpkKit.storeAt kyberStorePtr stKpk ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (_hErrKpk : ∀ (spkRec : SignedPreKeyRecord) (e : kpkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt kpkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (_hErrPk : ∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
        (opkId : BitVec 32) (e : pkKit.GetErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      hdrOpkIdBv? hdr = some opkId → pkKit.getRel stPk opkId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ pkKit.getEvs opkId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt pkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (_hErrKp : ∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (e : skit.KpErr) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      skit.kpRel stId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt skit.kpErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (_hErrBob : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (errTag w2 w3 w4 w5 w6 : BitVec 64)
        (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      Model.acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = none →
      errTag ≠ 0xfffffffffffffffe#64 → errTag ≠ 0xfffffffffffffffd#64 →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
        Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (_hErrRegId : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (drKey : DRKey) (e : skit.RegIdErr)
        (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      Model.acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey →
      skit.regIdRel stId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) ++ skit.regIdEvs (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt skit.regIdErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A s0 sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f)
    (_hOk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (drKey : DRKey) (localRegId : BitVec 32)
        (G_bob : SessionGhost) (sf : State),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      (hspkPub_len : spkPubBytes.length = 32) → (hspkPriv_len : spkPrivBytes.length = 32) →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      Model.acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey →
      skit.regIdRel stId (.ok localRegId) →
      G_bob.pending = none → G_bob.kyber = none →
      G_bob.alice.bytes = bytesToBv8 (Model.encodeEC hdr.ekAPk) →
      G_bob.regIds = unpack32 remoteRegId ++ unpack32 localRegId →
      Steps (dpPollProgPlaced ext) s sf →
      FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
        (stageP2Quiet spkKit kpkKit pkKit skit) (dpPollProgPlaced ext) sf →
      sf.pc = dpPollEntryPlaced + 0x1778#64 →
      sf.status = .Running → sf.sp = sp →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) ++ skit.regIdEvs (.ok localRegId) →
      sf.readReg64 .x8 = coroPtr + 0xe0#64 → sf.readReg64 .x9 = 8#64 →
      sf.readReg64 .x10 = msgVerByte.zeroExtend 64 → sf.readReg64 .x11 = coroPtr + 0xf8#64 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x20 = 0xfffffffffffffffe#64 →
      sf.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 →
      sf.readReg64 .x23 = (opkOptTag32 (hdrOpkIdBv? hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32) →
      sf.readReg64 .x24 = (opkOptTag32 (hdrOpkIdBv? hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32) →
      sf.readReg64 .x25 = sp + 0x210#64 → sf.readReg64 .x26 = v_330 →
      sf.readReg64 .x27 = sp + 0x370#64 → sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) sf
        (Over.p2OverOkPostAtPlaced A 0#64 spkKit kpkKit pkKit ikit s0
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
          recG sess G_bob
          (p2BobInitSessionV1 ikBPk (toU8 spkPubBytes)
            (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
              kyberPubBytes kyberPrivBytes opkSkBytes)
            drKey (initialStateValue F (p2BobSpqrParams drKey.pqrKey))
            hikBPk_len hikAPk_len
            (by simp [toU8, hspkPub_len])
            (by simp [mkP2AcceptKeysInput, toU8, clampBv8List_length hspkPriv_len]))
          hdr msgVerByte b_2c0 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk)
          stId gMe gPeer stk Frame)
        Q Qp),
    SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
      (Over.stageP2OverPreAtPlaced A 0#64 spkKit kpkKit pkKit ikit s0
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
        hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame)
      Q Qp

abbrev stageP2OverV1KitsAtPlacedProp (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    [LibsignalPlacement] (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64) (stk : Nat) : Prop :=
  stageP2OverV1KitsMemInvAtPlacedProp (StoreKit.LibsignalCodeRoLoaded lsmpl) P A F ext
    skit spkKit kpkKit pkKit stk

abbrev stageP2OverV1KitsFrozenAtPlacedProp (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    [LibsignalPlacement] (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64) (stk : Nat) : Prop :=
  stageP2OverV1KitsMemInvAtPlacedProp (LibsignalFrozen lsmpl) P A F ext
    skit spkKit kpkKit pkKit stk

/-- Relocatable `[LibsignalPlacement]` counterpart of `Over.stageP2_over_v1_kits_ext`. -/
def StageP2OverV1KitsPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State)),
    StructuralPrims P →
    RunHooksPlaced A ext →
    ∀ (ikit : IdentityStoreSpec A 0#64) (skit : IdentitySelfStoreSpec ikit),
      (lsmpl.base 547 ≠ 0#64 → IdentitySelfVtablesPlacedOk ikit skit) →
      ∀ (spkKit : SignedPreKeyStoreSpec A 0#64),
        (lsmpl.base 547 ≠ 0#64 → SignedPreKeyVtablesPlacedOk spkKit) →
      ∀ (kpkKit : KyberPreKeyStoreSpec A 0#64),
        (lsmpl.base 547 ≠ 0#64 → KyberPreKeyVtablesPlacedOk kpkKit) →
      ∀ (pkKit : PreKeyStoreSpec A 0#64),
        (lsmpl.base 547 ≠ 0#64 → PreKeyVtablesPlacedOk pkKit) →
      ∀ (stk : Nat), Over.stageP2OverV1CallStack spkKit kpkKit pkKit skit ≤ stk →
      stageP2OverV1KitsAtPlacedProp P A F ext skit spkKit kpkKit pkKit stk

set_option maxHeartbeats 1600000 in
private theorem stageP2PathCOver_qpan_cli_memInv_placed_of_at [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hAt : ∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
      (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      stageP2OverV1KitsMemInvAtPlacedProp Φ
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0 W.C.F
        (cliGhostExterns gh (cliExternsPlaced mmpl W))
        (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkWord (cliKitStk B))
        (dpClosSubStack B)) :
    StageP2PathCOverQpanCliMemInvPlacedStmt Φ mmpl gh W := by
  intro X B S Scope y g1 r sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hPromMiss hPromOver hh hread hcoins hdec0 hScope hFok hcur hIn hnotMatch _htrust hg1
    hfs1 hCode1 htr01 hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 hpan herr hok
  subst hg1
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, i, _, hi, hpm, hpkToE⟩ := pathA_pm_typed hdec0
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (OverP2Inst.stageP2_entry_unpack_pathCOver_placed y r sess m i s0 sp (sp + 0xc70#64)
      rngPtr v_a8 v_b8 v_d0 hcur hpm rfl hdec0 hFok hScope) ?_
  refine SepWPp.exists_elim fun g => ?_
  refine SepWPp.exists_elim fun recG => ?_
  refine SepWPp.exists_elim fun w => ?_
  refine SepWPp.pure_left fun ⟨_hkit, _hgcur, hcanon, hctBuf_nz, hopkWord⟩ => ?_
  have hPromMissAt : Over.PromoteMatchingMissAtPlacedProp E2E.HooksE.A0
      (cliGhostExterns gh (cliExternsPlaced mmpl W))
      y.fut g recG sess 4#8 (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk) :=
    Over.promoteMatchingMissAt_placed_of_gen hPromMiss y.fut g recG sess 4#8
      (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk)
      (OverP2Inst.p2Over_not_sessMatchesMsg sess y.g.msg m i hpm hnotMatch)
      (OverP2Inst.p2Over_serBytes_len m)
  have hPromOverAt : Over.PromoteOverAtPlacedProp E2E.HooksE.A0
      (cliGhostExterns gh (cliExternsPlaced mmpl W))
      y.fut g recG sess :=
    Over.promoteOverAt_placed_of_gen hPromOver y.fut g recG sess
      (OverP2Inst.encSessionMem_clearPending_lt_32 hIn hcur hcanon)
  let ikBSk : SignalPqxdh.Bytes :=
    match StoresGhost.opened.identity.keyPair cliIo.rd y.g.F with
    | .ok kp₀ => E2E.vecU8 kp₀.privateKey.bytes
    | .error _ => List.replicate 32 0
  let ikBPk : SignalPqxdh.Bytes :=
    match StoresGhost.opened.identity.keyPair cliIo.rd y.g.F with
    | .ok kp₀ => E2E.vecU8 kp₀.identityKey.publicKey.bytes
    | .error _ => List.replicate 32 0
  have hikBSk_len : ikBSk.length = 32 := by
    dsimp only [ikBSk]
    split
    · exact vecU8_length _
    · simp
  have hikBPk_len : ikBPk.length = 32 := by
    dsimp only [ikBPk]
    split
    · exact vecU8_length _
    · simp
  have hkp_sk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) →
      kp.privateKey.bytes.toList = bytesToBv8 ikBSk := by
    intro kp hrel
    have hkpEq := cliPollSelf_kpRel_ok_placed hrel
    dsimp only [ikBSk]; rw [hkpEq, bytesToBv8_vecU8]
  have hkp_pk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) →
      kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk := by
    intro kp hrel
    have hkpEq := cliPollSelf_kpRel_ok_placed hrel
    dsimp only [ikBPk]; rw [hkpEq, bytesToBv8_vecU8]
  let err0 : ApiError AddrVal Unit := .protocol .invalidKeyAgreement
  have herr0_p : err0 ≠ .panic := by nofun
  have herr0_s : err0 ≠ .store () := by nofun
  exact hAt X B y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey hh hread
    s0 s1 (OverP2Inst.pathAInnerFramePlaced y m i rngPtr sp)
    (fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Q sf Pf)
    (Qp := fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Qpan sf Pf)
    (fun sf Pf hp _ => by
      have hp' := poll_panicOomProp_of_matched emp hp
      rw [sepConj_emp] at hp'
      exact hpan sf Pf hp')
    sp (sp + 0xc70#64) y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
    y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
    y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
    (mkPathAHdr m) ikBSk ikBPk i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
    w.opkWord m.kpkId m.regId m.spkId
    StoresGhost.opened.signed StoresGhost.opened.kyber
    StoresGhost.opened.oneTime StoresGhost.opened.identity
    y.g.me y.g.peer g recG sess
    hPromMissAt hPromOverAt
    hctBuf_nz (sp_sub_576_ne_zero B hsub) hsub
    hikBSk_len hikBPk_len
    (vecU8_length m.idPub) (vecU8_length m.baseKey) (vecU8_length m.kyberCt)
    hCode1
    (cliPollStageP2_fsAt_placed hh y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B hfs1)
    rfl
    (fun r' hrel _ => cliPollSpk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    rfl
    (fun r' hrel _ => cliPollKpk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid))
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid) |>.symm)
    (fun _id r' _ hrel _ => cliPollPk_wf_of_preKeysWf_placed hdec0.preKeysWf r' hrel)
    hkp_sk hkp_pk
    (Or.inr (distinctSid_of_decPkOk₀ hdec0))
    hpc1 hrun1 hsp1 hsp_align htr01 hvregs1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hfp_reg
    -- SPK lookup error
    (fun e sf Pf hspkErr hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, List.append_nil] at htr_f
      have hspkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_spk_err
          ((cliSpk_getRel_error_iff (A := E2E.HooksE.A0) (b := 0#64) cliIo.rd y.g.F cliWrOk m.spkId
            (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll
            StoresGhost.opened.signed m.spkId).mp ⟨e, hspkErr⟩)
      have hrej : StageP2PathCOverModelRejPlaced X W y :=
        ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hspkNone)⟩
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap E2E.HooksE.A0 0#64
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hrej, hpost⟩)
    -- KPK lookup error
    (fun _spkRec e sf Pf _ _ hkpkErr hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_kpk_err
          ((cliKpk_getRel_error_iff (A := E2E.HooksE.A0) cliIo.rd y.g.F cliWrOk m.kpkId
            StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hrej : StageP2PathCOverModelRejPlaced X W y :=
        ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hkpkNone)⟩
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap E2E.HooksE.A0 0#64
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hrej, hpost⟩)
    -- OPK lookup error
    (fun _spkRec _kpkRec opkId e sf Pf _ _ _ _ hopkHdr hpkErr hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_getEvs_placed, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hmOpk : m.opkId = some opkId := (hdrOpkIdBv?_mkPathAHdr m).symm.trans hopkHdr
      have hpkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_opk_err hmOpk
          ((cliPk_getRel_error_iff (A := E2E.HooksE.A0) (b := 0#64) cliIo.rd y.g.F cliWrOk w.opkWord
            (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
            (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll
            StoresGhost.opened.oneTime opkId).mp ⟨e, hpkErr⟩)
      have hrej : StageP2PathCOverModelRejPlaced X W y :=
        ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hpkNone)⟩
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap E2E.HooksE.A0 0#64
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hrej, hpost⟩)
    -- Identity keypair lookup error
    (fun _spkRec _kpkRec wOpk e sf Pf _ _ _ _ _ hkpErr hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_opkOkEvs_placed, p2Over_cliPollSelf_kpEvs_placed,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate_placed E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpNone := cliPollSelf_kpRel_err_placed hkpErr
      have hrej : StageP2PathCOverModelRejPlaced X W y :=
        ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inr (Or.inl hkpNone))⟩
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (entails_decResAt_anyHeap_of_err y.out err0
          (cliPollSelf_kpErr_entails_decResAt_err E2E.HooksE.A0 0#64
            y.g.F y.g.peer (cliKitStk B) y.out e err0)))
        (p2ErrFrame_fold_pathA_placed y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hrej, hpost⟩)
    -- PQXDH acceptKeys rejection
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec _kyberPubBytes _kyberPrivBytes
        wOpk _opkPkBytes _opkSkBytes kp errTag w2 w3 w4 w5 w6 sf Pf
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccNone _ _
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_opkOkEvs_placed, p2Over_cliPollSelf_kpEvs_placed,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate_placed E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = E2E.vecU8 kp.privateKey.bytes := by
        dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes := by
        dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have haccNone0 : ∀ reg : BitVec 32,
          SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
            (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none := by
        intro reg
        have hmap :
            (SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
              (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m)).map
                ofSignalPqxdhDRKey = none := by
          rw [← Model.acceptKeys_ofSignalPqxdhPrimitives, ← hinp reg]
          exact haccNone
        exact Option.map_eq_none_iff.mp hmap
      have hrej : StageP2PathCOverModelRejPlaced X W y :=
        ⟨m, i, hpkToE, hi, hpm, Or.inr ⟨k, kp, hk, hkpOk, haccNone0⟩⟩
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap y.out errTag w2 w3 w4 w5 w6 err0))
        (p2ErrFrame_fold_pathA_placed y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hrej, hpost⟩)
    -- Local registration-ID lookup error
    (fun _spkRec _spkPubBytes _spkPrivBytes _kpkRec _kyberPubBytes _kyberPrivBytes
        wOpk _opkPkBytes _opkSkBytes _kp _drKey e sf Pf
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hregErr
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_opkOkEvs_placed, p2Over_cliPollSelf_kpEvs_placed,
          p2Over_cliPollSelf_regIdEvs_placed,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate_placed E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hregNone := cliPollSelf_regIdRel_err_placed hregErr
      have hrej : StageP2PathCOverModelRejPlaced X W y :=
        ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inr (Or.inr hregNone))⟩
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (entails_decResAt_anyHeap_of_err y.out err0
          (cliPollSelf_regIdErr_entails_decResAt_err E2E.HooksE.A0 0#64
            y.g.F y.g.peer (cliKitStk B) y.out e err0)))
        (p2ErrFrame_fold_pathA_placed y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hrej, hpost⟩)
    -- Success case: `+0x1778` fresh Bob V1 session with archived `sess` in `previous_sessions`
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey localRegId G_bob s2
        hspkRel _ hspkPub_len hspkPriv_len hspkPubEq hspkPrivEq
        hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hregRel
        hG_pend hG_kyb hG_alice hG_regs
        hSteps12 _ hpc2 hrun2 hsp2 htr2
        _ _ _ _ hx19_2 _ _ _ _ _ _ hx27_2 _ hx29_2
        hvregs2 _hCode2 => by
      rw [p2Over_cliPollSpk_getEvs_placed, p2Over_cliPollKpk_getEvs_placed,
          p2Over_cliPollPk_opkOkEvs_placed, p2Over_cliPollSelf_kpEvs_placed,
          p2Over_cliPollSelf_regIdEvs_placed,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr2
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate_placed E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hregOk := cliPollSelf_regIdRel_ok_placed hregRel
      have hikBSk_ok : ikBSk = E2E.vecU8 kp.privateKey.bytes := by
        dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes := by
        dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, hspkPub_eq, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0
        hspkRel hspkPubEq hspkPrivEq hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes
        hkpOk hikBSk_ok hikBPk_ok
      have hmapSome :
          (SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
            (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m)).map
              ofSignalPqxdhDRKey = some drKey := by
        rw [← Model.acceptKeys_ofSignalPqxdhPrimitives, ← hinp localRegId]
        exact haccSome
      obtain ⟨dk0, haccModel, hdk0⟩ := Option.map_eq_some_iff.mp hmapSome
      have hikBPk_bv :
          bytesToBv8 ikBPk = (keyPairOf W.C kp.privateKey.bytes).publicKey.bytes.toList := by
        rw [hikBPk_ok, hdec0.idPairDerived kp hkpOk, bytesToBv8_vecU8]
      have hst_eq := p2BobInitSessionV1_eq_pathAInitState (cliModelPrims_structural X W)
        W kp localRegId k m drKey dk0 ikBPk spkPubBytes
        (mkP2AcceptKeysInput (mkPathAHdr m) ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes)
        hikBPk_len (vecU8_length m.idPub)
        (by simp [toU8, hspkPub_len])
        (by simp [mkP2AcceptKeysInput, toU8, clampBv8List_length hspkPriv_len])
        haccSome hdk0 (hinp localRegId) hikBPk_bv hspkPub_eq
      have hextra := sessionExtraRel_pathAInitSession W kp localRegId k m dk0 G_bob
        hG_pend hG_kyb hG_alice hG_regs
      have hmsg_reasm :
          signalMessageAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA y.g.msg.message ∗
          ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ⊢
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg := by
        rw [preKeyMsgAt_eq_base_idKey_sep]
        exact Entails.of_eq (by ac_rfl)
      have halign2 : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
      have hx29_sp0 : s2.readReg64 .x29 = s0.sp - 0x60#64 := x29_eq_sp0_sub_60 hsp0 hx29_2
      rw [hst_eq, hopkUpd]
      refine sepWPp_drop_steps hSteps12 ?_
      refine sepWPp_conseq_pre
        (OverP2Inst.p2OverOkPost_fold_pathCOver_placed y m i w s0 s2 sp (sp + 0xc70#64) rngPtr
          recG G_bob sess (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m dk0)
          hcanon hpm hcoins hsub rfl hopkWord hsp2 hx19_2 hx27_2) ?_
      refine SepWPp.exists_elim fun prevCap' => ?_
      refine SepWPp.exists_elim fun prevPtr' => ?_
      refine SepWPp.pure_left fun hcap_ne => ?_
      exact hok s2 m i k kp localRegId dk0 G_bob prevCap' prevPtr' y.g.msgA y.g.msgG.msg
        (preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
        hcap_ne hpm hi hk hkpOk hregOk haccModel hextra hmsg_reasm
        hSteps12 htr2 hpc2 hrun2 hsp2 halign2 hx19_2 hx27_2 hx29_sp0 hvregs2
        (hInv.of_keepsFrozen hCode1 hSteps12.keepsFrozen))

private theorem stageP2PathCOver_qpan_cli_placed_of_at [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hAt : ∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
      (F0 : FsFiles) (peer : AddrGhost)
      (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      stageP2OverV1KitsAtPlacedProp
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0 W.C.F
        (cliGhostExterns gh (cliExternsPlaced mmpl W))
        (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkWord (cliKitStk B))
        (dpClosSubStack B)) :
    StageP2PathCOverQpanCliPlacedStmt mmpl gh W :=
  stageP2PathCOver_qpan_cli_memInv_placed_of_at StageP2MemInv.codeRoLoaded mmpl gh W hAt

/-- Path C Over Stage P2 V1 Instantiation (`StageP2PathCOverQpanCliPlacedStmt`) from
`StageP2OverV1KitsPlacedStmt`. -/
theorem stageP2PathCOver_qpan_cli_placed_of_kits [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hKits : StageP2OverV1KitsPlacedStmt) :
    StageP2PathCOverQpanCliPlacedStmt mmpl gh W :=
  stageP2PathCOver_qpan_cli_placed_of_at mmpl gh W
    fun X B F0 peer spkId kpkId opkWord kbk hh _hread =>
    hKits
      (P := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) (A := E2E.HooksE.A0) (F := W.C.F)
      (cliGhostExterns gh (cliExternsPlaced mmpl W))
      (cliModelPrims_structural X W)
      hh
      (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      (cliPollSelf_vtablesPlacedOk F0 peer (cliKitStk B))
      (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
      (cliPollSpk_vtablesPlacedOk F0 spkId (cliKitStk B))
      (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
      (cliPollKpk_vtablesPlacedOk F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkWord (cliKitStk B))
      (cliPollPk_vtablesPlacedOk F0 opkWord (cliKitStk B))
      (dpClosSubStack B)
      (OverP2Inst.stageP2OverV1CallStack_le_subStack_placed (A := E2E.HooksE.A0) F0 peer
        spkId kpkId opkWord kbk B)

/-! ## 3. Placed `PromoteMatchingMissGenPlacedProp` & `PromoteOverGenPlacedProp` Helpers -/

private theorem subroutine_ok_withLsCl_of_spec_map [LibsignalPlacement] {α β : Type}
    {prog : Program} {entry : BitVec 64} {specA : Spec α} {specB : Spec β}
    (f : β → α)
    (hpre : ∀ x s, specB.pre x s = specA.pre (f x) s)
    (hpost : ∀ x s0 sf, specA.post (f x) s0 sf = specB.post x s0 sf)
    (hpan : ∀ x s0 sf, specA.onPanic (f x) s0 sf = specB.onPanic x s0 sf)
    (hexit : ∀ x code s0 sf, specA.onExit (f x) code s0 sf = specB.onExit x code s0 sf)
    (hoom : ∀ x s0 sf, specA.onOom (f x) s0 sf = specB.onOom x s0 sf)
    (hok : subroutine_ok prog entry (withLsCl lsmpl specA)) :
    subroutine_ok prog entry (withLsCl lsmpl specB) := by
  intro x R s0 hpc hrun hp halign hL
  have hp' : s0.mem ⊨ (withLsCl lsmpl specA).pre (f x) s0 ∗ R := by
    dsimp only [withLsCl] at hp ⊢
    rwa [← hpre x s0]
  rcases hok (f x) R s0 hpc hrun hp' halign hL with
    ⟨sf, hsteps, ⟨hret, hcs, hq⟩ | hpa | hex | hoo⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcs, ?_⟩⟩
    dsimp only [withLsCl] at hq ⊢
    rwa [← hpost x s0 sf]
  · refine ⟨sf, hsteps, Or.inr (Or.inl ?_)⟩
    dsimp only [withLsCl] at hpa ⊢; rwa [← hpan x s0 sf]
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ?_))⟩
    rcases hex with ⟨code, he1, he2⟩
    refine ⟨code, he1, ?_⟩
    dsimp only [withLsCl] at he2 ⊢; rwa [← hexit x code s0 sf]
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ?_))⟩
    dsimp only [withLsCl] at hoo ⊢; rwa [← hoom x s0 sf]

/-- Relocatable `PromoteMatchingMissGenPlacedProp` (`lsmpl.base 50`) from `h_bb` on `ext`. -/
theorem promoteMatchingMissGen_placed_of_blackBox [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_bb : ext lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook) :
    Over.PromoteMatchingMissGenPlacedProp A ext := by
  have h50' : subroutine_ok (lsProg_518 ext) (lsmpl.base 50)
      (withLsCl lsmpl (Over.promoteMatchingSessionMissSpec A)) :=
    ls_subroutine_ok_cl_of_callee (callerProg := lsProg_518 ext)
      (Over.promote_matching_session_miss_placed_ok h_bb)
  exact subroutine_ok_withLsCl_of_spec_map
    (fun x : Over.P2PromoteMissGhost =>
      (⟨x.recPtr, x.msgVer, x.serPtr, x.serBytes, x.outPtr, x.g, x.r, x.s⟩ :
        Over.PromoteMissGhost))
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h50'

/-- Relocatable `PromoteMatchingMissGenPlacedProp` (`lsmpl.base 50`) at
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliPromoteMatchingMissGen_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    Over.PromoteMatchingMissGenPlacedProp E2E.HooksE.A0
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  promoteMatchingMissGen_placed_of_blackBox
    (IdKit.cliGhostExterns_blackBox mmpl gh W)

/-- Relocatable `PromoteOverGenPlacedProp` (`lsmpl.base 47`) from `SerContractsXPlaced` and
a Block `51`→`621` `grow_one` contract. -/
theorem promoteOverGen_placed_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Proofs.libsignal.Hooks2.SerContractsXPlaced A ext)
    (hGrow : subroutine_ok (lsProg_51 ext) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A))) :
    Over.PromoteOverGenPlacedProp A ext :=
  subroutine_ok_withLsCl_of_spec_map
    (fun x : Over.P2PromoteOverGenGhost =>
      (⟨x.recPtr, x.src, x.prevCap, x.prevPtr, x.G, x.sess, x.newBs⟩ :
        Over.PromoteOverGenGhost))
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (Over.promote_state_over_gen_placed_cl_of_contracts
      (callerProg := lsProg_518 ext) (callerBlk := 518) hC hGrow)

private theorem noAllocShimSpec_eq_sessionShimSpec_over :
    CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec =
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec := rfl

private theorem hookSat_sessionMemcpyRegion_of_codec {H : LibsignalHooks}
    (h : HookSat H lsMemcpySym framelessMemcpySpec) :
    HookSat H lsMemcpySym sessionMemcpyRegionSpec :=
  ProofLib.HookSat.mono h fun x R _ hpre => ⟨x, R, hpre, fun _ hpost => hpost⟩

private theorem hookSat_sessionMemcpy_of_codec {H : LibsignalHooks} (stk : Nat)
    (h : HookSat H lsMemcpySym framelessMemcpySpec) :
    HookSat H lsMemcpySym (sessionMemcpySpec stk) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp stk ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpySpec, libcMemcpySpec, framelessMemcpySpec] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · dsimp only [sessionMemcpySpec, framelessMemcpySpec] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

/-- Relocatable `PromoteOverGenPlacedProp` (`lsmpl.base 47`) at
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliPromoteOverGen_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    Over.PromoteOverGenPlacedProp E2E.HooksE.A0
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  promoteOverGen_placed_of_contracts
    (Proofs.libsignal.Hooks2.SerContractsXPlaced.of_hooks
      hh.codecHooks.alloc
      hh.codecHooks.dealloc
      hh.codecHooks.realloc
      (noAllocShimSpec_eq_sessionShimSpec_over ▸ hh.codecHooks.shim)
      (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_sessionMemmove_sat mmpl W _))
      (hookSat_sessionMemcpy_of_codec _ hh.codecHooks.memcpy)
      (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
      (Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W))
    (CryptoVerification.SpqrV1.Alloc.growOneVecU8_caller_withLsCl_ok
      (callerProg := lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 51)
      (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
      hh.codecHooks.shim
      hh.codecHooks.alloc
      hh.codecHooks.realloc)

/-! ## 4. Placed Stage P2 Over-Path Seam & Store-Kit Instantiation -/

private theorem cliStageP2ClosureHooksPlaced_over [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2ClosureHooksPlaced E2E.HooksE.A0
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  StageP2ClosureHooksPlaced.of_hooks
    hh.codecHooks.shim
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_sessionMemcpy_of_codec allocHookStack hh.codecHooks.memcpy)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)

private theorem cliUuidTryParse_placed_ok_over [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok
      ((blkPC_252).rebase (blkPl_252).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)) := by
  refine subroutine_ok_map_panic
    (UuidFs.uuidTryParse_placed_okFs_F (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (fun x R s0 hpre => ⟨x, R, ?_, fun sf hpost => ?_, fun _ hpan => ?_⟩)
    (fun _ _ _ _ _ _ he => False.elim (by
      rw [show (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse).keepsFs).onExit _ _ _ _ =
        ⌜False⌝ from rfl, satisfies_pure_sepConj] at he; exact he.1))
    (fun _ _ _ _ _ _ _ ho => False.elim (by
      rw [show (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse).keepsFs).onOom _ _ _ =
        ⌜False⌝ from rfl, satisfies_pure_sepConj] at ho; exact ho.1))
  · dsimp only [withLsCodeLoaded, Spec.keepsFs] at hpre ⊢
    exact hpre
  · dsimp only [withLsCodeLoaded, Spec.keepsFs] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · rw [show (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse).keepsFs).onPanic _ _ _ =
      ⌜False⌝ from rfl, satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1

private theorem cliStageP2PureCalleesPlaced4K_over_of_seams [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hS : SpqrV1PlacedSeams mmpl gh W)
    (h_accept : subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0)) :
    StageP2PureCalleesPlaced4K
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0 W.C.F
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  StageP2PureCalleesPlaced4K.of_hooks
    (cliModelPrims_structural X W)
    hh.codecHooks.shim
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_sessionMemcpyRegion_of_codec hh.codecHooks.memcpy)
    (hookSat_sessionMemcpy_of_codec allocHookStack hh.codecHooks.memcpy)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
    (Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W)
    (Kits.isSameAccount_4k_placed_ok_on_stageP1
      (IdKit.cliGhostExterns_blackBox mmpl gh W)
      (cliUuidTryParse_placed_ok_over mmpl gh W))
    h_accept
    hS.initialStateMemInv_lsProg75

private theorem cliInitBobErrOwned4K_placed_of_accept [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (h_accept_err : subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 79)
      (pqxdhAcceptErrOwnedPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0)) :
    subroutine_ok (stageP1ProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 75)
      (Sub5Placed.initializeBobSessionErrOwned4KPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0) :=
  Sub5Placed.of_responderCore_errOwned_to_4K_placed
    (Kits.initializeBobSession_err_owned_placed_ok_on_stageP1 h_accept_err)

/-- Statement of `Over.stageP2_over_v1_kits_ext_placed`,
parameterized over `StageP2ClosureHooksPlaced`, `StageP2PureCalleesPlaced4K`,
`Sub5Placed.initializeBobSessionErrOwned4KPlacedSpec`, the 4 placed store kits, and
`Over.stageP2OverV1CallStack4K`. -/
def StageP2OverV1KitsExtPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State)),
    StructuralPrims P →
    StageP2ClosureHooksPlaced A ext →
    StageP2PureCalleesPlaced4K P A F ext →
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (Sub5Placed.initializeBobSessionErrOwned4KPlacedSpec P A) →
    ∀ (ikit : IdentityStoreSpec A 0#64) (skit : IdentitySelfStoreSpec ikit),
      IdentitySelfVtablesPlacedOk ikit skit →
      IdentitySelfStoreKitPlacedOkI ikit skit ext →
    ∀ (spkKit : SignedPreKeyStoreSpec A 0#64),
      SignedPreKeyVtablesPlacedOk spkKit →
      SignedPreKeyStoreKitPlacedOk spkKit ext →
    ∀ (kpkKit : KyberPreKeyStoreSpec A 0#64),
      KyberPreKeyVtablesPlacedOk kpkKit →
      KyberPreKeyStoreKitPlacedOk kpkKit ext →
    ∀ (pkKit : PreKeyStoreSpec A 0#64),
      PreKeyVtablesPlacedOk pkKit →
      PreKeyStoreKitPlacedOk pkKit ext →
    ∀ (stk : Nat), Over.stageP2OverV1CallStack4K spkKit kpkKit pkKit skit ≤ stk →
    stageP2OverV1KitsAtPlacedProp P A F ext skit spkKit kpkKit pkKit stk

/-- Instantiates `StageP2OverV1KitsExtPlacedStmt` via `Over.stageP2_over_v1_kits_ext_placed`. -/
theorem stageP2OverV1Kits_ext_placed_inst [LibsignalPlacement] :
    StageP2OverV1KitsExtPlacedStmt :=
  fun {_ _ _} => Over.stageP2_over_v1_kits_ext_placed

private theorem stageP2OverV1CallStack4K_le_subStack_placed [LibsignalPlacement]
    {A : RustAlloc} (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    Over.stageP2OverV1CallStack4K
      (cliPollSpkKitPlaced A F0 spkId (cliKitStk B))
      (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKitPlaced A F0 opkWord (cliKitStk B))
      (cliPollSelfKitPlaced A F0 peer (cliKitStk B)) ≤ dpClosSubStack B := by
  rw [Over.stageP2OverV1CallStack4K_eq]
  exact OverP2Inst.stageP2OverV1CallStack_le_subStack_placed F0 peer spkId kpkId opkWord kbk B

/-- Path C Over Stage P2 V1 Instantiation (`StageP2PathCOverQpanCliPlacedStmt`) from
`(hDropNz : lsmpl.base 547 ≠ 0#64)`, `SpqrV1PlacedSeams`, the Block `79` `Pqxdh::accept` seams,
and the 4 placed CLI store-kit `subroutine_ok` bundles. -/
theorem stageP2PathCOver_qpan_cli_placed_of_seams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (h_accept : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (h_accept_err : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (hSelfKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      IdentitySelfStoreKitPlacedOkI
        (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (spkId : BitVec 32),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      SignedPreKeyStoreKitPlacedOk
        (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (B : RunBudgets) (F0 : FsFiles)
      (kpkId spkId : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      KyberPreKeyStoreKitPlacedOk
        (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (opkWord : BitVec 32),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      PreKeyStoreKitPlacedOk
        (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkWord (cliKitStk B))
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathCOverQpanCliPlacedStmt mmpl gh W :=
  stageP2PathCOver_qpan_cli_placed_of_at mmpl gh W
    fun X B F0 peer spkId kpkId opkWord kbk hh hread =>
    stageP2OverV1Kits_ext_placed_inst
      (P := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) (A := E2E.HooksE.A0) (F := W.C.F)
      (cliGhostExterns gh (cliExternsPlaced mmpl W))
      (cliModelPrims_structural X W)
      (cliStageP2ClosureHooksPlaced_over mmpl gh W hh)
      (cliStageP2PureCalleesPlaced4K_over_of_seams X mmpl gh W hh
        hSpqr (h_accept X))
      (cliInitBobErrOwned4K_placed_of_accept X mmpl gh W (h_accept_err X))
      (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      (cliPollSelf_vtablesPlacedOk F0 peer (cliKitStk B) hDropNz)
      (hSelfKit B F0 peer hh hread)
      (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
      (cliPollSpk_vtablesPlacedOk F0 spkId (cliKitStk B) hDropNz)
      (hSpkKit B F0 spkId hh hread)
      (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
      (cliPollKpk_vtablesPlacedOk F0 kpkId spkId kbk (cliKitStk B) hDropNz)
      (hKpkKit B F0 kpkId spkId kbk hh hread)
      (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkWord (cliKitStk B))
      (cliPollPk_vtablesPlacedOk F0 opkWord (cliKitStk B) hDropNz)
      (hPkKit B F0 opkWord hh hread)
      (dpClosSubStack B)
      (stageP2OverV1CallStack4K_le_subStack_placed (A := E2E.HooksE.A0) F0 peer
        spkId kpkId opkWord kbk B)

private theorem cliStageP2BaseCalleesPlaced4K_over [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2BaseCalleesPlaced4K E2E.HooksE.A0
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  StageP2BaseCalleesPlaced4K.of_hooks
    hh.codecHooks.shim
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_sessionMemcpy_of_codec allocHookStack hh.codecHooks.memcpy)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
    (Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W)
    (Kits.isSameAccount_4k_placed_ok_on_stageP1
      (IdKit.cliGhostExterns_blackBox mmpl gh W)
      (cliUuidTryParse_placed_ok_over mmpl gh W))

private theorem pqxdhAccept_opt_fields_exactSat_over [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {P : Initiator.Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : Initiator.StructuralPrims P)
    (hP : ResponderCore.PrimitivesMatchCrypto P C)
    (hH : LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat.PqxdhPlacedHookContractsExactSat
      P C A H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (ResponderCore.pqxdhAcceptOptFieldsFrozenPlacedSpec P A) :=
  ResponderCore.pqxdhAccept_opt_fields_placed_ok_of_block hWF
    (ResponderCore.ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    (CryptoVerification.E2E.Pqxdh.Shared.vecAppendElements_fast_placed_ok_cl h_memcpy)
    (hH.hkdfExtract_ok hP)
    (hH.hkdfExpandMultiInfo_ok hP)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy hH.kyberDecaps
    hH.handleError hH.handleAllocError

private theorem pqxdhAccept_err_owned_exactSat_over [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {P : Initiator.Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : Initiator.StructuralPrims P)
    (hP : ResponderCore.PrimitivesMatchCrypto P C)
    (hH : LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat.PqxdhPlacedHookContractsExactSat
      P C A H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (ResponderCore.pqxdhAcceptErrOwnedFrozenPlacedSpec P A) :=
  ResponderCore.pqxdhAccept_err_owned_placed_ok_of_block hWF
    (ResponderCore.ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy hH.handleError

private theorem initBobErrOwned_4k_exactSat_over [LibsignalFullPlacement]
    {P : Initiator.Primitives} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hWF : Initiator.StructuralPrims P)
    (hP : ResponderCore.PrimitivesMatchCrypto P C)
    (hH : LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat.PqxdhPlacedHookContractsExactSat
      P C A ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (Sub5Placed.initializeBobSessionErrOwnedFrozen4KPlacedSpec P A) :=
  Sub5Placed.of_responderCore_errOwned_to_4K_frozen_placed <| by
    have hbase :=
      ResponderCore.ls_subroutine_ok_withLsFrozen_of_block
        (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
        (ResponderCore.initializeBobSession_err_owned_frozen_placed_ok_of_accept
          (pqxdhAccept_err_owned_exactSat_over hWF hP hH h_memcpy))
    refine subroutine_ok_map_panic hbase ?_
      (fun _ _ _ _ _ _ he => by
        dsimp only [ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec,
          ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
          CryptoVerification.LibsignalTripleRatchet.withLsFrozen] at he
        exact not_satisfies_false_sepConj he)
      (fun _ _ _ _ _ _ _ ho => by
        dsimp only [ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec,
          ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
          CryptoVerification.LibsignalTripleRatchet.withLsFrozen] at ho
        exact (not_satisfies_false_sepConj ho).elim)
    intro g R s0 hpre
    refine ⟨g, R, ?_, fun _ hpost => hpost, fun _ hpan => hpan⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpre
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
    exact hpre.2

private theorem initBobOkV1_4k_exactSat_over [LibsignalFullPlacement]
    {P : Initiator.Primitives} {C : Crypto} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : Initiator.StructuralPrims P)
    (hP : ResponderCore.PrimitivesMatchCrypto P C)
    (hH : LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat.PqxdhPlacedHookContractsExactSat
      P C A ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hMemcpySess : HookSat ext lsMemcpySym sessionMemcpyRegionSpec)
    (hinit : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A F ext) :
    Kits.InitializeBobV1FrozenOkPlaced4K P A F ext :=
  Kits.InitializeBobV1MemInvOkPlaced.to_4K fun s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
      ratchetKeyPairPtr outPtr drKey Frame
      hfr hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc =>
    Kits.ls_sepWPp_of_block (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext)
      (i := 518) (j := 75) (LibsignalCodeLoaded.of_codeLoaded hfr.2)
      (CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_frozen_placed_of_accept
        hWF hH.noAllocShim hH.alloc hH.dealloc hMemcpySess hH.handleError
        (pqxdhAccept_opt_fields_exactSat_over hWF hP hH h_memcpy)
        (CryptoVerification.Cli.E2E.V1.initialStateMemInvPlacedOk_mono
          (fun _ h => ⟨LibsignalCodeLoaded.of_codeLoaded h.2, h.1⟩) hinit)
        s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
        hfr hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)
      (by decide) (by decide) (by decide)

/-- Closed `[LibsignalFullPlacement]` Path C Over Stage P2 V1 Instantiation
(`StageP2PathCOverQpanCliFrozenPlacedStmt`) discharging Block `79` (`Pqxdh::accept`) via
`withLsFrozen` with zero `h_accept` / `h_accept_err` seams. -/
theorem stageP2PathCOver_qpan_cli_full_placed_of_seams [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (hSelfKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      IdentitySelfStoreKitPlacedOkI
        (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (spkId : BitVec 32),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      SignedPreKeyStoreKitPlacedOk
        (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ (B : RunBudgets) (F0 : FsFiles)
      (kpkId spkId : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      KyberPreKeyStoreKitPlacedOk
        (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ (B : RunBudgets) (F0 : FsFiles) (opkWord : BitVec 32),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      PreKeyStoreKitPlacedOk
        (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkWord (cliKitStk B))
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathCOverQpanCliFrozenPlacedStmt mmpl gh W :=
  stageP2PathCOver_qpan_cli_memInv_placed_of_at StageP2MemInv.frozen mmpl gh W
    fun X B F0 peer spkId kpkId opkWord kbk hh hread =>
      Over.stageP2_over_v1_kits_frozen_ext_placed
        (P := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) (A := E2E.HooksE.A0) (F := W.C.F)
        (cliGhostExterns gh (cliExternsPlaced mmpl W))
        (cliModelPrims_structural X W)
        (cliStageP2ClosureHooksPlaced_over mmpl gh W hh)
        (cliStageP2BaseCalleesPlaced4K_over mmpl gh W hh)
        (initBobErrOwned_4k_exactSat_over
          (cliModelPrims_structural X W) (cliModelPrims_matchCrypto X W)
          (cliResponderPqxdhHookContractsPlaced X mmpl gh W hG hh)
          hh.codecHooks.memcpy)
        (initBobOkV1_4k_exactSat_over
          (cliModelPrims_structural X W) (cliModelPrims_matchCrypto X W)
          (cliResponderPqxdhHookContractsPlaced X mmpl gh W hG hh)
          hh.codecHooks.memcpy
          (hookSat_sessionMemcpyRegion_of_codec hh.codecHooks.memcpy)
          hSpqr.initialStateMemInv_lsProg75)
        (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollSelf_vtablesPlacedOk F0 peer (cliKitStk B) hDropNz)
        (hSelfKit B F0 peer hh hread)
        (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
        (cliPollSpk_vtablesPlacedOk F0 spkId (cliKitStk B) hDropNz)
        (hSpkKit B F0 spkId hh hread)
        (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
        (cliPollKpk_vtablesPlacedOk F0 kpkId spkId kbk (cliKitStk B) hDropNz)
        (hKpkKit B F0 kpkId spkId kbk hh hread)
        (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkWord (cliKitStk B))
        (cliPollPk_vtablesPlacedOk F0 opkWord (cliKitStk B) hDropNz)
        (hPkKit B F0 opkWord hh hread)
        (dpClosSubStack B)
        (stageP2OverV1CallStack4K_le_subStack_placed (A := E2E.HooksE.A0) F0 peer
          spkId kpkId opkWord kbk B)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
