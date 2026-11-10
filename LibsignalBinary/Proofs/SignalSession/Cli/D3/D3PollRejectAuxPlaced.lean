/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCallee
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromote
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.PreKeyGeneralAux
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.PreKeyKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KyberKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFolds
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1OkTrapPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub5Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SelfSpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch

/-!
# Shared Poll & Store Rejection Helpers (`pkToE? pm = none`)

Store well-formedness and message rejection predicates (`DecPkStoreOk`, `MsgCondPkToENone`,
`DecPkOkD3Untyped`), kit-invariant projections, `Slots.loadRec` bridges, Stage-P2 hook/callee
bundles on `cliGhostExterns`, and relocatable poll entry unpacking.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp decryptPrekeyClosureName
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
open CryptoVerification.SignalSession.Cli.KitInst hiding
  cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced cliKyberPreKeyStoreSpecPlaced
  cliPreKeyStoreSpecPlaced_quiet cliSignedPreKeyStoreSpecPlaced_quiet
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns cliGhostExterns_other)

/-! ## 1. Pure Store & Message Rejection Predicates and Kit Invariant Projections -/

/-- Message- and scope-independent store well-formedness predicate for `pkToE? pm = none`
rejections (dropping `typed` and `sessMatch` from `DecPkOk₀`). -/
structure DecPkStoreOk (W : PEParams) (F : FsFiles) : Prop where
  keyPairLt : ∀ bs,
    StoresGhost.opened.identity.own.get cliIo.rd F (Cli.utf8 "identity-key-pair") = .ok bs →
    bs.length < 2 ^ 32
  preKeysWf : PreKeyFilesWf W F
  baseKeysLt : ∀ i bs,
    StoresGhost.opened.kyber.lastResort.get cliIo.rd F (Cli.baseKeysName i) = .ok bs →
    bs.length < 2 ^ 32

/-- Message rejection condition: `pm` parses from some wire body via `Pksm.pksmParse`,
has `pkToE? pm = none`, has distinct peer/self service IDs, and matches no active session. -/
def MsgCondPkToENone (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop :=
  (∃ body : List (BitVec 8), Pksm.pksmParse body = some pm) ∧
  pkToE? pm = none ∧
  ¬ SameServiceId peer me ∧
  ∀ r s, Slots.loadRec Scope F peer = .ok (some r) →
    r.currentSession = some s → ¬ SessMatchesPm s pm

/-- Whenever `pkToE? pm = none` and no loaded active session matches `pm`, `decPkDef`
evaluates to `some none` (clean protocol rejection, `0` writes). -/
theorem decPkDef_eq_some_none_of_d3b3
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    (hpk : pkToE? pm = none)
    (hnoMatch : ∀ r s, Slots.loadRec Scope F peer = .ok (some r) →
      r.currentSession = some s → ¬ SessMatchesPm s pm) :
    decPkDef X W Scope F peer me pm coins = some none := by
  unfold decPkDef
  dsimp only
  cases hload : Slots.loadRec Scope F peer with
  | error _ => rfl
  | ok opt =>
    dsimp only
    cases StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey with
    | error _ => rfl
    | ok b =>
      cases b with
      | false => rfl
      | true =>
        dsimp only
        cases opt with
        | none =>
          dsimp only [Option.bind]
          rw [hpk]
        | some r =>
          dsimp only [Option.bind]
          cases hcur : r.currentSession with
          | none =>
            rw [hpk]
          | some s =>
            have hnm := hnoMatch r s hload hcur
            simp only [hnm, ↓reduceIte]

theorem toRecord_currentSession_eq_pqSessionOf (x : RecordExtras)
    (g : GhostState (List (BitVec 8))) :
    (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g).currentSession =
      some (pqSessionOf x g) :=
  rfl

/-- `decPkOk` predicate combining `DecPkStoreOk` and `MsgCondPkToENone`. -/
def DecPkOkD3Untyped (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop :=
  DecPkStoreOk W F ∧ MsgCondPkToENone Scope F peer me pm

theorem cliIdOwnInv_of_storeOk {W : PEParams} {F : FsFiles} (hd : DecPkStoreOk W F) :
    CliIdOwnInv cliIo.rd F cliWrOk StoresGhost.opened.identity.own where
  ownPathLt := show (0 : Nat) < 2 ^ 32 by decide
  kpPathOk := cliWrOk_ownFile (.tail _ (.head _))
  regPathOk := cliWrOk_ownFile (.tail _ (.tail _ (.head _)))
  kpSizeOk := hd.keyPairLt

theorem cliPkInv_of_storeOk {W : PEParams} {F : FsFiles}
    (hd : DecPkStoreOk W F) (pid : BitVec 32) :
    CliPkInv cliIo.rd F cliWrOk pid StoresGhost.opened.oneTime where
  nameOk := pkNameOk_opened_oneTime pid
  sizeOk := by
    intro bs hget
    rcases hd.preKeysWf.oneTime pid bs hget with rfl | ⟨sk, rfl⟩
    · decide
    · exact oneTimeRecordBytes_length_lt W.C pid sk
  oneLt := ⟨show (0 : Nat) < 2 ^ 32 by decide, Or.inl (show (0 : Nat) + 1 < 2 ^ 32 by decide)⟩

theorem cliSpkInv_of_storeOk {W : PEParams} {F : FsFiles}
    (hd : DecPkStoreOk W F) (sid : BitVec 32) :
    CliSpkInv cliIo.rd F cliWrOk sid StoresGhost.opened.signed where
  nameOk := pkNameOk_opened_signed sid
  sizeOk := by
    intro bs hget
    rcases hd.preKeysWf.signed sid bs hget with rfl | ⟨k, rfl⟩
    · decide
    · exact signedRecordBytes_length_lt W.C sid k

theorem cliKpkInvFull_of_storeOk {W : PEParams} {F : FsFiles}
    (hd : DecPkStoreOk W F) (kid ksid : BitVec 32) (kbk : PublicKey) :
    CliKpkInvFull cliIo.rd F cliWrOk kid ksid kbk StoresGhost.opened.kyber where
  markInv := {
    nameOk := pkNameOk_opened_kyberOneTime kid
    baseOk := kpkBaseKeysOk_opened kid
    seenOk := fun bs hget _ _ => hd.baseKeysLt kid bs hget
    oneLt := ⟨show (0 : Nat) < 2 ^ 32 by decide, Or.inl (show (0 : Nat) + 1 < 2 ^ 32 by decide)⟩
    lastLt := ⟨show (0 : Nat) < 2 ^ 32 by decide, Or.inl (show (0 : Nat) + 1 < 2 ^ 32 by decide)⟩
  }
  lastNameOk := pkNameOk_opened_kyberLastResort kid
  oneSizeOk := by
    intro bs hget
    rcases hd.preKeysWf.kyberOneTime kid bs hget with rfl | ⟨k, rfl⟩
    · decide
    · exact kyberRecordBytes_length_lt kid k
  lastSizeOk := by
    intro bs hget
    rcases hd.preKeysWf.kyberLastResort kid bs hget with rfl | ⟨k, rfl⟩
    · decide
    · exact kyberRecordBytes_length_lt kid k

/-- Bridges `cliPollSessKit.loadRel` to `Slots.loadRec Scope F peer.val`. -/
theorem loadRec_of_cliPollSess_loadRel
    {A : RustAlloc} {b : BitVec 64}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {σ : DpKitStk}
    {opt : Option (SessionRecord (List (BitVec 8)))}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hload_rel : (cliPollSessKit A b F Slots.scopeKit peer σ).loadRel
      StoresGhost.opened.sessions peer.val (.ok opt)) :
    Slots.loadRec Scope F peer.val = .ok opt := by
  have hloadK : (.ok opt) = Slots.loadRec Slots.scopeKit F peer.val :=
    Slots.cliSessLoadRel_eq_loadRec hinjK hload_rel
  exact (loadRec_scopeKit_eq hinjK hsub hf).symm.trans hloadK.symm

/-- Placed specialization (`b := 0#64`) bridging `cliPollSessKitPlaced.loadRel` to `Slots.loadRec`. -/
theorem loadRec_of_cliPollSessPlaced_loadRel [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {σ : DpKitStk}
    {opt : Option (SessionRecord (List (BitVec 8)))}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hload_rel : (cliPollSessKitPlaced E2E.HooksE.A0 F Slots.scopeKit peer σ).loadRel
      StoresGhost.opened.sessions peer.val (.ok opt)) :
    Slots.loadRec Scope F peer.val = .ok opt :=
  loadRec_of_cliPollSess_loadRel (A := E2E.HooksE.A0) (b := 0#64) (σ := σ) hinjK hsub hf hload_rel

/-! ## 2. Placed Stage P2 Hook & Callee Bundles on `cliGhostExterns g (cliExternsPlaced mmpl W)` -/

theorem stageP1ProgPlaced_eq_dpPollProgPlaced [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    stageP1ProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)) =
      Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  rfl

private theorem cliGhostExterns_blackBox_placed
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W) lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook :=
  (cliGhostExterns_other g (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (RunGlue.cliExternsPlaced_row mmpl W (Slots.blackBox_row_placed mmpl W))

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
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp halign => ?_
  have hp' : s0.mem ⊨ (withLsCl lsmpl specA).pre (f x) s0 ∗ R := by
    dsimp only [withLsCl] at hp ⊢
    rwa [← hpre x s0]
  refine hok.mono_outcome (f x) R s0 hpc hrun hp' halign ?_
  rintro sf (⟨hret, hcs, hq⟩ | ⟨hp1, hpa⟩ | ⟨code, he1, he2⟩ | ⟨ho1, hoo⟩)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [withLsCl] at hq ⊢
    rwa [← hpost x s0 sf]
  · refine Or.inr (Or.inl ⟨hp1, ?_⟩)
    dsimp only [withLsCl] at hpa ⊢; rwa [← hpan x s0 sf]
  · refine Or.inr (Or.inr (Or.inl ⟨code, he1, ?_⟩))
    dsimp only [withLsCl] at he2 ⊢; rwa [← hexit x code s0 sf]
  · refine Or.inr (Or.inr (Or.inr ⟨ho1, ?_⟩))
    dsimp only [withLsCl] at hoo ⊢; rwa [← hoom x s0 sf]

private theorem promoteMatchingMissGen_placed_of_blackBox [LibsignalPlacement] {A : RustAlloc}
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

theorem promoteMatchingMissGen_cli_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    Over.PromoteMatchingMissGenPlacedProp E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  promoteMatchingMissGen_placed_of_blackBox (cliGhostExterns_blackBox_placed mmpl g W)

theorem cliStageP2ClosureHooksPlaced_d3 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 g) :
    StageP2ClosureHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  StageP2ClosureHooksPlaced.of_hooks
    (Slots.cliExternsPlaced_noAllocShim_sat mmpl g W hG.shim_eq)
    (Slots.cliExternsPlaced_alloc_sat mmpl g W hG)
    (Slots.cliExternsPlaced_dealloc_sat mmpl g W hG)
    (Slots.cliExternsPlaced_sessionMemcpy_sat mmpl g W hG allocHookStack)
    (Slots.cliGhostExterns_panic_handle_error mmpl g W)

theorem cliUuidTryParse_placed_ok_d3 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    subroutine_ok
      ((blkPC_252).rebase (blkPl_252).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)) := by
  refine subroutine_ok_map_panic
    (UuidFs.uuidTryParse_placed_okFs_F (cliGhostExterns g (cliExternsPlaced mmpl W)))
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

theorem cliStageP2BaseCalleesPlaced4K_d3 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 g) :
    StageP2BaseCalleesPlaced4K E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  StageP2BaseCalleesPlaced4K.of_hooks
    (Slots.cliExternsPlaced_noAllocShim_sat mmpl g W hG.shim_eq)
    (Slots.cliExternsPlaced_alloc_sat mmpl g W hG)
    (Slots.cliExternsPlaced_dealloc_sat mmpl g W hG)
    (Slots.cliExternsPlaced_sessionMemcpy_sat mmpl g W hG allocHookStack)
    (Slots.cliGhostExterns_panic_handle_error mmpl g W)
    (Slots.cliGhostExterns_panic_handle_alloc_error mmpl g W)
    (Kits.isSameAccount_4k_placed_ok_on_stageP1
      (cliGhostExterns_blackBox_placed mmpl g W)
      (cliUuidTryParse_placed_ok_d3 mmpl g W))

theorem cliStrToOwnedLocal2_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 g) :
    subroutine_ok (stageP1ProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (Matched.strToOwnedLocal2Spec E2E.HooksE.A0)) := by
  let ext := cliGhostExterns g (cliExternsPlaced mmpl W)
  have hpan_eq : Rust.withPanics ext = ext := RunGlue.withPanics_cliGhostExterns mmpl g W
  have hprog_eq : stageP1ProgPlaced ext = lsProg_518 (Rust.withPanics ext) := by
    dsimp only [stageP1ProgPlaced]
    rw [hpan_eq]
  rw [hprog_eq]
  refine Matched.str_to_owned_local2_placed_ok_at
    (callerProg := lsProg_518 (Rust.withPanics ext)) (i := 518)
    (ext := ext) ?_ ?_ ?_ ?_ (by decide)
  · rw [hpan_eq]
    exact ls_hook_ok_ultra_of_mem
      (Slots.cliExternsPlaced_noAllocShim_sat mmpl g W hG.shim_eq) (by decide)
  · rw [hpan_eq]
    exact ls_hook_ok_ultra_of_mem
      (Slots.cliExternsPlaced_alloc_sat mmpl g W hG) (by decide)
  · rw [hpan_eq]
    exact ls_hook_ok_ultra_of_mem
      (Slots.cliExternsPlaced_memcpyRegionRO_sat mmpl g W hG) (by decide)
  · rw [hpan_eq]
    exact Slots.cliGhostExterns_panic_handle_error mmpl g W

/-! ## 3. Relocatable Poll Entry Unpacking -/

/-- Relocatable spatial bundle at the entry of `cliDpPollName` (Block `518`). -/
def dpPollEntrySpatialPlaced [LibsignalPlacement] {B : RunBudgets} {S : RunSem}
    (stk' : Nat) (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s0 : State) (R : SepProp) : SepProp :=
  memRegion y.out 48 ∗
  dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
  dpCxAt y.cx ∗
  storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
  protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
  protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
  coinsInstalledPlaced y.g.coinsP y.g.coins ∗
  SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
  FromRecordCallees.lsLogOff ∗
  E2E.HooksE.A0.pool ∗
  preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
  stackAt s0.sp stk' ∗
  R

/-- Pure invariants unpacked from `withLsCodeRoLoaded lsmpl (dpPollSpecState ...)` for
`pkToE? pm = none` rejections. -/
structure DpPollEntryD3PurePlaced [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {W : CliHooks} {B : RunBudgets} {S : RunSem}
    (MsgCond : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s0 : State) : Prop where
  rocl : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val
  storeOk : DecPkStoreOk ⟨W.C, W.Q⟩ y.g.F
  msgCond : MsgCond y.g.F y.g.peer.val y.g.me.val y.g.msg

theorem dpPollPre_unpack_d3_placed [LibsignalPlacement]
    {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {MsgCond : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧ MsgCond F peer me pm)
    (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S) stk')).pre y s0 ∗ R) :
    DpPollEntryD3PurePlaced (Scope := Scope) (W := W) MsgCond stk' y s0 ∧
      (s0.mem ⊨ dpPollEntrySpatialPlaced stk' y s0 R) := by
  have ⟨hrocl, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  have h1 : s0.mem ⊨
      ⌜s0.readReg64 .x0 = y.out ∧ s0.readReg64 .x1 = y.fut ∧ s0.readReg64 .x2 = y.cx ∧
        (dpSlotArgsPlaced y.g).length = 13 ∧ stk' ≤ s0.sp.toNat⌝ ∗
      (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        dpCxAt y.cx ∗
        (⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
            S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg⌝ ∗
          (⌜y.g.coins.length < 2 ^ 63⌝ ∗
            (storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
              protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
              protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
              coinsInstalledPlaced y.g.coinsP y.g.coins ∗
              SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
              FromRecordCallees.lsLogOff ∗
              E2E.HooksE.A0.pool ∗
              preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗ R)))) := by
    simpa only [dpPollSpecState, dpSlotPollKStatePlaced, RunCompose.slotFramePlaced, sepConj_assoc] using hpre0
  rw [satisfies_pure_sepConj] at h1
  obtain ⟨⟨hx0, hx1, hx2, _, hstk_le⟩, h2⟩ := h1
  have h3 : s0.mem ⊨
      ⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
          S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg⌝ ∗
      (⌜y.g.coins.length < 2 ^ 63⌝ ∗ dpPollEntrySpatialPlaced stk' y s0 R) := by
    simpa only [dpPollEntrySpatialPlaced, sepConj_comm, sepConj_left_comm, sepConj_assoc] using h2
  rw [satisfies_pure_sepConj] at h3
  obtain ⟨⟨hfiles_eq, hfilesOk, hdecPkOk⟩, h4⟩ := h3
  rw [satisfies_pure_sepConj] at h4
  obtain ⟨hcoins_lt, hm_base⟩ := h4
  obtain ⟨hFok, hstoreOk, hmsgCond⟩ :=
    hSemOk y.g.F y.g.peer.val y.g.me.val y.g.msg hfilesOk hdecPkOk
  exact ⟨⟨hrocl, hx0, hx1, hx2, hstk_le, hfiles_eq, hcoins_lt, hFok, hstoreOk, hmsgCond⟩, hm_base⟩

end LibsignalBinary.Proofs.SignalSession.Cli.D3
