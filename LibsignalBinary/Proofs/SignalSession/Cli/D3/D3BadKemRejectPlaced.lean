/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2TopPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3V3RejectPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch

/-!
# `v4` Bad-KEM & Unified `pkToE? = none` Pre-Key Rejection

Defines the version-4 Bad-KEM message condition `MsgCondBadKem`, proves placed Stage-P2
entry unpacks and unified error-exit folds on Path A and Over-Path C, and combines `v3` and
`v4` Bad-KEM poll contracts into unified `pkToE? pm = none` slot rejection theorems.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E CryptoVerification.E2E.Bin CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding Bytes PqxdhHookContracts PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderCore CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp decryptPrekeyClosureName
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs CryptoVerification.SignalSession.Cli.RunProofs.Poll
open CryptoVerification.SignalSession.Cli.KitInst hiding
  cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced cliKyberPreKeyStoreSpecPlaced
  cliPreKeyStoreSpecPlaced_quiet cliSignedPreKeyStoreSpecPlaced_quiet
open CryptoVerification.CodeLayout
open CryptoVerification.CliHandshake.Placed CryptoVerification.CliHandshake.RespClosurePlaced
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns cliGhostExterns_other)

/-! ## 1. `v4` Bad-KEM Message Condition & Store-Kit Event Lemmas -/

theorem not_p2SessMatchesMsg_of_v4_badKem {sess : Session (List (BitVec 8))} {pm : PreKeySignalMessage}
    (kp : KyberPayload) (hv4 : pm.messageVersion = 4#8) (hnm : ¬ SessMatchesPm sess pm) :
    ¬ Over.SessMatchesMsg sess 4#8 (5#8 :: bytesToBv8 (mkBadKemHdr pm kp).ekAPk) := by
  rw [bytesToBv8_mkBadKemHdr_ekAPk]; change ¬ Over.SessMatchesMsg sess 4#8 pm.baseKey.serialize
  unfold Over.SessMatchesMsg SessMatchesPm at *; intro ⟨hver, hser⟩; exact hnm ⟨hv4.symm ▸ hver, hser⟩

/-- Version-4 Bad-KEM message condition: distinct service IDs (`¬ SameServiceId peer me`),
outer `messageVersion = 4`, a Kyber payload `kp` with `pkVecTag? 8 1568 kp.ciphertext = none`,
and no loaded active peer session matching `pm`. -/
def MsgCondBadKem (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop :=
  ¬ RunProofs.SameServiceId peer me ∧ pm.messageVersion = 4#8 ∧
  (∃ kp : KyberPayload, pm.kyberPayload = some kp ∧ pkVecTag? 8#8 1568 kp.ciphertext = none) ∧
  ∀ r s, Slots.loadRec Scope F peer = .ok (some r) → r.currentSession = some s → ¬ SessMatchesPm s pm

theorem cliPollSpk_getEvs_nil {A : RustAlloc} [LibsignalPlacement] {F : FsFiles} {sid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollSpkKitPlaced A F sid σ).GetErr SignedPreKeyRecord) :
    (cliPollSpkKitPlaced A F sid σ).getEvs id ans = [] := rfl

theorem cliPollKpk_getEvs_nil {A : RustAlloc} [LibsignalPlacement] {F : FsFiles} {kid sid id : BitVec 32}
    {kbk : PublicKey} {σ : DpKitStk} (ans : Except (cliPollKpkKitPlaced A F kid sid kbk σ).GetErr KyberPreKeyRecord) :
    (cliPollKpkKitPlaced A F kid sid kbk σ).getEvs id ans = [] := rfl

theorem cliPollPk_getEvs_nil {A : RustAlloc} [LibsignalPlacement] {F : FsFiles} {pid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollPkKitPlaced A F pid σ).GetErr PreKeyRecord) :
    (cliPollPkKitPlaced A F pid σ).getEvs id ans = [] := rfl

theorem cliPollPk_opkOkEvs_nil {A : RustAlloc} [LibsignalPlacement] {F : FsFiles} {pid : BitVec 32} {σ : DpKitStk}
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkEvs (cliPollPkKitPlaced A F pid σ) opt wOpk = [] := by cases opt <;> rfl

theorem cliPollPk_opkOkUpdate_eq (A : RustAlloc) [LibsignalPlacement] (F : FsFiles) (pid : BitVec 32) (σ : DpKitStk)
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkUpdate (cliPollPkKitPlaced A F pid σ) StoresGhost.opened.oneTime opt wOpk = StoresGhost.opened.oneTime := by
  cases opt <;> rfl

theorem cliPollSelf_kpEvs_nil {A : RustAlloc} [LibsignalPlacement] {F : FsFiles} {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKitPlaced A F peer σ).KpErr IdentityKeyPair) :
    (cliPollSelfKitPlaced A F peer σ).kpEvs ans = [] := rfl

theorem distinctSid_of_not_sameAcct_d3 {rem loc : AddrGhost} (hAcct : ¬ RunProofs.SameServiceId rem.val loc.val) :
    CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid uuidTryParse loc.name.bytes rem.name.bytes :=
  fun sid hloc hrem => hAcct ⟨sid, hrem, hloc⟩

theorem stageP2OverV1CallStack_le_subStack_badKem_placed [LibsignalPlacement] {A : RustAlloc} (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    Over.stageP2OverV1CallStack (cliPollSpkKitPlaced A F0 spkId (cliKitStk B))
      (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B)) (cliPollPkKitPlaced A F0 opkIdWord (cliKitStk B))
      (cliPollSelfKitPlaced A F0 peer (cliKitStk B)) ≤ dpClosSubStack B :=
  Nat.max_le.mpr ⟨Poll.stageP2V1CallStack_le_subStack (A := A) 0#64 F0 peer spkId kpkId opkIdWord kbk B,
    Nat.le_trans (by decide : Over.stageP2OverPureAndErrStack ≤ 1048576 - 3280) (Nat.le_add_right _ _)⟩

/-! ## 2. Unified `pkToE? pm = none` Poll & Slot Combinators -/

/-- Unified `pkToE? pm = none` poll theorem dispatching version `3` to the `v3` poll
contract and version `4` to the `v4` Bad-KEM poll contract. -/
theorem cliDpPoll_pkToENone_reject_ok_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧ MsgCondPkToENone Scope F peer me pm ∧
      (∀ coins, S.decryptPrekey F peer me pm coins = some none)) (stk' : Nat)
    (hv3_poll : ∀ S' : RunSem,
      (∀ F peer me pm, S'.filesOk F peer me → S'.decPkOk F peer me pm →
        Slots.FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧ MsgCondV3 Scope F peer me pm ∧
        (∀ coins, S'.decryptPrekey F peer me pm coins = some none)) →
      subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))))
        (lsmpl.base 518)
        (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState (K₀_statePlaced B S') stk')))
    (hv4_poll : ∀ S' : RunSem,
      (∀ F peer me pm, S'.filesOk F peer me → S'.decPkOk F peer me pm →
        Slots.FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧ MsgCondBadKem Scope F peer me pm ∧
        (∀ coins, S'.decryptPrekey F peer me pm coins = some none)) →
      subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))))
        (lsmpl.base 518)
        (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState (K₀_statePlaced B S') stk'))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))))
      (lsmpl.base 518)
      (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState (K₀_statePlaced B S) stk')) := by
  refine subroutine_ok.of_codeLoaded fun y R s0 hpc hrun hpre hsp _hL => ?_
  obtain ⟨hpure, _⟩ := dpPollPre_unpack_d3_placed (W := W)
    (MsgCond := fun F peer me pm => MsgCondPkToENone Scope F peer me pm ∧
      ∀ coins, S.decryptPrekey F peer me pm coins = some none)
    (fun F peer me pm hf hd => let ⟨h1, h2, h3, h4⟩ := hok F peer me pm hf hd; ⟨h1, h2, h3, h4⟩) stk' y R s0 hpre
  obtain ⟨⟨⟨body, hparse⟩, hpkNone, hAcct, hnoMatch⟩, hAns0⟩ := hpure.msgCond
  let g0 : DecPkGhost := y.g
  let S' : RunSem :=
    { S with decPkOk := fun F peer me pm =>
        S.decPkOk F peer me pm ∧ F = g0.F ∧ peer = g0.peer.val ∧ me = g0.me.val ∧ pm = g0.msg }
  let y' : DpPollGhostState (K₀_statePlaced B S') := ⟨y.out, y.fut, y.cx, g0⟩
  have hpre' : s0.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl
      (dpPollSpecState (K₀_statePlaced B S') stk')).pre y' s0 ∗ R := by
    have hiff : S'.decPkOk g0.F g0.peer.val g0.me.val g0.msg ↔ S.decPkOk g0.F g0.peer.val g0.me.val g0.msg :=
      and_iff_left ⟨rfl, rfl, rfl, rfl⟩
    simpa only [StoreKit.withLsCodeRoLoaded, dpPollSpecState, K₀_statePlaced,
      dpSlotPollKStatePlaced, RunCompose.slotFramePlaced, y', g0, propext hiff] using hpre
  rcases version_three_or_four_of_pksmParse_some hparse with hv3 | hv4
  · exact (hv3_poll S' (fun F peer me pm _ hd => by
      have ⟨_, hF, hp, hm, hpm⟩ :
          S.decPkOk F peer me pm ∧ F = g0.F ∧ peer = g0.peer.val ∧ me = g0.me.val ∧ pm = g0.msg := hd
      subst hF; subst hp; subst hm; subst hpm
      exact ⟨hpure.filesOkPeer, hpure.storeOk, ⟨hv3, hnoMatch⟩, hAns0⟩)).mono_outcome
      y' R s0 hpc hrun hpre' hsp (fun _ hout => hout)
  · have hkpBad := (pkToE?_eq_none_iff_of_pksmParse_v4 hparse hv4).mp hpkNone
    exact (hv4_poll S' (fun F peer me pm _ hd => by
      have ⟨_, hF, hp, hm, hpm⟩ :
          S.decPkOk F peer me pm ∧ F = g0.F ∧ peer = g0.peer.val ∧ me = g0.me.val ∧ pm = g0.msg := hd
      subst hF; subst hp; subst hm; subst hpm
      exact ⟨hpure.filesOkPeer, hpure.storeOk, ⟨hAcct, hv4, hkpBad, hnoMatch⟩, hAns0⟩)).mono_outcome
      y' R s0 hpc hrun hpre' hsp (fun _ hout => hout)

/-- Unified `decPkSlotSpecPlaced` rejection contract covering both `v3` and `v4` Bad-KEM
pre-key messages. -/
theorem cliDecryptPrekey_pkToENone_reject_slot_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧ MsgCondPkToENone Scope F peer me pm ∧
      (∀ coins, S.decryptPrekey F peer me pm coins = some none))
    (hv3_poll : ∀ stk', dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 → ∀ S' : RunSem,
      (∀ F peer me pm, S'.filesOk F peer me → S'.decPkOk F peer me pm →
        Slots.FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧ MsgCondV3 Scope F peer me pm ∧
        (∀ coins, S'.decryptPrekey F peer me pm coins = some none)) →
      subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))))
        (lsmpl.base 518)
        (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState (K₀_statePlaced B S') stk')))
    (hv4_poll : ∀ stk', dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 → ∀ S' : RunSem,
      (∀ F peer me pm, S'.filesOk F peer me → S'.decPkOk F peer me pm →
        Slots.FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧ MsgCondBadKem Scope F peer me pm ∧
        (∀ coins, S'.decryptPrekey F peer me pm coins = some none)) →
      subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))))
        (lsmpl.base 518)
        (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState (K₀_statePlaced B S') stk')))
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (lsProg_520 (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))))
      (lsmpl.base 520)
      (decPkSlotSpecPlaced E2E.HooksE.A0 S stk) :=
  decPk_slot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed
      (ext := cliGhostExterns g (cliExternsPlaced mmpl W)) (K₀_statePlaced B S)
      (fun stk' h1 h2 => cliDpPoll_pkToENone_reject_ok_placed mmpl g W B S Scope hok stk'
        (hv3_poll stk' h1 h2) (hv4_poll stk' h1 h2))
      stk (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced, dpSlotPollKStatePlaced] at hstk ⊢; omega) hstk64)

theorem cliDecryptPrekey_pkToENone_reject_slot_decPkDef_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧ MsgCondPkToENone Scope F peer me pm)
    (hv3_poll : ∀ stk', dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 → ∀ S' : RunSem,
      (∀ F peer me pm, S'.filesOk F peer me → S'.decPkOk F peer me pm →
        Slots.FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧ MsgCondV3 Scope F peer me pm ∧
        (∀ coins, S'.decryptPrekey F peer me pm coins = some none)) →
      subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))))
        (lsmpl.base 518)
        (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState (K₀_statePlaced B S') stk')))
    (hv4_poll : ∀ stk', dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 → ∀ S' : RunSem,
      (∀ F peer me pm, S'.filesOk F peer me → S'.decPkOk F peer me pm →
        Slots.FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧ MsgCondBadKem Scope F peer me pm ∧
        (∀ coins, S'.decryptPrekey F peer me pm coins = some none)) →
      subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))))
        (lsmpl.base 518)
        (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState (K₀_statePlaced B S') stk')))
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (lsProg_520 (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))))
      (lsmpl.base 520)
      (decPkSlotSpecPlaced E2E.HooksE.A0 S stk) :=
  cliDecryptPrekey_pkToENone_reject_slot_placed mmpl g W B S Scope
    (fun F peer me pm hf hd => by
      obtain ⟨h1, h2, h3⟩ := hok F peer me pm hf hd
      exact ⟨h1, h2, h3, fun coins => hS ▸ decPkDef_eq_some_none_of_d3b3 X ⟨W.C, W.Q⟩ Scope F peer me pm coins h3.2.1 h3.2.2.2⟩)
    hv3_poll hv4_poll stk hstk hstk64

/-! ## 3. Placed Stage P2 Spatial Entry Unpacks & Unified Error-Exit Fold -/

/-- Spatial frame preserved untouched across `stageP2_pathA_badKem_kits_*_placed` and `stageP2_over_badKem_kits_*_placed`. -/
def badKemInnerFramePlaced [LibsignalPlacement] {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S)) (kp : KyberPayload) (rngPtr sp : BitVec 64) : SepProp :=
  (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).storeAt (y.g.stores + 240#64) StoresGhost.opened.sessions ∗
  dirAt E2E.HooksE.A0 (y.g.stores + 280#64) StoresGhost.opened.pub ∗
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
  processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
  memRegion (y.fut + 640#64) 24 ∗ memRegion (y.fut + 684#64) 8 ∗ memRegion (y.fut + 692#64) 12 ∗ memRegion (y.fut + 705#64) 7 ∗
  memRegion (y.fut + 913#64) 7 ∗ memRegion (y.fut + 1267#64) 5 ∗ memRegion (y.fut + 1922#64) 6 ∗
  (sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 120 ∗ memRegion (sp + 216#64) 348 ∗ memRegion (sp + 592#64) 20 ∗ memRegion (sp + 633#64) 39 ∗
  memRegion (sp + 688#64) 36 ∗ memRegion (sp + 736#64) 36 ∗ memRegion (sp + 784#64) 36 ∗ memRegion (sp + 832#64) 36 ∗
  spMidGapsAt sp ∗ sp550P2V1RemAt sp ∗ signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA y.g.msg.message ∗
  badKemMsgRemInnerAt y.g.msgG y.g.msgA y.g.msg kp

private theorem dup_pure_sepConj_right_d3 {φ : Prop} {P Q : SepProp}
    (h : Q ⊢ ⌜φ⌝ ∗ Q) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_right h) (by rw [sepConj_pure_left_comm]; exact Entails.refl _)

private theorem dup_pure_sepConj_left_d3 {φ : Prop} {P Q : SepProp}
    (h : P ⊢ ⌜φ⌝ ∗ P) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_left h) (by rw [sepConj_assoc]; exact Entails.refl _)

theorem badKemInnerFramePlaced_dup_kyber [LibsignalPlacement] {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S)) (kp : KyberPayload) (rngPtr sp : BitVec 64) :
    badKemInnerFramePlaced y kp rngPtr sp ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗ badKemInnerFramePlaced y kp rngPtr sp := by
  unfold badKemInnerFramePlaced
  repeat (first
    | exact badKemMsgRemInnerAt_dup_kyber y.g.msgG y.g.msgA y.g.msg kp
    | exact dup_pure_sepConj_left_d3 (badKemMsgRemInnerAt_dup_kyber y.g.msgG y.g.msgA y.g.msg kp)
    | refine dup_pure_sepConj_right_d3 ?_)

theorem stageP2BadKemPreAtPlaced_dup_kyber [LibsignalPlacement] {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S)) (kp : KyberPayload) (w : Poll.PathAEntryWords)
    (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64) :
    stageP2BadKemPreAtPlaced E2E.HooksE.A0
      (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
      (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)) (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
      y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
      StoresGhost.opened.signed StoresGhost.opened.kyber StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (badKemInnerFramePlaced y kp rngPtr sp) ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
      stageP2BadKemPreAtPlaced E2E.HooksE.A0
        (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
        (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
        (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)) (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B))
        s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
        y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
        y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
        (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
        w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
        StoresGhost.opened.signed StoresGhost.opened.kyber StoresGhost.opened.oneTime StoresGhost.opened.identity
        y.g.me y.g.peer (dpClosSubStack B) (badKemInnerFramePlaced y kp rngPtr sp) := by
  unfold stageP2BadKemPreAtPlaced
  repeat (first
    | exact badKemInnerFramePlaced_dup_kyber y kp rngPtr sp
    | exact dup_pure_sepConj_left_d3 (badKemInnerFramePlaced_dup_kyber y kp rngPtr sp)
    | refine dup_pure_sepConj_right_d3 ?_)

/-- Unpack Stage P2 Path A (`opt = none`) entry into `stageP2BadKemPreAtPlaced ... badKemInnerFramePlaced`. -/
theorem stageP2_entry_unpack_badKem_pathA_placed [LibsignalPlacement] {W : CliHooks}
    {B : RunBudgets} {S : RunSem} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S)) (kp : KyberPayload)
    (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hv4 : y.g.msg.messageVersion = 4#8) (hkp : y.g.msg.kyberPayload = some kp) (hfp : fp = sp + 3184#64)
    (hstoreOk : DecPkStoreOk ⟨W.C, W.Q⟩ y.g.F) (hFok : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → Slots.scopeIn r') :
    stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut none ∗ preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗ protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗ FromRecordCallees.lsLogOff ∗ stackAt sp (dpClosSubStack B) ⊢
      ∃∗ w : Poll.PathAEntryWords, ⌜∀ id : BitVec 32, y.g.msg.preKeyId = some id → w.opkWord = id⌝ ∗
        stageP2BadKemPreAtPlaced E2E.HooksE.A0
          (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
          (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)) (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
          y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
          StoresGhost.opened.signed StoresGhost.opened.kyber StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer (dpClosSubStack B) (badKemInnerFramePlaced y kp rngPtr sp) := by
  dsimp only [p1LoadedRecordAt, stageP2PostP1At]
  have hdrEq : ResponderClosure.sessionRecordEmptyHeaderAt (y.fut + 224#64) =
      ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 224#64) := rfl
  rw [hdrEq, coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    (cells (y.fut + 920#64) 2 ∗ memRegion (y.fut + 592#64) 48 ∗ coroUnusedP1At y.fut) ∗
    closStackUnusedP1OkAt sp ∗ storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
    (ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 224#64) ∗ memRegion (y.fut + 256#64) 336 ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 112#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 120#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 128#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 704#64) ↦₈ 0#8) ∗ ((y.fut + 816#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 904#64) ↦₆₄ (y.g.msgA + 200#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 912#64) ↦₈ 0#8) ∗ ((y.fut + 1266#64) ↦₈ 0#8) ∗ (sp ↦₆₄ 0#64) ∗
      ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ v_a8) ∗
      ((sp + 176#64) ↦₆₄ (y.fut + 912#64)) ∗ ((sp + 184#64) ↦₆₄ v_b8) ∗ ((sp + 192#64) ↦₆₄ y.cx) ∗
      ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ v_d0) ∗ memRegion (sp + 216#64) 348 ∗ memRegion (sp + 992#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗ memRegion y.out 48 ∗ E2E.HooksE.A0.pool ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗ protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      FromRecordCallees.lsLogOff ∗ stackAt sp (dpClosSubStack B)) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (preKeyMsgAt_unpack_badKem y.g.msgG y.g.msgA y.g.msg kp hv4 hkp)
    (sepConj_mono (Poll.coro_unused_split_p2v1 y.fut) (sepConj_mono_left (Poll.stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 => Entails.sepExists_elim fun u90 =>
    Entails.sepExists_elim fun u488 => Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 => Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun hopkWord => ?_
  have hstores := storesAt_entails_cliPollStoresKitsAtPlaced (A := E2E.HooksE.A0) (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := opkWord) (sid := y.g.msg.signedPreKeyId) (kid := kp.preKeyId) (kbk := y.g.msg.baseKey) (cliKitStk B) y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hScope hFok) (cliIdOwnInv_of_storeOk hstoreOk) (cliIdInv_opened_peer hFok)
    (cliPkInv_of_storeOk hstoreOk opkWord) (cliSpkInv_of_storeOk hstoreOk y.g.msg.signedPreKeyId)
    (cliKpkInvFull_of_storeOk hstoreOk kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey)
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  refine Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩ (Entails.pure_right hopkWord ?_)
  exact Entails.of_eq (by
    have htailEq : Kits.p2CoroScratchTailAt y.fut = p2CoroScratchTailAt y.fut := rfl
    dsimp only [cliPollStoresKitsAtPlaced, cliPollStoresKitsAt, stageP2BadKemPreAtPlaced, badKemInnerFramePlaced,
      cliPollSessKitPlaced, cliPollSpkKitPlaced, cliPollKpkKitPlaced, cliPollPkKitPlaced, cliPollIdKitPlaced, FromRecordCallees.lsLogOff]
    simp only [BitVec.reduceNeg]; rw [hdrEq, htailEq]; ac_rfl)

private theorem pull_pure_msg_group {M1 M2 M3 Tail : SepProp} {φ : Prop} :
    (M1 ∗ M2 ∗ (⌜φ⌝ ∗ M3)) ∗ Tail = ⌜φ⌝ ∗ ((M1 ∗ M2 ∗ M3) ∗ Tail) := by ac_rfl

/-- Unpack Stage P2 Over-Path C (`opt = some r`, `r.currentSession = some sess`) entry into
`stageP2OverBadKemPreAtPlaced ... badKemInnerFramePlaced`. -/
theorem stageP2_entry_unpack_badKem_over_placed [LibsignalPlacement] {W : CliHooks}
    {B : RunBudgets} {S : RunSem} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8))) (kp : KyberPayload)
    (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hcur : r.currentSession = some sess) (hv4 : y.g.msg.messageVersion = 4#8) (hkp : y.g.msg.kyberPayload = some kp)
    (hfp : fp = sp + 3184#64) (hstoreOk : DecPkStoreOk ⟨W.C, W.Q⟩ y.g.F)
    (hFok : Slots.FilesOkPeer Scope y.g.F y.g.peer.val) (hScope : ∀ r', Scope r' → Slots.scopeIn r') :
    stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut (some r) ∗ preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗ protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗ FromRecordCallees.lsLogOff ∗ stackAt sp (dpClosSubStack B) ⊢
      ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ w : Poll.PathAEntryWords,
        ⌜(y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63) ∧
         (∀ id : BitVec 32, y.g.msg.preKeyId = some id → w.opkWord = id)⌝ ∗
        stageP2OverBadKemPreAtPlaced E2E.HooksE.A0
          (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
          (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)) (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
          y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
          StoresGhost.opened.signed StoresGhost.opened.kyber StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer g recG sess (dpClosSubStack B) (badKemInnerFramePlaced y kp rngPtr sp) := by
  rw [sepConj_comm (stageP2PostP1At _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _, ← sepConj_assoc]
  dsimp only [p1LoadedRecordAt]; simp only [sepConj_assoc]; refine Entails.pure_left fun _hkit => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun g => ?_
  refine Entails.trans (sepConj_mono_left (sessionRecordAt_some_eq_prev_sess E2E.HooksE.A0 y.fut g r sess hcur)) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun recG => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun _hgcur => ?_
  dsimp only [stageP2PostP1At]; rw [coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    (cells (y.fut + 920#64) 2 ∗ memRegion (y.fut + 592#64) 48 ∗ coroUnusedP1At y.fut) ∗
    closStackUnusedP1OkAt sp ∗ storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
    (Poll.prevSessionsEmptyAt E2E.HooksE.A0 y.fut g ∗ sessionStateReprAt E2E.HooksE.A0 (y.fut + 248#64) recG sess ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 112#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 120#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 128#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 704#64) ↦₈ 0#8) ∗ ((y.fut + 816#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 904#64) ↦₆₄ (y.g.msgA + 200#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 912#64) ↦₈ 0#8) ∗ ((y.fut + 1266#64) ↦₈ 0#8) ∗ (sp ↦₆₄ 0#64) ∗
      ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗ ((sp + 168#64) ↦₆₄ v_a8) ∗
      ((sp + 176#64) ↦₆₄ (y.fut + 912#64)) ∗ ((sp + 184#64) ↦₆₄ v_b8) ∗ ((sp + 192#64) ↦₆₄ y.cx) ∗
      ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ v_d0) ∗ memRegion (sp + 216#64) 348 ∗ memRegion (sp + 992#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗ memRegion y.out 48 ∗ E2E.HooksE.A0.pool ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗ protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      FromRecordCallees.lsLogOff ∗ stackAt sp (dpClosSubStack B)) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (preKeyMsgAt_unpack_badKem y.g.msgG y.g.msgA y.g.msg kp hv4 hkp)
    (sepConj_mono (Poll.coro_unused_split_p2v1 y.fut) (sepConj_mono_left (Poll.stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 => Entails.sepExists_elim fun u90 =>
    Entails.sepExists_elim fun u488 => Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 => Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun hopkWord => ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (badKemMsgRemInnerAt_dup_kyber y.g.msgG y.g.msgA y.g.msg kp)))) ?_
  rw [pull_pure_msg_group]; refine Entails.pure_left fun hkyb => ?_
  have hstores := storesAt_entails_cliPollStoresKitsAtPlaced (A := E2E.HooksE.A0) (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := opkWord) (sid := y.g.msg.signedPreKeyId) (kid := kp.preKeyId) (kbk := y.g.msg.baseKey) (cliKitStk B) y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hScope hFok) (cliIdOwnInv_of_storeOk hstoreOk) (cliIdInv_opened_peer hFok)
    (cliPkInv_of_storeOk hstoreOk opkWord) (cliSpkInv_of_storeOk hstoreOk y.g.msg.signedPreKeyId)
    (cliKpkInvFull_of_storeOk hstoreOk kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey)
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  have hprevEq : Poll.prevSessionsEmptyAt E2E.HooksE.A0 y.fut g = Matched.prevSessionsEmptyAt E2E.HooksE.A0 y.fut g := rfl
  refine Entails.sepExists_right g (Entails.sepExists_right recG
    (Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩ (Entails.pure_right ⟨hkyb, hopkWord⟩ ?_)))
  exact Entails.of_eq (by
    have htailEq : Kits.p2CoroScratchTailAt y.fut = p2CoroScratchTailAt y.fut := rfl
    dsimp only [cliPollStoresKitsAtPlaced, cliPollStoresKitsAt, stageP2OverBadKemPreAtPlaced, badKemInnerFramePlaced,
      cliPollSessKitPlaced, cliPollSpkKitPlaced, cliPollKpkKitPlaced, cliPollPkKitPlaced, cliPollIdKitPlaced, FromRecordCallees.lsLogOff]
    simp only [BitVec.reduceNeg]; rw [hprevEq, htailEq]; ac_rfl)

set_option maxHeartbeats 800000 in
/-- Fold any placed Stage P2 Bad-KEM error exit (`p2BadKemErrFrameAtPlaced ... badKemInnerFramePlaced`)
into `dpFutDoneAt ∗ memRegion sp 3280 ∗ decResAt ∗ storesAt ∗ preKeyMsgAt ∗ ... ∗ anyHeap`. -/
theorem p2BadKemErrFrame_fold_placed [LibsignalPlacement] {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (kp : KyberPayload) (w : Poll.PathAEntryWords) (s0 : State) (sp fp rngPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (hv4 : y.g.msg.messageVersion = 4#8) (hkp : y.g.msg.kyberPayload = some kp) (hfp : fp = sp + 3184#64)
    (hopk : ∀ id : BitVec 32, y.g.msg.preKeyId = some id → w.opkWord = id) :
    (decResAt E2E.HooksE.A0 y.out (.error err) ∗ anyHeap) ∗
    (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F y.g.msg.signedPreKeyId (cliKitStk B)).storeAt (y.g.stores + 80#64) StoresGhost.opened.signed ∗
    (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B)).storeAt (y.g.stores + 120#64) StoresGhost.opened.kyber ∗
    (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)).storeAt (y.g.stores + 200#64) StoresGhost.opened.oneTime ∗
    (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B)).identityAt y.g.stores StoresGhost.opened.identity ∗
    p2BadKemErrFrameAtPlaced E2E.HooksE.A0 s0 sp fp y.fut y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym)
      y.g.peerA (y.g.msgA + 200#64) (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion
      w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId y.g.me y.g.peer (dpClosSubStack B)
      (badKemInnerFramePlaced y kp rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗ memRegion sp 3280 ∗ decResAt E2E.HooksE.A0 y.out (.error err) ∗
      storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗ preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗ protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗ stackAt sp (dpClosSubStack B) ∗ anyHeap := by
  have hstores := cliPollStoresKitsAtPlaced_entails_storesAt (A := E2E.HooksE.A0) (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := w.opkWord) (sid := y.g.msg.signedPreKeyId) (kid := kp.preKeyId) (kbk := y.g.msg.baseKey) (cliKitStk B) y.g.stores StoresGhost.opened
  have hmsgFold := p2BadKemMsgFields_reassemble y.g.msgG y.g.msgA y.g.msg kp w.opkWord hv4 hkp hopk
  have hcoro := Poll.p2_coro_err_fold y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 240#64) (lsρ cliSessionVtSym)
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hstk := Poll.p2_stack_err_fold sp fp s0 hfp
  dsimp only [p2BadKemErrFrameAtPlaced, badKemInnerFramePlaced]
  refine Entails.trans (show _ ⊢
    (processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 112#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 120#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 128#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      memRegion (y.fut + 224#64) 368 ∗ cells (y.fut + 592#64) 6 ∗ memRegion (y.fut + 640#64) 24 ∗ memRegion (y.fut + 664#64) 20 ∗
      memRegion (y.fut + 684#64) 8 ∗ memRegion (y.fut + 692#64) 12 ∗ ((y.fut + 704#64) ↦₈ 1#8) ∗
      ((y.fut + 816#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 904#64) ↦₆₄ (y.g.msgA + 200#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 912#64) ↦₈ 1#8) ∗ memRegion (y.fut + 920#64) 96 ∗ ((y.fut + 1265#64) ↦₈ 0#8) ∗ ((y.fut + 1266#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 705#64) 7 ∗ memRegion (y.fut + 913#64) 7 ∗ memRegion (y.fut + 1160#64) 8 ∗ memRegion (y.fut + 1200#64) 65 ∗
      memRegion (y.fut + 1267#64) 5 ∗ p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 1922#64) 6) ∗
    ((sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 120 ∗ memRegion (sp + 128#64) 88 ∗ memRegion (sp + 216#64) 348 ∗ memRegion (sp + 592#64) 20 ∗
      memRegion (sp + 624#64) 9 ∗ memRegion (sp + 633#64) 39 ∗ memRegion (sp + 688#64) 36 ∗ memRegion (sp + 736#64) 36 ∗
      memRegion (sp + 784#64) 36 ∗ memRegion (sp + 832#64) 36 ∗ memRegion (sp + 880#64) 36 ∗
      memRegion (sp + 928#64) 8 ∗ memRegion (sp + 940#64) 1 ∗ memRegion (sp + 944#64) 48 ∗ memRegion (sp + 992#64) 368 ∗
      spMidGapsAt sp ∗ cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗ cells (sp + 2016#64) 4 ∗ cells (sp + 2352#64) 8 ∗
      memRegion (sp + 2704#64) 288 ∗ memRegion (fp + -128#64) 9 ∗ sp550P2V1RemAt sp ∗ decryptPrekeySavedRegsAt (sp + 3280#64) s0) ∗
    decResAt E2E.HooksE.A0 y.out (.error err) ∗
    cliPollStoresKitsAtPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer w.opkWord
      y.g.msg.signedPreKeyId kp.preKeyId y.g.msg.baseKey (cliKitStk B) y.g.stores StoresGhost.opened ∗
    (p2BadKemMsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkBadKemHdr y.g.msg kp) kp.ciphertext
        y.g.msg.message.messageVersion w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId ∗
      signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA y.g.msg.message ∗
      badKemMsgRemInnerAt y.g.msgG y.g.msgA y.g.msg kp) ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗ protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗ stackAt sp (dpClosSubStack B) ∗ anyHeap
    by exact Entails.of_eq (by
      dsimp only [cliPollStoresKitsAtPlaced, cliPollStoresKitsAt, cliPollSessKitPlaced, cliPollSpkKitPlaced,
        cliPollKpkKitPlaced, cliPollPkKitPlaced, cliPollIdKitPlaced, FromRecordCallees.lsLogOff]
      simp only [BitVec.reduceNeg]; ac_rfl)) ?_
  exact sepConj_mono hcoro (sepConj_mono hstk (sepConj_mono_right (sepConj_mono hstores (sepConj_mono_left hmsgFold))))

/-! ## 4. Callee Transfers & Error-Word Helpers on `stageP1ProgPlaced` -/

theorem subroutine_ok_withLsFrozen_of_rocl [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog entry (withLsFrozen lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := extract_withLsFrozen hp
      dsimp only [StoreKit.withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨StageP2MemInv.frozen.toCodeRo hfr, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem initializeBobSession_badKem_errOwned_placed_ok_on_stageP1 [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    (h_accept : subroutine_ok (lsProg_75 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 79)
      (pqxdhAcceptBadKemErrOwnedPlacedSpec E2E.HooksE.A0)) :
    subroutine_ok (stageP1ProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 75)
      (initializeBobSessionBadKemErrOwnedPlacedSpec E2E.HooksE.A0) := by
  rw [stageP1ProgPlaced_eq_dpPollProgPlaced mmpl g W]
  have hrocl := StoreKit.ls_subroutine_ok_rocl_of_block
    (callerProg := Poll.dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (i := 518) (j := 75)
    (initializeBobSession_badKem_errOwned_placed_ok_of_accept h_accept)
    (by decide) (by decide) (by decide)
  exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

theorem cliIsSameAccount_placed_ok_on_stageP1_d3 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (stageP1ProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 17)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountDistinctSpec E2E.HooksE.A0 uuidTryParse)) :=
  Kits.isSameAccount_placed_ok_on_stageP1
    ((cliGhostExterns_other g (cliExternsPlaced mmpl W)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (RunGlue.cliExternsPlaced_row mmpl W (Slots.blackBox_row_placed mmpl W)))
    (cliUuidTryParse_placed_ok_d3 mmpl g W)

theorem badKemSpeWords_entails_decResAt_anyHeap
    (A : RustAlloc) (out errTag w2 w3 w4 w5 w6 : BitVec 64)
    (err : ApiError AddrVal Unit) :
    speWordsAt out errTag w2 w3 w4 w5 w6 ∗
    pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ⊢
    decResAt A out (.error err) ∗ anyHeap := by
  unfold pqxdhBadKemErrPayloadAt
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun isStr => ?_
  cases isStr
  · simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun i => ?_
    rw [sepConj_comm]
    refine Entails.pure_left fun ⟨hi, htag⟩ => ?_
    subst htag
    exact Entails.trans
      (plainSpeWords_entails_decResAt_err A out i (show RunDrop.PlainSpeTag i from hi) w2 w3 w4 w5 w6 err)
      (entails_sepConj_anyHeap _)
  · simp only [↓reduceIte]
    rw [← sepConj_assoc, sepConj_comm (speWordsAt out errTag w2 w3 w4 w5 w6) ⌜errTag = speWord 24⌝,
        sepConj_assoc]
    refine Entails.pure_left fun htag => ?_
    subst htag
    have hstr := strSpeWords_entails_decResAt_anyHeap A out 24 (by decide) w2 w3 w4 w5 w6 emp err
    rwa [sepConj_emp] at hstr

end LibsignalBinary.Proofs.SignalSession.Cli.D3
