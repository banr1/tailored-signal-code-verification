/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Placed D2(c) Top-Level Poll Closure Assembly (`PollOverPlaced`)

Relocatable (`[LibsignalPlacement]`) counterpart of `DecryptPrekey/Over/PollOver.lean` on Block `518`
(`dpPollProgPlaced`), proving Stage P1 postcondition reassembly, `closure_trusted_d2c_placed_ok`,
`cliDpPollOk_d2c_placed_of_stages`, and `d2cStages_placed_inst` (plus `LibsignalFrozen` variants).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.Variant
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.CliHandshake.RespClosurePlaced

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Stage P1 Postcondition Reassembly (`overP1Ok_recombine_entails_stageP2_placed`) -/

theorem overP1Ok_post_eq_stageP2PostP1At_placed [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s0 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kid sid kbk σ
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt Scope E2E.HooksE.A0 y.fut opt ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗
      cells (y.fut + 0x398#64) 2 ∗
      ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      E2E.HooksE.A0.pool) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗
      memRegion y.out 48) =
    stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Scope E2E.HooksE.A0 y.fut opt := by
  dsimp only [stageP2PostP1At, cliPollSessKitPlaced, cliPollIdKitPlaced,
    cliPollPkKitPlaced, cliPollSpkKitPlaced, cliPollKpkKitPlaced,
    cliIdStoreSpecFullPlaced, cliPreKeyStoreSpecPlaced,
    cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
    cliKyberPreKeyStoreSpecPlaced]
  sep_frame

theorem overP1Ok_recombine_entails_stageP2_placed [LibsignalPlacement]
    {B : RunBudgets} {S : RunSem}
    (stk' : Nat) (_hneed : dpPollNeed B ≤ stk') (_hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s0 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kid sid kbk σ
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut opt ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗
      cells (y.fut + 0x398#64) 2 ∗
      ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      FromRecordCallees.lsLogOff ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores
        (ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey
          .receiving (.ok true)) ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      E2E.HooksE.A0.pool ∗
      stackAt sp (stageP1CallStack kit ikit)) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗
      memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit) ⊢
    stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut opt ∗
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
    LsTokenInit ∗
    FromRecordCallees.lsLogOff ∗
    stackAt sp (dpClosSubStack B) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le : stageP1CallStack kit ikit ≤ dpClosSubStack B :=
    stageP1CallStack_le_subStack (A := E2E.HooksE.A0) 0#64 y.g.F Slots.scopeKit y.g.peer B
  have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := E2E.HooksE.A0)
    (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
  have hp1_eq := overP1Ok_post_eq_stageP2PostP1At_placed (Scope := Slots.scopeKit)
    y s0 rngPtr v_a8 v_b8 v_d0 opt
  dsimp only at hp1_eq
  have hp1_ent := Entails.of_eq hp1_eq
  have hpm_ent := Entails.of_eq
    (preKeyMsgAt_eq_idKey_sep E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg).symm
  have hstk_ent := Entails.of_eq
    (stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64).symm
  have h4 := sepConj_mono hp1_ent (sepConj_mono hstores_back (sepConj_mono hpm_ent hstk_ent))
  let Pass : SepProp :=
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    LsTokenInit ∗
    FromRecordCallees.lsLogOff ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have htrust_id : ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val
      y.g.msg.identityKey .receiving (.ok true) = StoresGhost.opened.identity := rfl
  refine Entails.trans ?_ (Entails.trans (sepConj_mono_left h4 : _ ∗ Pass ⊢ _ ∗ Pass) ?_)
  · rw [htrust_id]
    dsimp only [cliPollStoresKitsAtPlaced, Pass, sp, σ, pid, sid, kid, kbk, kit, ikit]
    sep_frame
  · dsimp only [Pass, sp, σ, kit, ikit]
    sep_frame

/-! ## 2. Base Poll Stage Bundle Interfaces (`ClosureBaseStagesCliPlacedStmt` / `ClosureBaseStagesPlacedStmt`) -/

def OverClosurePathAPlacedStmt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r', Scope r' → Slots.scopeIn r') →
    S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope →
    ∀ (stk' : Nat), dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
    ∀ (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
      (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp),
      s0.fs.files = y.g.F →
      Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
      DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
      y.g.coins.length < 2 ^ 63 →
      StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
        y.g.msg.identityKey = .ok true →
      (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer
        (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok none) →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1 →
      s1.trace = s0.trace →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = s0.sp - 0xcd0#64 →
      dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat →
      s1.pc = dpPollEntryPlaced + 0x0868#64 →
      s1.status = .Running →
      (s1.sp &&& 15#64 == 0#64) = true →
      StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
      let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
      let K := dpSlotPollKStatePlaced E2E.HooksE.A0 B S
      let sp := s0.sp - 0xcd0#64
      SepWPp prog (s0.readReg64 .x30) s1
        (stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut none ∗
         preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
         protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
         coinsInstalledPlaced y.g.coinsP y.g.coins ∗
         storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
         LsTokenInit ∗
         FromRecordCallees.lsLogOff ∗
         stackAt sp (dpClosSubStack B) ∗
         memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
         memRegion y.cx 32)
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R))

def OverClosurePathBPlacedStmt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r', Scope r' → Slots.scopeIn r') →
    S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope →
    ∀ (stk' : Nat), dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
    ∀ (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
      (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
      (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp),
      s0.fs.files = y.g.F →
      Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
      DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
      y.g.coins.length < 2 ^ 63 →
      StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
        y.g.msg.identityKey = .ok true →
      (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer
        (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)) →
      r.currentSession = some sess →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1 →
      s1.trace = s0.trace →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = s0.sp - 0xcd0#64 →
      dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat →
      s1.pc = dpPollEntryPlaced + 0x0868#64 →
      s1.status = .Running →
      (s1.sp &&& 15#64 == 0#64) = true →
      StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
      let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
      let K := dpSlotPollKStatePlaced E2E.HooksE.A0 B S
      let sp := s0.sp - 0xcd0#64
      SepWPp prog (s0.readReg64 .x30) s1
        (stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut (some r) ∗
         preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
         protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
         coinsInstalledPlaced y.g.coinsP y.g.coins ∗
         storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
         LsTokenInit ∗
         FromRecordCallees.lsLogOff ∗
         stackAt sp (dpClosSubStack B) ∗
         memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
         memRegion y.cx 32)
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R))

def OverStageP1OkCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) (remoteIdKey : IdentityKey),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced E2E.HooksE.A0 F0 Slots.scopeKit peer σ
    let ikit := cliPollIdKitPlaced E2E.HooksE.A0 F0 peer σ
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) →
    stageP1CallStack kit ikit ≤ 2 ^ 64 →
    (∀ ans, kit.loadRel StoresGhost.opened.sessions peer.val ans → ans.isOk = true) →
    (∀ ans, ikit.trustRel StoresGhost.opened.identity peer.val remoteIdKey .receiving ans →
      ans = .ok true) →
    ∀ (s0 : State)
      (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
       sessStorePtr idStorePtr
       preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
       kyberStorePtr kyberStoreVt rngPtr
       v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
      (b_390 b_4f2 : BitVec 8),
      StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem →
      s0.fs.files = F0 →
      s0.pc = dpPollEntryPlaced →
      s0.status = .Running →
      (s0.sp &&& 15#64 == 0#64) = true →
      s0.sp - 0xcd0#64 = sp →
      s0.readReg64 .x0 = outPtr →
      s0.readReg64 .x1 = coroPtr →
      s0.readReg64 .x2 = ctxPtr →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (dpPollEntryPlaced + 0x868#64) s0
        (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
           sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
           preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
           kyberStorePtr kyberStoreVt rngPtr ∗
         cells (coroPtr + 0x70#64) 14 ∗
         cells (coroPtr + 0xe0#64) 4 ∗
         memRegion (coroPtr + 0x100#64) 336 ∗
         ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
         cells (coroPtr + 0x2c8#64) 25 ∗
         ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
         ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
         cells (coroPtr + 0x428#64) 8 ∗
         cells (coroPtr + 0x490#64) 4 ∗
         ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
         (sp ↦₆₄ v_sp0) ∗
         ((sp + 0x98#64) ↦₆₄ u_98) ∗
         ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
         ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
         ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
         ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
         ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (sp + 0xd8#64) 348 ∗
         memRegion (sp + 0x3e0#64) 368 ∗
         cells (s0.sp - 0x60#64) 12 ∗
         FromRecordCallees.lsLogOff ∗
         kit.storeAt sessStorePtr StoresGhost.opened.sessions ∗
         ikit.identityAt idStorePtr StoresGhost.opened.identity ∗
         protocolAddressAt E2E.HooksE.A0 peer remoteAddrPtr ∗
         ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
         E2E.HooksE.A0.pool ∗
         stackAt sp (stageP1CallStack kit ikit))
        (fun sf P_f =>
          (∃ opt : Option (SessionRecord (List (BitVec 8))),
            kit.loadRel StoresGhost.opened.sessions peer.val (.ok opt) ∧
            ikit.trustRel StoresGhost.opened.identity peer.val remoteIdKey .receiving (.ok true) ∧
            sf.trace = s0.trace ++ kit.loadEvs E2E.Record.encodeRecord peer.val (.ok opt) ++
              ikit.trustEvs peer.val remoteIdKey .receiving (.ok true) ∧
            (P_f ⊢
              ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
                decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                  preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                  kyberStorePtr kyberStoreVt rngPtr ∗
                decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                  preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                  kyberStorePtr kyberStoreVt rngPtr ∗
                p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 coroPtr opt ∗
                ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
                processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                  spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
                processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                  spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
                ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
                cells (coroPtr + 0x398#64) 2 ∗
                ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
                (sp ↦₆₄ 0#64) ∗
                ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
                ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
                ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
                ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
                ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
                ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
                ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
                memRegion (sp + 0xd8#64) 348 ∗
                memRegion (sp + 0x3e0#64) 368 ∗
                decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
                FromRecordCallees.lsLogOff ∗
                kit.storeAt sessStorePtr StoresGhost.opened.sessions ∗
                ikit.identityAt idStorePtr
                  (ikit.trustUpdate StoresGhost.opened.identity peer.val remoteIdKey
                    .receiving (.ok true)) ∗
                protocolAddressAt E2E.HooksE.A0 peer remoteAddrPtr ∗
                ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
                E2E.HooksE.A0.pool ∗
                stackAt sp (stageP1CallStack kit ikit))) ∧
          sf.sp = sp ∧
          sf.readReg64 .x8 = kyberStorePtr ∧
          sf.readReg64 .x9 = msgPtr ∧
          sf.readReg64 .x10 = kyberStoreVt ∧
          sf.readReg64 .x11 = preKeyStorePtr ∧
          sf.readReg64 .x12 = remoteAddrPtr ∧
          sf.readReg64 .x13 = preKeyStoreVt ∧
          sf.readReg64 .x14 = localAddrPtr ∧
          sf.readReg64 .x15 = idStorePtr ∧
          sf.readReg64 .x16 = ikit.id_vt ∧
          sf.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
          sf.readReg64 .x19 = coroPtr ∧
          sf.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
          sf.readReg64 .x22 = spkStorePtr ∧
          sf.readReg64 .x23 = coroPtr + 0xe0#64 ∧
          sf.readReg64 .x24 = spkStoreVt ∧
          sf.readReg64 .x25 = sp + 0x210#64 ∧
          sf.readReg64 .x28 = sp + 0xa90#64 ∧
          sf.readReg64 .x29 = s0.sp - 0x60#64 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
        (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0)

def OverClosureUntrustedD2cPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r, Scope r → Slots.scopeIn r) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope →
    ∀ (stk' : Nat), dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
    ∀ (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
      (R : SepProp) (s0 : State),
      s0.pc = dpPollEntryPlaced →
      s0.status = .Running →
      s0.spAligned = true →
      StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem →
      s0.readReg64 .x0 = y.out →
      s0.readReg64 .x1 = y.fut →
      s0.readReg64 .x2 = y.cx →
      s0.fs.files = y.g.F →
      Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
      StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
        y.g.msg.identityKey = .ok false →
      (s0.mem ⊨
        memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        memRegion y.cx 32 ∗
        storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
        protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
        protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        FromRecordCallees.lsLogOff ∗
        E2E.HooksE.A0.pool ∗
        preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R) →
      let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
      let K := dpSlotPollKStatePlaced E2E.HooksE.A0 B S
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f =>
            (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
              (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).post y s0 sf ∗ R)) ∧
              sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f =>
            Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
              (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R))

structure ClosureBaseStagesCliPlacedStmt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop where
  untrustedD2c : OverClosureUntrustedD2cPlacedStmt
  stageP1Ok : OverStageP1OkCliPlacedStmt
  cliTryDecryptPqV1 : OverCliTryDecryptPqV1PlacedStmt mmpl gh W
  pathA : OverClosurePathAPlacedStmt mmpl gh W
  pathB : OverClosurePathBPlacedStmt mmpl gh W

structure ClosureBaseStagesPlacedStmt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop where
  stageP1Untrusted : StageP1UntrustedPlacedStmt
  stageP1Ok : StageP1OkPlacedStmt
  cliTryDecryptPqV1 : OverCliTryDecryptPqV1PlacedStmt mmpl gh W
  pathA : OverClosurePathAPlacedStmt mmpl gh W
  pathB : OverClosurePathBPlacedStmt mmpl gh W

def OverClosurePathAFrozenPlacedStmt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r', Scope r' → Slots.scopeIn r') →
    S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope →
    ∀ (stk' : Nat), dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
    ∀ (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
      (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp),
      s0.fs.files = y.g.F →
      Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
      DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
      y.g.coins.length < 2 ^ 63 →
      StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
        y.g.msg.identityKey = .ok true →
      (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer
        (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok none) →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1 →
      s1.trace = s0.trace →
      LibsignalFrozen lsmpl s1.mem →
      s1.sp = s0.sp - 0xcd0#64 →
      dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat →
      s1.pc = dpPollEntryPlaced + 0x0868#64 →
      s1.status = .Running →
      (s1.sp &&& 15#64 == 0#64) = true →
      StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
      let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
      let K := dpSlotPollKStatePlaced E2E.HooksE.A0 B S
      let sp := s0.sp - 0xcd0#64
      SepWPp prog (s0.readReg64 .x30) s1
        (stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut none ∗
         preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
         protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
         coinsInstalledPlaced y.g.coinsP y.g.coins ∗
         storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
         LsTokenInit ∗
         FromRecordCallees.lsLogOff ∗
         stackAt sp (dpClosSubStack B) ∗
         memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
         memRegion y.cx 32)
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (withLsFrozen lsmpl (dpPollSpecState K stk')).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (withLsFrozen lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R))

def OverClosurePathBFrozenPlacedStmt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r', Scope r' → Slots.scopeIn r') →
    S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope →
    ∀ (stk' : Nat), dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
    ∀ (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
      (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
      (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp),
      s0.fs.files = y.g.F →
      Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
      DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
      y.g.coins.length < 2 ^ 63 →
      StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
        y.g.msg.identityKey = .ok true →
      (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer
        (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)) →
      r.currentSession = some sess →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1 →
      s1.trace = s0.trace →
      LibsignalFrozen lsmpl s1.mem →
      s1.sp = s0.sp - 0xcd0#64 →
      dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat →
      s1.pc = dpPollEntryPlaced + 0x0868#64 →
      s1.status = .Running →
      (s1.sp &&& 15#64 == 0#64) = true →
      StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
      let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
      let K := dpSlotPollKStatePlaced E2E.HooksE.A0 B S
      let sp := s0.sp - 0xcd0#64
      SepWPp prog (s0.readReg64 .x30) s1
        (stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut (some r) ∗
         preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
         protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
         coinsInstalledPlaced y.g.coinsP y.g.coins ∗
         storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
         LsTokenInit ∗
         FromRecordCallees.lsLogOff ∗
         stackAt sp (dpClosSubStack B) ∗
         memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
         memRegion y.cx 32)
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (withLsFrozen lsmpl (dpPollSpecState K stk')).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (withLsFrozen lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R))

structure ClosureBaseStagesCliFrozenPlacedStmt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop where
  untrustedD2c : OverClosureUntrustedD2cPlacedStmt
  stageP1Ok : OverStageP1OkCliPlacedStmt
  cliTryDecryptPqV1 : OverCliTryDecryptPqV1PlacedStmt mmpl gh W
  pathA : OverClosurePathAFrozenPlacedStmt mmpl gh W
  pathB : OverClosurePathBFrozenPlacedStmt mmpl gh W

theorem ClosureBaseStagesPlacedStmt.toCli [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (h : ClosureBaseStagesPlacedStmt mmpl gh W) :
    ClosureBaseStagesCliPlacedStmt mmpl gh W where
  untrustedD2c := fun mmpl' gh' W' X B S Scope hh _hRead _hDeser hinjK hsub hS stk' hneed hstk63 y R s0 =>
    closure_untrusted_d2c_placed_ok
      (fun {_A _ext _Scope _enc _kit _ikit _st _ist} =>
        @h.stageP1Untrusted _A _ext _Scope _enc _kit _ikit _st _ist)
      mmpl' gh' W' X B S Scope hh hinjK hsub hS stk' hneed hstk63 y R s0
  stageP1Ok := fun mmpl' gh' W' B F0 peer remoteIdKey hh _hRead _hDeser hp1_64 hload htrust
      s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
      sessStorePtr idStorePtr preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt rngPtr v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
      b_390 b_4f2 hro0 hfiles0 hpc hrun hsp_align0 hsp_eq hx0 hx1 hx2 =>
    h.stageP1Ok
      (A := E2E.HooksE.A0) (ext := cliGhostExterns gh' (cliExternsPlaced mmpl' W'))
      (Scope := Slots.scopeKit) (encRecord := E2E.Record.encodeRecord)
      (kit := cliPollSessKitPlaced E2E.HooksE.A0 F0 Slots.scopeKit peer (cliKitStk B))
      (ikit := cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      (st := StoresGhost.opened.sessions) (ist := StoresGhost.opened.identity)
      peer remoteIdKey hh.alloc hp1_64 rfl rfl
      hload htrust s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
      sessStorePtr idStorePtr preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt rngPtr v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
      b_390 b_4f2 hro0 (cliPollStageP1_fsAt_placed hh F0 Slots.scopeKit peer B hfiles0)
      hpc hrun hsp_align0 hsp_eq hx0 hx1 hx2
  cliTryDecryptPqV1 := h.cliTryDecryptPqV1
  pathA := h.pathA
  pathB := h.pathB

/-! ## 3. Trusted-Identity Branch (`trusted = .ok true`): Stage P1 → Path A / Path B / Path C -/

set_option maxHeartbeats 1000000 in
theorem closure_trusted_d2c_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hSt2 : ClosureBaseStagesCliPlacedStmt mmpl gh W)
    (hD2c : D2cStagesPlacedStmt mmpl gh W)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hstk_sp : stk' ≤ s0.sp.toNat)
    (hro0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hm_base : s0.mem ⊨ dpPollEntrySpatialPlaced stk' y s0 R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced E2E.HooksE.A0 B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  dsimp only [dpPollEntrySpatialPlaced] at hm_base
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kid sid kbk σ
  let sp := s0.sp - 0xcd0#64
  have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using hsp
  have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
    (subStack_le_sp_of_dpPollNeed hneed hstk_sp).1
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c σ y.g.stores
    hsub hfPeer hdecOk pid sid kid kbk
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      cliPollStoresKitsAtPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer
        pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le : stageP1CallStack kit ikit ≤ dpClosSubStack B :=
    stageP1CallStack_le_subStack (A := E2E.HooksE.A0) 0#64 y.g.F Slots.scopeKit y.g.peer B
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
      preKeyMsgAt_eq_idKey_sep E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_ok s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_98, u_a0, u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  rw [← ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)] at hm_flat
  simp only [Nat.reduceMul] at hm_flat
  dsimp only [cliPollStoresKitsAtPlaced, coroUnusedP1AtPlaced] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗
    cells (y.fut + 0xe0#64) 4 ∗
    memRegion (y.fut + 0x100#64) 336 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
    cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗
    ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
    ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
    cells (y.fut + 0x428#64) 8 ∗
    cells (y.fut + 0x490#64) 4 ∗
    ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
    (sp ↦₆₄ v_sp0) ∗
    ((sp + 0x98#64) ↦₆₄ u_98) ∗
    ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
    ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
    ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
    ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
    ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x3e0#64) 368 ∗
    cells (s0.sp - 0x60#64) 12 ∗
    FromRecordCallees.lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    E2E.HooksE.A0.pool ∗
    stackAt sp (stageP1CallStack kit ikit)
  let Fr_inner : SepProp :=
    memRegion (y.fut + 0x250#64) 48 ∗
    coroUnusedP1At y.fut ∗
    closStackUnusedP1OkAt sp ∗
    memRegion y.out 48 ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1CallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    LsTokenInit
  have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
    Satisfies.mono (by
      dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
        cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
        cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced,
        cliPreKeyStoreSpecPlaced, cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
        cliKyberPreKeyStoreSpecPlaced]
      sep_frame) hm_flat
  refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
  have hwp := hSt2.stageP1Ok mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey hh hRead hDeser
    (Nat.le_trans hp1_le hsub64)
    (fun _ (h : (cliPollSessKit E2E.HooksE.A0 0#64 y.g.F Slots.scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit E2E.HooksE.A0 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390 b_4f2
    hro0 hfiles0 hpc hrun hsp_align0 rfl hx0 hx1 hx2
  refine sepWPp_bind_p1 hwp rfl ?_ ?_
  · intro sm P_m _hsteps hpanm _hsteps' hm_pan
    exact dpPollOnPanic_of_closOom_placed stk' y hpanm hm_pan
  · intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, hro1⟩
    have htr1 : s1.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true :=
      hs1_sp ▸ sp_sub_cd0_align_std3 hsp_align0
    have hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) :=
      ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
       hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1⟩
    refine sepWPp_conseq_pre (sepConj_mono_left hent_1) ?_
    simp only [sepExists_sepConj_left]
    refine sepWPp_sepExists_left fun v_a8 =>
      sepWPp_sepExists_left fun v_b8 =>
      sepWPp_sepExists_left fun v_d0 => ?_
    have hrecomb := overP1Ok_recombine_entails_stageP2_placed stk' hneed hstk63 y s0
      coins v_a8 v_b8 v_d0 opt
    dsimp only at hrecomb
    refine sepWPp_conseq_pre hrecomb ?_
    let S0 : RunSem := { S with decryptPrekey := decPkDef X ⟨W.C, W.Q⟩ Scope }
    let y0 : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S0) :=
      ⟨y.out, y.fut, y.cx, y.g⟩
    cases opt with
    | none =>
      have hloadNone : Slots.loadRec Scope y.g.F y.g.peer.val = .ok none :=
        loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload_rel
      have hnone : ∀ r', Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r') →
          r'.currentSession = none := by
        intro r' hr'; rw [hloadNone] at hr'; cases hr'
      have hdecOk0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg :=
        hdecOk.toDecPkOk₀_of_noCurrent hnone
      have hEq : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
          S0.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins := by
        dsimp only [S0]
        rw [hS]
        exact decPkDefD2c_eq_decPkDef_of_noCurrent X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val
          y.g.me.val y.g.msg y.g.coins hnone
      exact sepWPp_pollGoal_of_decPk_eq_placed stk' y s0 s1 _ R hEq
        (hSt2.pathA X B S0 Scope hh hRead hDeser hinjK hsub rfl
          stk' hneed hstk63 y0 s0 s1 coins v_a8 v_b8 v_d0 R hfiles0 hfPeer hdecOk0 hcoins htrusted
          hload_rel hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1)
    | some r =>
      obtain ⟨sess, hcur⟩ :=
        currentSession_some_of_cliPollSess_loadRel (A := E2E.HooksE.A0) (b := 0#64)
          (F0 := y.g.F) (peer := y.g.peer) (σ := σ) hload_rel
      have hloadSome : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
        loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload_rel
      rcases Classical.em (SessMatchesPm sess y.g.msg) with hmatch | hnot_match
      · have hdecOk0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg :=
          hdecOk.toDecPkOk₀_of_match hloadSome hcur hmatch
        have hEq : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
            S0.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins := by
          dsimp only [S0]
          rw [hS]
          exact decPkDefD2c_eq_decPkDef_of_match X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val
            y.g.me.val y.g.msg y.g.coins hloadSome hcur hmatch
        exact sepWPp_pollGoal_of_decPk_eq_placed stk' y s0 s1 _ R hEq
          (hSt2.pathB X B S0 Scope hh hRead hDeser hinjK hsub rfl
            stk' hneed hstk63 y0 r sess s0 s1 coins v_a8 v_b8 v_d0 R hfiles0 hfPeer hdecOk0 hcoins
            htrusted hload_rel hcur hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1)
      · exact closure_pathC_placed_ok mmpl gh W hD2c.stageP2Over hD2c.stageP3Prev1 hD2c.stageP4Prev1
          hSt2.cliTryDecryptPqV1 X B S Scope hh hRead hinjK hsub hS stk' hneed hstk63 y r sess s0 s1
          coins v_a8 v_b8 v_d0 R hfiles0 hfPeer hdecOk hcoins htrusted hload_rel hcur hnot_match
          hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

/-! ## 4. Top-Level Placed D2(c) Poll Closure Assembly -/

/-- Given `ClosureBaseStagesCliPlacedStmt` and `D2cStagesPlacedStmt`, Block `518` satisfies
`CliDpPollOkD2cStatePlacedStmt`. -/
theorem cliDpPollOk_d2c_placed_of_cliStages [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hSt2 : ClosureBaseStagesCliPlacedStmt mmpl gh W)
    (hD2c : D2cStagesPlacedStmt mmpl gh W) :
    CliDpPollOkD2cStatePlacedStmt mmpl gh W := by
  intro X B S Scope hh hRead hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_d2c_placed (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    exact hSt2.untrustedD2c mmpl gh W X B S Scope hh hRead hDeser hinjK hsub hS stk' hneed' hstk63 y R s0
      hpc hrun hsp hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hpure.decPkOk htrusted hm_base
  | true =>
    exact closure_trusted_d2c_placed_ok mmpl gh W hSt2 hD2c X B S Scope hh hRead hDeser hinjK hsub hS
      stk' hneed' hstk63 y R s0 hpc hrun hsp hpure.stk_le_sp hpure.ro hpure.x0 hpure.x1 hpure.x2
      hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt htrusted hm_base

/-- Given `ClosureBaseStagesPlacedStmt` and `D2cStagesPlacedStmt`, Block `518` satisfies
`CliDpPollOkD2cStatePlacedStmt`. -/
theorem cliDpPollOk_d2c_placed_of_stages [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hSt2 : ClosureBaseStagesPlacedStmt mmpl gh W)
    (hD2c : D2cStagesPlacedStmt mmpl gh W) :
    CliDpPollOkD2cStatePlacedStmt mmpl gh W :=
  cliDpPollOk_d2c_placed_of_cliStages mmpl gh W hSt2.toCli hD2c

/-! ## 5. `LibsignalFrozen`-Guarded D2(c) Poll Closure Assembly (`[LibsignalFullPlacement]`) -/

set_option maxHeartbeats 1000000 in
theorem closure_trusted_d2c_frozen_placed_ok [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hSt2 : ClosureBaseStagesCliFrozenPlacedStmt mmpl gh W)
    (hD2c : D2cStagesFrozenPlacedStmt mmpl gh W)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hstk_sp : stk' ≤ s0.sp.toNat)
    (hfr0 : LibsignalFrozen lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hm_base : s0.mem ⊨ dpPollEntrySpatialPlaced stk' y s0 R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced E2E.HooksE.A0 B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsFrozen lsmpl (dpPollSpecState K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsFrozen lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  have hro0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem :=
    ⟨LibsignalCodeLoaded.of_codeLoaded hfr0.2, hfr0.1⟩
  dsimp only [dpPollEntrySpatialPlaced] at hm_base
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kid sid kbk σ
  let sp := s0.sp - 0xcd0#64
  have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using hsp
  have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
    (subStack_le_sp_of_dpPollNeed hneed hstk_sp).1
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c σ y.g.stores
    hsub hfPeer hdecOk pid sid kid kbk
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      cliPollStoresKitsAtPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer
        pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le : stageP1CallStack kit ikit ≤ dpClosSubStack B :=
    stageP1CallStack_le_subStack (A := E2E.HooksE.A0) 0#64 y.g.F Slots.scopeKit y.g.peer B
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
      preKeyMsgAt_eq_idKey_sep E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_ok s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_98, u_a0, u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  rw [← ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)] at hm_flat
  simp only [Nat.reduceMul] at hm_flat
  dsimp only [cliPollStoresKitsAtPlaced, coroUnusedP1AtPlaced] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗
    cells (y.fut + 0xe0#64) 4 ∗
    memRegion (y.fut + 0x100#64) 336 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
    cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗
    ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
    ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
    cells (y.fut + 0x428#64) 8 ∗
    cells (y.fut + 0x490#64) 4 ∗
    ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
    (sp ↦₆₄ v_sp0) ∗
    ((sp + 0x98#64) ↦₆₄ u_98) ∗
    ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
    ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
    ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
    ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
    ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x3e0#64) 368 ∗
    cells (s0.sp - 0x60#64) 12 ∗
    FromRecordCallees.lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    E2E.HooksE.A0.pool ∗
    stackAt sp (stageP1CallStack kit ikit)
  let Fr_inner : SepProp :=
    memRegion (y.fut + 0x250#64) 48 ∗
    coroUnusedP1At y.fut ∗
    closStackUnusedP1OkAt sp ∗
    memRegion y.out 48 ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1CallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    LsTokenInit
  have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
    Satisfies.mono (by
      dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
        cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
        cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced,
        cliPreKeyStoreSpecPlaced, cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
        cliKyberPreKeyStoreSpecPlaced]
      sep_frame) hm_flat
  refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
  have hwp := hSt2.stageP1Ok mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey hh hRead hDeser
    (Nat.le_trans hp1_le hsub64)
    (fun _ (h : (cliPollSessKit E2E.HooksE.A0 0#64 y.g.F Slots.scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit E2E.HooksE.A0 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390 b_4f2
    hro0 hfiles0 hpc hrun hsp_align0 rfl hx0 hx1 hx2
  refine sepWPp_bind_p1 hwp rfl ?_ ?_
  · intro sm P_m _hsteps hpanm _hsteps' hm_pan
    exact dpPollOnPanic_of_closOom_placed stk' y hpanm hm_pan
  · intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, _hro1⟩
    have hfr1 : LibsignalFrozen lsmpl s1.mem :=
      libsignalFrozen_of_keepsFrozen hfr0 hsteps01.keepsFrozen
    have htr1 : s1.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true :=
      hs1_sp ▸ sp_sub_cd0_align_std3 hsp_align0
    have hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) :=
      ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
       hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1⟩
    refine sepWPp_conseq_pre (sepConj_mono_left hent_1) ?_
    simp only [sepExists_sepConj_left]
    refine sepWPp_sepExists_left fun v_a8 =>
      sepWPp_sepExists_left fun v_b8 =>
      sepWPp_sepExists_left fun v_d0 => ?_
    have hrecomb := overP1Ok_recombine_entails_stageP2_placed stk' hneed hstk63 y s0
      coins v_a8 v_b8 v_d0 opt
    dsimp only at hrecomb
    refine sepWPp_conseq_pre hrecomb ?_
    let S0 : RunSem := { S with decryptPrekey := decPkDef X ⟨W.C, W.Q⟩ Scope }
    let y0 : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S0) :=
      ⟨y.out, y.fut, y.cx, y.g⟩
    cases opt with
    | none =>
      have hloadNone : Slots.loadRec Scope y.g.F y.g.peer.val = .ok none :=
        loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload_rel
      have hnone : ∀ r', Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r') →
          r'.currentSession = none := by
        intro r' hr'; rw [hloadNone] at hr'; cases hr'
      have hdecOk0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg :=
        hdecOk.toDecPkOk₀_of_noCurrent hnone
      have hEq : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
          S0.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins := by
        dsimp only [S0]
        rw [hS]
        exact decPkDefD2c_eq_decPkDef_of_noCurrent X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val
          y.g.me.val y.g.msg y.g.coins hnone
      exact sepWPp_pollGoal_of_decPk_eq_placed stk' y s0 s1 _ R hEq
        (hSt2.pathA X B S0 Scope hh hRead hDeser hinjK hsub rfl
          stk' hneed hstk63 y0 s0 s1 coins v_a8 v_b8 v_d0 R hfiles0 hfPeer hdecOk0 hcoins htrusted
          hload_rel hsteps01 htr1 hfr1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1)
    | some r =>
      obtain ⟨sess, hcur⟩ :=
        currentSession_some_of_cliPollSess_loadRel (A := E2E.HooksE.A0) (b := 0#64)
          (F0 := y.g.F) (peer := y.g.peer) (σ := σ) hload_rel
      have hloadSome : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
        loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload_rel
      rcases Classical.em (SessMatchesPm sess y.g.msg) with hmatch | hnot_match
      · have hdecOk0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg :=
          hdecOk.toDecPkOk₀_of_match hloadSome hcur hmatch
        have hEq : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
            S0.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins := by
          dsimp only [S0]
          rw [hS]
          exact decPkDefD2c_eq_decPkDef_of_match X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val
            y.g.me.val y.g.msg y.g.coins hloadSome hcur hmatch
        exact sepWPp_pollGoal_of_decPk_eq_placed stk' y s0 s1 _ R hEq
          (hSt2.pathB X B S0 Scope hh hRead hDeser hinjK hsub rfl
            stk' hneed hstk63 y0 r sess s0 s1 coins v_a8 v_b8 v_d0 R hfiles0 hfPeer hdecOk0 hcoins
            htrusted hload_rel hcur hsteps01 htr1 hfr1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1)
      · exact closure_pathC_frozen_placed_ok mmpl gh W hD2c.stageP2Over hD2c.stageP3Prev1 hD2c.stageP4Prev1
          hSt2.cliTryDecryptPqV1 X B S Scope hh hRead hinjK hsub hS stk' hneed hstk63 y r sess s0 s1
          coins v_a8 v_b8 v_d0 R hfiles0 hfPeer hdecOk hcoins htrusted hload_rel hcur hnot_match
          hsteps01 htr1 hfr1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

theorem cliDpPollOk_d2c_frozen_placed_of_cliStages [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hSt2 : ClosureBaseStagesCliFrozenPlacedStmt mmpl gh W)
    (hD2c : D2cStagesFrozenPlacedStmt mmpl gh W) :
    CliDpPollOkD2cStateFrozenPlacedStmt mmpl gh W := by
  intro X B S Scope hh hRead hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_d2c_frozen_placed (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    exact hSt2.untrustedD2c mmpl gh W X B S Scope hh hRead hDeser hinjK hsub hS stk' hneed' hstk63 y R s0
      hpc hrun hsp hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hpure.decPkOk htrusted hm_base
  | true =>
    exact closure_trusted_d2c_frozen_placed_ok mmpl gh W hSt2 hD2c X B S Scope hh hRead hDeser hinjK hsub hS
      stk' hneed' hstk63 y R s0 hpc hrun hsp hpure.stk_le_sp hpure.fr hpure.x0 hpure.x1 hpure.x2
      hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt htrusted hm_base

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
