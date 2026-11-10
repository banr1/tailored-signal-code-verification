/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.Closure
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Poll Top-Level Closure Assembly

Bundles the nine `[LibsignalPlacement]` stage contracts (`ClosureStages2PlacedStmt`) and proves
`cliDpPollOk_state_of_stages_placed : ClosureStages2PlacedStmt -> CliDpPollOkStatePlacedStmt` on
Block `518` (`dpPollEntryPlaced`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Coins.Placed
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  CliGhostHooks cliGhostExterns cliGhostExterns_other
)

set_option linter.unusedSimpArgs false in
private theorem withPanics_cliGhostExterns_eq (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      cliGhostExterns gh (cliExternsPlaced mmpl W) := by
  funext n
  by_cases hp : Rust.isPanicSymbol n = true
  · have hother : cliGhostExterns gh (cliExternsPlaced mmpl W) n = cliExternsPlaced mmpl W n :=
      cliGhostExterns_other gh (cliExternsPlaced mmpl W)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsReadFileSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsReadStdinSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemsetSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemcpySym] at hp)
    unfold Rust.withPanics
    rw [hother]
    unfold cliExternsPlaced isCliPanicSymbolPlaced
    simp [hp]
  · simp [Rust.withPanics, hp]

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- Relocatable `[LibsignalPlacement]` CLI-specialized Stage P1 untrusted-identity contract
(`dpPollEntryPlaced → s0.readReg64.x30`) for `cliPollSessKitPlaced` and `cliPollIdKitPlaced`. -/
def StageP1UntrustedTrapPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets) (F0 : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced E2E.HooksE.A0 F0 Slots.scopeKit peer σ
    let ikit := cliPollIdKitPlaced E2E.HooksE.A0 F0 peer σ
    ∀ (st : kit.StoreState) (ist : ikit.IdState),
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) →
    stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 →
    kit.addrOk peer.val →
    ikit.addrOk peer.val →
    (∀ ans, kit.loadRel st peer.val ans → ans.isOk = true) →
    (∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false) →
    ∀ (s0 : State)
      (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
       sessStorePtr idStorePtr
       preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
       kyberStorePtr kyberStoreVt rngPtr
       v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
      (b_390 : BitVec 8),
      StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem →
      FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
        (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 →
      s0.pc = dpPollEntryPlaced →
      s0.status = .Running →
      (s0.sp &&& 15#64 == 0#64) = true →
      s0.sp - 0xcd0#64 = sp →
      s0.readReg64 .x0 = outPtr →
      s0.readReg64 .x1 = coroPtr →
      s0.readReg64 .x2 = ctxPtr →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s0
        (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
           sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
           preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
           kyberStorePtr kyberStoreVt rngPtr ∗
         cells (coroPtr + 0x70#64) 14 ∗
         cells (coroPtr + 0xe0#64) 4 ∗
         memRegion (coroPtr + 0x100#64) 336 ∗
         cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
         cells (coroPtr + 0x2c8#64) 25 ∗
         ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
         ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
         (sp ↦₆₄ v_sp0) ∗
         ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
         ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
         ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
         ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (sp + 0xd8#64) 348 ∗
         memRegion (sp + 0x370#64) 36 ∗
         memRegion (sp + 0x3e0#64) 368 ∗
         cells (sp + 0xa90#64) 6 ∗
         cells (s0.sp - 0x60#64) 12 ∗
         memRegion outPtr 48 ∗
         FromRecordCallees.lsLogOff ∗
         kit.storeAt sessStorePtr st ∗
         ikit.identityAt idStorePtr ist ∗
         protocolAddressAt E2E.HooksE.A0 peer remoteAddrPtr ∗
         ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
         E2E.HooksE.A0.pool ∗
         stackAt sp (stageP1UntrustedCallStack kit ikit))
        (fun sf P_f =>
          (∃ opt : Option (SessionRecord (List (BitVec 8))),
            kit.loadRel st peer.val (.ok opt) ∧
            ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
            sf.trace = s0.trace ++ kit.loadEvs E2E.Record.encodeRecord peer.val (.ok opt) ++
              ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
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
                memRegion (coroPtr + 0xe0#64) 368 ∗
                cells (coroPtr + 0x250#64) 6 ∗
                ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
                processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                  spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
                ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
                cells (coroPtr + 0x398#64) 2 ∗
                (sp ↦₆₄ 0#64) ∗
                ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
                ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
                ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
                ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
                ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
                memRegion (sp + 0xd8#64) 348 ∗
                memRegion (sp + 0x370#64) 36 ∗
                memRegion (sp + 0x3e0#64) 368 ∗
                cells (sp + 0xa90#64) 6 ∗
                decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
                apiDecResultAt E2E.HooksE.A0 outPtr (.error (.untrustedIdentity peer.val)) ∗
                FromRecordCallees.lsLogOff ∗
                kit.storeAt sessStorePtr st ∗
                ikit.identityAt idStorePtr
                  (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
                protocolAddressAt E2E.HooksE.A0 peer remoteAddrPtr ∗
                ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
                E2E.HooksE.A0.pool ∗
                stackAt sp (stageP1UntrustedCallStack kit ikit))) ∧
          sf.sp = s0.sp ∧
          ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
        (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0)

/-- Relocatable `[LibsignalPlacement]` bundle of the stage contracts consumed by
`cliDpPollOk_state_of_stages_placed`:
- `stageP1Ok` & `stageP1Untrusted`: Stage P1 on `cliGhostExterns gh (cliExternsPlaced mmpl W)`,
- `stageP2Matched`, `stageP3PrevEmpty`, & `stageP4Matched`: Path B matched stages,
- `stageP2PathA`, `stageP3Gen`, & `stageP4PathA`: Path A new-session stages,
- `tryDecryptPqV1`: `try_decrypt_prekey_message_pq_v1` callee contract on Block `518`. -/
structure ClosureStages2PlacedStmt [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) : Prop where
  stageP1Ok : StageP1OkTrapPlacedStmt
  stageP1Untrusted : StageP1UntrustedTrapPlacedStmt
  stageP2Matched : StageP2MatchedFramedCliPlacedStmt
  stageP3PrevEmpty : StageP3PrevEmptyVRegsPlacedStmt
  stageP4Matched : StageP4MatchedPlacedStmt
  stageP2PathA : StageP2PathAQpanCliPlacedStmt mmpl gh W
  stageP3Gen : StageP3GenStepsVRegsPlacedStmt
  stageP4PathA : StageP4PathAPlacedStmt
  tryDecryptPqV1 : CliTryDecryptPqV1PlacedStmt mmpl gh W

/-- Untrusted-identity branch (`trusted =.ok false`) of `subroutine_ok_of_sepWPp_steps` for
Block `518` under `[LibsignalPlacement]` using `StageP1UntrustedTrapPlacedStmt`. -/
theorem closure_untrusted_trap_placed_ok [LibsignalPlacement]
    (hUntrusted : StageP1UntrustedTrapPlacedStmt)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hro0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
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
      R) :
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
  have hent_stores := storesAt_entails_cliPollStoresKitsAtPlaced (A := E2E.HooksE.A0)
    (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ
    y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hfPeer)
    (cliIdOwnInv_opened hdecOk)
    (cliIdInv_opened_peer hfPeer)
    (cliPkInv_opened hdecOk pid)
    (cliSpkInv_opened hdecOk sid)
    (cliKpkInvFull_opened hdecOk kid sid kbk)
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
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1UntrustedCallStack_le_subStack (A := E2E.HooksE.A0)
    0#64 y.g.F Slots.scopeKit y.g.peer B
  have hp1_64 : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
      preKeyMsgAt_eq_idKey_sep E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_untrusted s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  dsimp only [cliPollStoresKitsAtPlaced] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗
    cells (y.fut + 0xe0#64) 4 ∗
    memRegion (y.fut + 0x100#64) 336 ∗
    cells (y.fut + 0x250#64) 6 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
    cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗
    ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
    ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
    (sp ↦₆₄ v_sp0) ∗
    ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
    ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
    ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
    ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x370#64) 36 ∗
    memRegion (sp + 0x3e0#64) 368 ∗
    cells (sp + 0xa90#64) 6 ∗
    cells (s0.sp - 0x60#64) 12 ∗
    memRegion y.out 48 ∗
    FromRecordCallees.lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    E2E.HooksE.A0.pool ∗
    stackAt sp (stageP1UntrustedCallStack kit ikit)
  let Fr_inner : SepProp :=
    cells (y.fut + 0x428#64) 8 ∗
    cells (y.fut + 0x490#64) 4 ∗
    ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
    coroUnusedP1At y.fut ∗
    closStackUnusedUntrustedAt sp ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
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
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, cliPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
      cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := hUntrusted mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey
    StoresGhost.opened.sessions StoresGhost.opened.identity
    hh hReadFile hDeser hp1_64 rfl rfl
    (fun _ (h : (cliPollSessKit E2E.HooksE.A0 0#64 y.g.F Slots.scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit E2E.HooksE.A0 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    hro0
    (cliPollStageP1_fsAt_placed hh y.g.F Slots.scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  refine SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨⟨opt, hload, _, htr_evs, hent_f⟩, hspf, hcs, hvregs, _⟩
    refine ⟨?_, hspf, closureCalleeSaved_toCalleeSavedPreserved hcs hvregs⟩
    intro hsteps hmf
    have htr_eq : sf.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hloadRec : Slots.loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload
    have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none := by
      rw [hS]
      exact decPkDef_of_trust_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadRec (Or.inr htrusted)
    have hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) s0.trace sf.trace :=
      slotOutTr_of_err StoresGhost.opened s0.trace sf.trace nofun nofun hans
    have hmf1 := Satisfies.mono (sepConj_mono_left hent_f) hmf
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hmf1
    rcases hmf1 with ⟨v_a8, v_b8, v_d0, hmf2⟩
    have hcoro := coro_of_p1_untrusted_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins b_4f2
    have hstk3280 := clos_stack_3280_of_p1_untrusted s0.sp s0
      0#64 v_a8 (y.fut + 0x390#64) v_b8 y.cx y.out v_d0
    have hres := apiDecResultAt_untrusted_entails_decResAt E2E.HooksE.A0 y.out y.g.peer.val
    have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := E2E.HooksE.A0)
      (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    let Leftover : SepProp :=
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit
    have hmf_reord : sf.mem ⊨
        (apiDecResultAt E2E.HooksE.A0 y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          cliPollStoresKitsAtPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          (((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRemIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg) ∗
          FromRecordCallees.lsLogOff ∗
          E2E.HooksE.A0.pool ∗
          Leftover ∗
          (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            memRegion (y.fut + 0xe0#64) 368 ∗
            cells (y.fut + 0x250#64) 6 ∗
            ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
              (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
            ((y.fut + 0x390#64) ↦₈ 1#8) ∗
            cells (y.fut + 0x398#64) 2 ∗
            cells (y.fut + 0x428#64) 8 ∗
            cells (y.fut + 0x490#64) 4 ∗
            ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
            coroUnusedP1At y.fut) ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
                (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit)) ∗
            ((sp ↦₆₄ 0#64) ∗
              ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
              ((sp + 0xc8#64) ↦₆₄ y.out) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗
              memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗
              decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              closStackUnusedUntrustedAt sp))) ∗ R := by
      have htrust_id : ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val
          y.g.msg.identityKey .receiving (.ok false) = StoresGhost.opened.identity := rfl
      rw [htrust_id] at hmf2
      dsimp only [Fr_inner] at hmf2
      refine Satisfies.mono ?_ hmf2
      dsimp only [Leftover, cliPollStoresKitsAtPlaced]
      sep_frame
    rw [← preKeyMsgAt_eq_idKey_sep E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg,
        ← stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
        show sp + 0xcd0#64 = s0.sp from sp_frame_sub_add s0.sp] at hmf_reord
    have hmf_folded : sf.mem ⊨
        (decResAt E2E.HooksE.A0 y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          E2E.HooksE.A0.pool ∗
          Leftover ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion sp 3280)) ∗ R :=
      Satisfies.mono (sepConj_mono_left
        (sepConj_mono hres
          (sepConj_mono hstores_back
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono hcoro
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk3280)))))))))))))
        hmf_reord
    dsimp only [sp] at hmf_folded
    rw [← stackAt_poll_entry_split s0.sp B stk' hneed hstk63] at hmf_folded
    have hpost := dpPollPost_of_decResAt_placed B S stk' y s0 sf StoresGhost.opened
      (.error (.untrustedIdentity y.g.peer.val)) Leftover hh hsteps htr_eq hout
    exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · intro sf P_f hoom _hsteps hmf
    rw [← sepConj_assoc] at hmf
    exact dpPollOnPanic_of_closOom_placed stk' y hoom hmf

/-- given `ClosureStages2PlacedStmt`, Block `518`
(`dpPollEntryPlaced = lsmpl.base 518`) satisfies `CliDpPollOkStatePlacedStmt`. -/
theorem cliDpPollOk_state_of_stages_placed [LibsignalPlacement]
    (hSt : ∀ mmpl gh W, ClosureStages2PlacedStmt mmpl gh W) : CliDpPollOkStatePlacedStmt := by
  intro mmpl gh W X B S Scope hh hReadFile hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  let st := hSt mmpl gh W
  have hProg : DecryptPrekeyHelpers.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
    dsimp only [DecryptPrekeyHelpers.dpPollProgPlaced, dpPollProgPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP1ProgPlaced]
    rw [withPanics_cliGhostExterns_eq mmpl gh W]
  have hEntry : DecryptPrekeyHelpers.dpPollEntryPlaced = dpPollEntryPlaced := rfl
  rw [hProg] at hReadFile hDeser ⊢
  rw [hEntry]
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_placed (W := W) (X := X) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    exact closure_untrusted_trap_placed_ok st.stageP1Untrusted mmpl gh W X B S Scope hh hReadFile hDeser
      hinjK hsub hS stk' hneed' hstk63 y R s0 hpc hrun hsp
      hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.decPkOk
      htrusted hm_base
  | true =>
    exact closure_trusted_placed_ok mmpl gh W st.stageP1Ok st.stageP2Matched st.stageP3PrevEmpty
      st.stageP4Matched st.stageP2PathA st.stageP3Gen st.stageP4PathA st.tryDecryptPqV1
      X B S Scope hh hReadFile hDeser hinjK hsub hS
      stk' hneed' hstk63 y R s0 hpc hrun hsp hpure.stk_le_sp
      hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.decPkOk
      hpure.coins_lt htrusted hm_base

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
