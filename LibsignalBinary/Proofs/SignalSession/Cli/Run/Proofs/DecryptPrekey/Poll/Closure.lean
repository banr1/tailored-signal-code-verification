/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Poll Top-Level Closure Assembly

Bundles the six stage contracts (`ClosureStages2Stmt` and `Ext`-generalized
`ClosureStages2ExtStmt`) and proves `cliDpPollOk_state_of_stages` and
`cliDpPollOk_state_of_stages_ext` by unpacking `dpPollSpecState.pre`, extracting the deterministic
`trusted` boolean, and dispatching to the untrusted (`false`) or trusted (`true`) branch.
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
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (closureEntry)
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust (trustCallStack)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- Trap-bridged Ext + `calleeSavedVRegs` contract for `stageP1_untrusted_ok_kit`. -/
def StageP1UntrustedTrapExtStmt : Prop :=
  ∀ {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {abs : String → Option (State → State)}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey),
    AllocHooks A abs →
    AllocContracts img.base A ext →
    TrapsOnly (trTrapProgAt img.base C abs) (tripleRatchetProgAtExt img.base ext) →
    SessionOnlyKitOkSE kit Scope encRecord ext →
    IdentityStoreKitOkIE img ikit ext →
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
      img.base &&& 0xfff#64 = 0#64 →
      ImgCallInv img s0 →
      FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
        (tripleRatchetProgAtExt img.base ext) s0 →
      s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
        Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName →
      s0.status = .Running →
      (s0.sp &&& 15#64 == 0#64) = true →
      s0.sp - 0xcd0#64 = sp →
      s0.readReg64 .x0 = outPtr →
      s0.readReg64 .x1 = coroPtr →
      s0.readReg64 .x2 = ctxPtr →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0
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
         ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
         ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
         ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
         ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
         ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
         ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
         ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
         ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
         logOff img ∗
         kit.storeAt sessStorePtr st ∗
         ikit.identityAt idStorePtr ist ∗
         protocolAddressAt A peer remoteAddrPtr ∗
         ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
         A.pool ∗
         stackAt sp (stageP1UntrustedCallStack kit ikit))
        (fun sf P_f =>
          (∃ opt : Option (SessionRecord (List (BitVec 8))),
            kit.loadRel st peer.val (.ok opt) ∧
            ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
            sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
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
                apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
                ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
                ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
                ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
                ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
                ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
                ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
                ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
                ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
                ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
                ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
                logOff img ∗
                kit.storeAt sessStorePtr st ∗
                ikit.identityAt idStorePtr
                  (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
                protocolAddressAt A peer remoteAddrPtr ∗
                ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
                A.pool ∗
                stackAt sp (stageP1UntrustedCallStack kit ikit))) ∧
          sf.sp = s0.sp ∧
          ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          img.FrozenLoaded sf ∧
          sf.symtab = img.symtab)
        (PanicOomProp s0)

/-- Bundle of the six stage contracts consumed by `cliDpPollOk_state_of_stages`:
- `stageP1Ok` & `stageP1Untrusted`: `StageP1` on `cliExterns W`,
- `stageP2Matched`, `stageP3PrevEmpty`, & `stageP4Matched`: Path B matched stages,
- `stageP2PathA`: Path A `StageP2` with `Qpan` / `PanicOomProp`. -/
structure ClosureStages2Stmt : Prop where
  stageP1Ok : StageP1OkTrapExtStmt
  stageP1Untrusted : StageP1UntrustedTrapExtStmt
  stageP2Matched : StageP2MatchedFramedCliStmt
  stageP3PrevEmpty : StageP3PrevEmptyVRegsStmt
  stageP4Matched : StageP4MatchedExtStmt
  stageP2PathA : StageP2PathAQpanCliStmt

/-- Untrusted-identity branch (`trusted =.ok false`) of `subroutine_ok_of_sepWPp_steps` for
`cliDpPollName` using `StageP1UntrustedTrapExtStmt`. -/
theorem closure_untrusted_trap_ok
    (hUntrusted : StageP1UntrustedTrapExtStmt)
    {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit E2E.HooksE.A0 img))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr cliDpPollName)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hinv0 : ImgCallInv img s0)
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
      dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
      memRegion y.cx 32 ∗
      storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗
      TokenInit img ∗
      logOff img ∗
      E2E.HooksE.A0.pool ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := tripleRatchetProgAtExt img.base (cliExterns W)
    let K := dpSlotPollKState E2E.HooksE.A0 img B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).onPanic y s0 sf ∗ R)) := by
  dsimp only
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKit E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer σ
  let pkKit := cliPollPkKit E2E.HooksE.A0 img.base y.g.F pid σ
  let spkKit := cliPollSpkKit E2E.HooksE.A0 img.base y.g.F sid σ
  let kpkKit := cliPollKpkKit E2E.HooksE.A0 img.base y.g.F kid sid kbk σ
  let sp := s0.sp - 0xcd0#64
  have hm_vt :=
    satisfies_stageP1VtablesAt
      (cliPollSess_vtablesOk (A := E2E.HooksE.A0) himg y.g.F Slots.scopeKit y.g.peer σ)
      (cliPollId_vtablesOk (A := E2E.HooksE.A0) himg y.g.F y.g.peer σ)
      hinv0.1 hm_base
  have hent_stores := storesAt_entails_cliPollStoresKitsAt (A := E2E.HooksE.A0) img.base σ
    y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hfPeer)
    (cliIdOwnInv_opened hdecOk)
    (cliIdInv_opened_peer hfPeer)
    (cliPkInv_opened hdecOk pid)
    (cliSpkInv_opened hdecOk sid)
    (cliKpkInvFull_opened hdecOk kid sid kbk)
  have hm_stores : s0.mem ⊨ stageP1VtablesAt img kit ikit ∗
      (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAt E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
        protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
        coinsInstalled img y.g.coinsP y.g.coins ∗
        TokenInit img ∗
        logOff img ∗
        E2E.HooksE.A0.pool ∗
        preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R) :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hent_stores))))) hm_vt
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1UntrustedCallStack_le_subStack (A := E2E.HooksE.A0)
    img.base y.g.F Slots.scopeKit y.g.peer B
  have hp1_64 : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1 img y.g y.fut,
      preKeyMsgAt_eq_idKey_sep E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_untrusted s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  dsimp only [cliPollStoresKitsAt, stageP1VtablesAt] at hm_flat
  rw [sessVt_eq_cliPollSessKit E2E.HooksE.A0 img y.g.F Slots.scopeKit y.g.peer σ,
      idVt_eq_cliPollIdKit E2E.HooksE.A0 img y.g.F y.g.peer σ,
      oneTimeVt_eq_cliPollPkKit E2E.HooksE.A0 img y.g.F pid σ,
      signedVt_eq_cliPollSpkKit E2E.HooksE.A0 img y.g.F sid σ,
      kyberVt_eq_cliPollKpkKit E2E.HooksE.A0 img y.g.F kid sid kbk σ] at hm_flat
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
    ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
    ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
    ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
    ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
    ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
    ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
    ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
    ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
    logOff img ∗
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
    coinsInstalled img y.g.coinsP y.g.coins ∗
    TokenInit img
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := hUntrusted
    y.g.peer y.g.msg.identityKey
    hh.allocHooks
    hh.allocContracts
    (Slots.trapsOnly_trTrap_cli img.base W)
    (cliPollSess_kitOkSE_of_deser W himg y.g.F Slots.scopeKit y.g.peer B hDeser)
    (cliPollId_kitOkIE W himg y.g.F y.g.peer B)
    hp1_64 rfl rfl
    (fun _ (h : kit.loadRel StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : ikit.trustRel StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    (cliBase_aligned himg) hinv0
    (cliPollStageP1_fsAt hh y.g.F Slots.scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  refine SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨⟨opt, hload, _, htr_evs, hent_f⟩, hspf, hcs, hvregs, _hFf, _⟩
    refine ⟨?_, hspf, calleeSavedPreserved_of_closure hcs hvregs⟩
    intro hsteps hmf
    have htr_eq : sf.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKit, cliPollIdKit, cliSessionStoreSpec,
        cliIdStoreSpecFull, cliIdentityStoreSpec] using htr_evs
    have hloadRec : Slots.loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSess_loadRel hinjK hsub hfPeer hload
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
    have hstores_back := cliPollStoresKitsAt_entails_storesAt (A := E2E.HooksE.A0)
      img.base (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    let Leftover : SepProp :=
      stageP1VtablesAt img kit ikit ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗
      TokenInit img
    have hmf_reord : sf.mem ⊨
        (apiDecResultAt E2E.HooksE.A0 y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          cliPollStoresKitsAt E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          (((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRemIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg) ∗
          logOff img ∗
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
      dsimp only [Leftover, stageP1VtablesAt, cliPollStoresKitsAt]
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
          logOff img ∗
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
    have hpost := dpPollPost_of_decResAt B S stk' y s0 sf StoresGhost.opened
      (.error (.untrustedIdentity y.g.peer.val)) Leftover hh hsteps htr_eq hout
    exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · intro sf P_f hoom _hsteps hmf
    rw [← sepConj_assoc] at hmf
    exact dpPollOnPanic_of_closOom stk' y hoom hmf

/-- given `ClosureStages2Stmt`, `cliDpPollName` satisfies
`CliDpPollOkStateStmt`. -/
theorem cliDpPollOk_state_of_stages (hSt : ClosureStages2Stmt) : CliDpPollOkStateStmt := by
  intro img W X B S Scope himg hh _hRead hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack (img := img) (W := W) (X := X) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatial] at hm_base
    exact closure_untrusted_trap_ok hSt.stageP1Untrusted W X B S Scope himg hh hDeser hinjK hsub hS
      stk' hneed' hstk63 y R s0 hpc hrun hsp
      hpure.inv hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.decPkOk
      htrusted hm_base
  | true =>
    exact closure_trusted_ok hSt.stageP1Ok hSt.stageP2Matched hSt.stageP3PrevEmpty
      hSt.stageP4Matched hSt.stageP2PathA W X B S Scope himg hh hDeser hinjK hsub hS
      stk' hneed' hstk63 y R s0 hpc hrun hsp hpure.stk_le_sp
      hpure.inv hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.decPkOk
      hpure.coins_lt htrusted hm_base

/-! ## `Ext`-Generalized Top-Level Poll Closure Assembly (`ClosureStages2ExtStmt` → `CliDpPollOkStateExtStmt`) -/

/-- New-session (`opt = none`) continuation contract from `+0x0868#64` to `s0.readReg64.x30` on
`tripleRatchetProgAtExt img.base (cliExternsWith ext)`. -/
def ClosurePathAContExtStmt : Prop :=
  ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    CliExternsOk P A ext →
    Obj.Loads libsignalSessionImage img →
    RunHooksExt img A (cliExternsWith ext) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit A img) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r', Scope r' → Slots.scopeIn r') →
    S.decryptPrekey = decPkDef X P Scope →
    ∀ (stk' : Nat), dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
    ∀ (y : DpPollGhostState (dpSlotPollKState A img B S))
      (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp),
      s0.fs.files = y.g.F →
      Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
      DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
      y.g.coins.length < 2 ^ 63 →
      StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
        y.g.msg.identityKey = .ok true →
      (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer
        (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok none) →
      Steps (tripleRatchetProgAtExt img.base (cliExternsWith ext)) s0 s1 →
      s1.trace = s0.trace → ImgCallInv img s1 →
      s1.sp = s0.sp - 0xcd0#64 → dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat →
      s1.pc = closureEntry img (cliExternsWith ext) + 0x0868#64 →
      s1.status = .Running → (s1.sp &&& 15#64 == 0#64) = true →
      StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) →
      let prog := tripleRatchetProgAtExt img.base (cliExternsWith ext)
      let K := dpSlotPollKState A img B S
      let sp := s0.sp - 0xcd0#64
      let σ := cliKitStk B
      let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
      let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
      SepWPp prog (s0.readReg64 .x30) s1
        (stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
           (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
           (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt Slots.scopeKit A y.fut none ∗
         preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt A y.g.peer y.g.peerA ∗
         protocolAddressAt A y.g.me y.g.meA ∗
         coinsInstalled img y.g.coinsP y.g.coins ∗
         storesAt A y.g.stores StoresGhost.opened ∗
         TokenInit img ∗ logOff img ∗ stackAt sp (dpClosSubStack B) ∗
         memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
         memRegion y.cx 32 ∗ stageP1VtablesAt img kit ikit)
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).onPanic y s0 sf ∗ R))

/-- Matched-session (`opt = some r`) continuation contract from `+0x0868#64` to `s0.readReg64.x30` on
`tripleRatchetProgAtExt img.base (cliExternsWith ext)`. -/
def ClosurePathBContExtStmt : Prop :=
  ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    CliExternsOk P A ext →
    Obj.Loads libsignalSessionImage img →
    RunHooksExt img A (cliExternsWith ext) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit A img) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r', Scope r' → Slots.scopeIn r') →
    S.decryptPrekey = decPkDef X P Scope →
    ∀ (stk' : Nat), dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
    ∀ (y : DpPollGhostState (dpSlotPollKState A img B S))
      (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
      (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp),
      s0.fs.files = y.g.F →
      Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
      DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
      y.g.coins.length < 2 ^ 63 →
      StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
        y.g.msg.identityKey = .ok true →
      (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer
        (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)) →
      r.currentSession = some sess →
      Steps (tripleRatchetProgAtExt img.base (cliExternsWith ext)) s0 s1 →
      s1.trace = s0.trace → ImgCallInv img s1 →
      s1.sp = s0.sp - 0xcd0#64 → dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat →
      s1.pc = closureEntry img (cliExternsWith ext) + 0x0868#64 →
      s1.status = .Running → (s1.sp &&& 15#64 == 0#64) = true →
      StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) →
      let prog := tripleRatchetProgAtExt img.base (cliExternsWith ext)
      let K := dpSlotPollKState A img B S
      let sp := s0.sp - 0xcd0#64
      let σ := cliKitStk B
      let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
      let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
      SepWPp prog (s0.readReg64 .x30) s1
        (stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
           (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
           (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt Slots.scopeKit A y.fut (some r) ∗
         preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt A y.g.peer y.g.peerA ∗
         protocolAddressAt A y.g.me y.g.meA ∗
         coinsInstalled img y.g.coinsP y.g.coins ∗
         storesAt A y.g.stores StoresGhost.opened ∗
         TokenInit img ∗ logOff img ∗ stackAt sp (dpClosSubStack B) ∗
         memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
         memRegion y.cx 32 ∗ stageP1VtablesAt img kit ikit)
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).onPanic y s0 sf ∗ R))

/-- `Ext`-generalized stage bundle consumed by `cliDpPollOk_state_of_stages_ext`. -/
structure ClosureStages2ExtStmt : Prop where
  stageP1Ok : StageP1OkXExtStmt
  stageP1Untrusted : StageP1UntrustedXExtStmt
  sessKitOk : PollSessKitOkExtStmt
  idKitOk : PollIdKitOkExtStmt
  pathA : ClosurePathAContExtStmt
  pathB : ClosurePathBContExtStmt

private theorem p1Ok_post_eq_stageP2PostP1At_ext {img : Obj.Image} {A : RustAlloc}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
    let pkKit := cliPollPkKit A img.base y.g.F pid σ
    let spkKit := cliPollSpkKit A img.base y.g.F sid σ
    let kpkKit := cliPollKpkKit A img.base y.g.F kid sid kbk σ
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt Scope A y.fut opt ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ cells (y.fut + 0x398#64) 2 ∗
      ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗ (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ A.pool) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗ memRegion y.out 48) =
    stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Scope A y.fut opt := by
  dsimp only [stageP2PostP1At]
  rw [← sessVt_eq_cliPollSessKit A img y.g.F Slots.scopeKit y.g.peer (cliKitStk B),
      ← idVt_eq_cliPollIdKit A img y.g.F y.g.peer (cliKitStk B),
      ← oneTimeVt_eq_cliPollPkKit A img y.g.F (pmPreKeyId y.g.msg) (cliKitStk B),
      ← signedVt_eq_cliPollSpkKit A img y.g.F y.g.msg.signedPreKeyId (cliKitStk B),
      ← kyberVt_eq_cliPollKpkKit A img y.g.F (pmKyberId y.g.msg)
          y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B)]
  sep_frame

private theorem p1Ok_recombine_entails_stageP2_ext {img : Obj.Image} {A : RustAlloc}
    {B : RunBudgets} {S : RunSem}
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
    let pkKit := cliPollPkKit A img.base y.g.F pid σ
    let spkKit := cliPollSpkKit A img.base y.g.F sid σ
    let kpkKit := cliPollKpkKit A img.base y.g.F kid sid kbk σ
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt Slots.scopeKit A y.fut opt ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ cells (y.fut + 0x398#64) 2 ∗
      ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗ (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
      ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
      ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
      ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
      ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
      ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
      ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
      ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
      ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
      ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
      logOff img ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores
        (ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey
          .receiving (.ok true)) ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      A.pool ∗ stackAt sp (stageP1CallStack kit ikit)) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗ memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗ TokenInit img) ⊢
    stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Slots.scopeKit A y.fut opt ∗
    preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A y.g.peer y.g.peerA ∗
    protocolAddressAt A y.g.me y.g.meA ∗
    coinsInstalled img y.g.coinsP y.g.coins ∗
    storesAt A y.g.stores StoresGhost.opened ∗
    TokenInit img ∗ logOff img ∗ stackAt sp (dpClosSubStack B) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗ stageP1VtablesAt img kit ikit := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1CallStack_le_subStack (A := A)
    img.base y.g.F Slots.scopeKit y.g.peer B
  have hstores_back := cliPollStoresKitsAt_entails_storesAt (A := A)
    img.base (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
  have hp1_eq := p1Ok_post_eq_stageP2PostP1At_ext (Scope := Slots.scopeKit) y s0 rngPtr v_a8 v_b8 v_d0 opt
  dsimp only at hp1_eq
  have hp1_ent := Entails.of_eq hp1_eq
  have hpm_ent := Entails.of_eq (preKeyMsgAt_eq_idKey_sep A y.g.msgG y.g.msgA y.g.msg).symm
  have hstk_ent := Entails.of_eq
    (stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64).symm
  have h4 := sepConj_mono hp1_ent (sepConj_mono hstores_back (sepConj_mono hpm_ent hstk_ent))
  let Pass : SepProp :=
    protocolAddressAt A y.g.peer y.g.peerA ∗ protocolAddressAt A y.g.me y.g.meA ∗
    coinsInstalled img y.g.coinsP y.g.coins ∗ TokenInit img ∗ logOff img ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗ stageP1VtablesAt img kit ikit
  refine Entails.trans ?_ (Entails.trans (sepConj_mono_left h4 : _ ∗ Pass ⊢ _ ∗ Pass) ?_)
  · dsimp only [cliPollId_trustUpdate_eq, cliPollStoresKitsAt, stageP1VtablesAt, Pass,
      sp, σ, pid, sid, kid, kbk, kit, ikit]
    sep_frame
  · dsimp only [Pass, sp, σ, kit, ikit]
    sep_frame

set_option maxHeartbeats 800000 in
private theorem closure_trusted_x_ext_ok
    (hP1 : StageP1OkXExtStmt)
    (hSessKit : PollSessKitOkExtStmt)
    (hIdKit : PollIdKitOkExtStmt)
    (hPathA : ClosurePathAContExtStmt)
    (hPathB : ClosurePathBContExtStmt)
    {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit A img))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDef X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr cliDpPollName)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hstk_sp : stk' ≤ s0.sp.toNat) (hinv0 : ImgCallInv img s0)
    (hx0 : s0.readReg64 .x0 = y.out) (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx) (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hm_base : s0.mem ⊨ dpPollEntrySpatialExt A img stk' y s0 R) :
    let prog := tripleRatchetProgAtExt img.base (cliExternsWith ext)
    let K := dpSlotPollKState A img B S
    ∃ P0 Fr : SepProp, (s0.mem ⊨ P0 ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P0
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).onPanic y s0 sf ∗ R)) := by
  dsimp only
  dsimp only [dpPollEntrySpatialExt] at hm_base
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
  let pkKit := cliPollPkKit A img.base y.g.F pid σ
  let spkKit := cliPollSpkKit A img.base y.g.F sid σ
  let kpkKit := cliPollKpkKit A img.base y.g.F kid sid kbk σ
  let sp := s0.sp - 0xcd0#64
  have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using hsp
  have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
    (subStack_le_sp_of_dpPollNeed hneed hstk_sp).1
  have hm_vt :=
    satisfies_stageP1VtablesAt
      (cliPollSess_vtablesOk (A := A) himg y.g.F Slots.scopeKit y.g.peer σ)
      (cliPollId_vtablesOk (A := A) himg y.g.F y.g.peer σ)
      hinv0.1 hm_base
  have hent_stores := storesAt_entails_cliPollStoresKitsAt (A := A) img.base σ
    y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hfPeer)
    (cliIdOwnInv_opened hdecOk)
    (cliIdInv_opened_peer hfPeer)
    (cliPkInv_opened hdecOk pid)
    (cliSpkInv_opened hdecOk sid)
    (cliKpkInvFull_opened hdecOk kid sid kbk)
  have hm_stores : s0.mem ⊨ stageP1VtablesAt img kit ikit ∗
      (memRegion y.out 48 ∗ dpFutStartAt y.fut (dpSlotArgs img y.g) ∗ memRegion y.cx 32 ∗
        cliPollStoresKitsAt A img.base y.g.F Slots.scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A y.g.peer y.g.peerA ∗ protocolAddressAt A y.g.me y.g.meA ∗
        coinsInstalled img y.g.coinsP y.g.coins ∗ TokenInit img ∗ logOff img ∗ A.pool ∗
        preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗ stackAt s0.sp stk' ∗ R) :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hent_stores))))) hm_vt
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1CallStack_le_subStack (A := A)
    img.base y.g.F Slots.scopeKit y.g.peer B
  have hp1_64 : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1 img y.g y.fut,
      preKeyMsgAt_eq_idKey_sep A y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_ok s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_98, u_a0, u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  rw [← ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)] at hm_flat
  simp only [Nat.reduceMul] at hm_flat
  dsimp only [cliPollStoresKitsAt, stageP1VtablesAt] at hm_flat
  rw [sessVt_eq_cliPollSessKit A img y.g.F Slots.scopeKit y.g.peer σ,
      idVt_eq_cliPollIdKit A img y.g.F y.g.peer σ,
      oneTimeVt_eq_cliPollPkKit A img y.g.F pid σ,
      signedVt_eq_cliPollSpkKit A img y.g.F sid σ,
      kyberVt_eq_cliPollKpkKit A img y.g.F kid sid kbk σ] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗ cells (y.fut + 0xe0#64) 4 ∗
    memRegion (y.fut + 0x100#64) 336 ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
    cells (y.fut + 0x2c8#64) 25 ∗ ((y.fut + 0x390#64) ↦₈ b_390) ∗
    ((y.fut + 0x398#64) ↦₆₄ u_398) ∗ ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
    cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗
    ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ (sp ↦₆₄ v_sp0) ∗
    ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
    ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
    cells (s0.sp - 0x60#64) 12 ∗
    ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
    ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
    ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
    ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
    ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
    ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
    ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
    ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
    logOff img ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt A y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    A.pool ∗ stackAt sp (stageP1CallStack kit ikit)
  let Fr_inner : SepProp :=
    memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut ∗
    closStackUnusedP1OkAt sp ∗ memRegion y.out 48 ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1CallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt A y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalled img y.g.coinsP y.g.coins ∗ TokenInit img
  have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner]; sep_frame) hm_flat
  refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
  have hwp := hP1
    y.g.peer y.g.msg.identityKey hh.alloc hh.allocHooks
    (hSessKit P A ext B hOk himg hh hRead hDeser y.g.F y.g.peer)
    (hIdKit P A ext B hOk himg hh hRead y.g.F y.g.peer)
    hp1_64
    (by dsimp [kit, σ, loadCallStack, cliPollSessKit, cliSessionStoreSpec, cliKitStk,
          SessKit.loadPollNeed]; omega)
    (by dsimp [ikit, σ, trustCallStack, cliPollIdKit, cliIdStoreSpecFull, cliIdentityStoreSpec,
          cliKitStk, IdKit.trustPollNeed]; omega)
    rfl rfl
    (fun _ (h : kit.loadRel StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : ikit.trustRel StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2
    (cliBase_aligned himg) hinv0
    (cliPollStageP1_fsAt_ext hh.fs y.g.F Slots.scopeKit y.g.peer B hfiles0)
    hpc hrun hsp_align0 rfl hx0 hx1 hx2
  refine sepWPp_bind_p1 hwp rfl ?_ ?_
  · intro sm P_m _hsteps hpanm _hsteps' hm_pan
    exact dpPollOnPanic_of_closOom stk' y hpanm hm_pan
  · intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, hfz1, hsym1⟩
    have htr1 : s1.trace = s0.trace := stageP1Ok_trace_eq htr_evs
    have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true :=
      hs1_sp ▸ sp_sub_cd0_align_std3 hsp_align0
    have hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) :=
      ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
       hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1⟩
    refine sepWPp_conseq_pre (sepConj_mono_left hent_1) ?_
    simp only [sepExists_sepConj_left]
    refine sepWPp_sepExists_left fun v_a8 =>
      sepWPp_sepExists_left fun v_b8 =>
      sepWPp_sepExists_left fun v_d0 => ?_
    have hrecomb := p1Ok_recombine_entails_stageP2_ext stk' hneed hstk63 y s0 coins v_a8 v_b8 v_d0 opt
    dsimp only at hrecomb
    refine sepWPp_conseq_pre hrecomb ?_
    cases opt with
    | none =>
      exact hPathA P A ext X B S Scope hOk himg hh hRead hDeser hinjK hsub hS
        stk' hneed hstk63 y s0 s1 coins v_a8 v_b8 v_d0 R hfiles0 hfPeer hdecOk hcoins
        htrusted hload_rel hsteps01 htr1 ⟨hfz1, hsym1⟩ hs1_sp hsp_sub hpc1 hrun1
        hsp_align1 hregs1
    | some r =>
      obtain ⟨sess, hcur⟩ := currentSession_some_of_cliPollSess_loadRel hload_rel
      exact hPathB P A ext X B S Scope hOk himg hh hRead hDeser hinjK hsub hS
        stk' hneed hstk63 y r sess s0 s1 coins v_a8 v_b8 v_d0 R hfiles0 hfPeer hdecOk hcoins
        htrusted hload_rel hcur hsteps01 htr1 ⟨hfz1, hsym1⟩ hs1_sp hsp_sub hpc1 hrun1
        hsp_align1 hregs1

/-- `Ext`-generalized Layer T assembly: given `ClosureStages2ExtStmt`,
`cliDpPollName` satisfies `CliDpPollOkStateExtStmt`. -/
theorem cliDpPollOk_state_of_stages_ext (hSt : ClosureStages2ExtStmt) : CliDpPollOkStateExtStmt := by
  intro img P A ext X B S Scope hOk himg hh hRead hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_ext (img := img) (P := P) (A := A) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialExt] at hm_base
    exact closure_untrusted_x_ext_ok hSt.stageP1Untrusted hSt.sessKitOk hSt.idKitOk
      P A ext X B S Scope hOk himg hh hRead hDeser hinjK hsub hS
      stk' hneed' hstk63 y R s0 hpc hrun hsp
      hpure.inv hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.decPkOk
      htrusted hm_base
  | true =>
    exact closure_trusted_x_ext_ok hSt.stageP1Ok hSt.sessKitOk hSt.idKitOk hSt.pathA hSt.pathB
      P A ext X B S Scope hOk himg hh hRead hDeser hinjK hsub hS
      stk' hneed' hstk63 y R s0 hpc hrun hsp hpure.stk_le_sp
      hpure.inv hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.decPkOk
      hpure.coins_lt htrusted hm_base

end CryptoVerification.SignalSession.Cli.RunProofs.Poll

