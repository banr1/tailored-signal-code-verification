/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStorePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.HelpersPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.SessionBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Budget-Threaded Stage 5 Accept Path (`[LibsignalPlacement]`): `save_identity`, `memcpy`, and `promote_state`

Verifies the accepted registration-ID path (`+0x163c → +0x1768 → lr`) on `initProgPlaced W` under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli hiding
  idSaveShimSpecPlaced idSavePollSpecPlaced sessStoreShimSpecPlaced sessStorePollSpecPlaced
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs hiding initSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
  (sepWPp_weaken_pre sepWPp_pure_left sepWPp_exists_left)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas hiding
  s5_call_raw_placed s5_dealloc_ok_at_placed s5_memcpy_ok_at_placed s5_call_futDrop_placed
  s5_call_dealloc_placed s5_call_dropSS_placed s5_call_idSaveShim_placed s5_call_idSavePoll_placed
  s5_call_memcpy_placed s5_call_promoteState_placed s5_call_sessStoreShim_placed
  s5_call_sessStorePoll_placed stage5_epilogue_placed_ok stage5_err_cleanup_placed_ok
  stage5_cleanup_after_store_placed_ok stage5_store_and_cleanup_placed_ok stage5_accept_placed_ok
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced idSaveShimSpecPlaced idSavePollSpecPlaced
   sessStoreShimSpecPlaced sessStorePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced initSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
  (promoteStateEmptyBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStorePlacedBudget
  (stage5_store_and_cleanup_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailPlacedBudgetAux
  (initArgsSaveRestPlaced initArgsAtPlaced_save_split stage5ScratchSaveRestPlaced
   stage5ScratchAt_save_split_placed stage5ScratchMemcpyRestPlaced
   stage5ScratchAt_memcpy_split_placed stage5_memcpy_promote_seg_placed_ok
   stage5_save_shim_poll_placed_ok stage5_save_drop_dealloc_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm, -wp_norm] fsp_stage5_eqs

/-- Updated `SessionGhost` after `stage5_accept_placed_ok` writes `(bundle.regId, reg)`. -/
abbrev initAcceptSessionGhost (x : InitGhost) (hdr : SignalPqxdh.HandshakeHdr)
    (dataPtr : BitVec 64) (opkId reg padVal w1_kyb : BitVec 32)
    (sg : SessionGhost) (kg : TailVecGhost) : SessionGhost :=
  let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
  let pg : TailVecGhost :=
    { vec := ⟨33#64, dataPtr, (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize⟩
      tail := unpack32 opkFlag ++ unpack32 opkId ++ unpack64 0#64 ++
                unpack32 x.bundle.spkId ++ unpack32 padVal }
  let kg' : TailVecGhost := { vec := kg.vec, tail := unpack32 x.bundle.kpkId ++ unpack32 w1_kyb }
  { sg with pending := some pg, kyber := some kg',
            regIds := unpack32 x.bundle.regId ++ unpack32 reg }

/-- Promoted initiator `Session` stored in `SessionRecord` on the accepted path. -/
abbrev initAcceptSession (be : PreKeyBundleFields) (kp : IdentityKeyPair)
    (hdr : SignalPqxdh.HandshakeHdr) (reg : BitVec 32) (peer : AddrVal)
    (ss : SessionState (List (BitVec 8))) : Session (List (BitVec 8)) :=
  RecordX.sessionOfX
    (fun _ => initiatorRecordExtras ⟨kp.privateKey.bytes, reg⟩ be
      ⟨u8Vec 32 hdr.ekAPk⟩ (u8Vec 1568 hdr.kemCt))
    ⟨initParty peer, ss.setUnacknowledgedPreKeyMessage, 0, [0]⟩

/-- Continuation from `offSaveDeallocDone` (`+0x1734`): runs `memcpy` + `promote_state`, folds
`sessionRecordAt`, and hands off to `stage5_store_and_cleanup_placed_ok`. -/
theorem stage5_memcpy_and_promote_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {StoreEnv : SessStorePollGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W]
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields}
    {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey}
    {hdr : SignalPqxdh.HandshakeHdr} {pqspkPtr dataPtr : BitVec 64}
    {opkId reg padVal w1_kyb : BitVec 32} {sg : SessionGhost}
    {ss : SessionState (List (BitVec 8))} {kg : TailVecGhost}
    {w5c0 w5c8 w5d0 : BitVec 64} {BRest Extra : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPromote : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 47)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl promoteStateEmptyBudgetSpec))
    (hRodataStoreSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliSessionVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 605) ∗ P))
    (hStoreShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 605)
      (sessStoreShimSpecPlaced A lim (stk - cliInitiateFrame)))
    (hStorePoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim StoreEnv (stk - cliInitiateFrame)))
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (hDropSS : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
          M A lim)))
    (hFitStoreShim : FitsEnv M lim st (BoxAllocEnv 32))
    (hFitStorePoll : ∀ (fut : BitVec 64) (evsShim : List AllocEvent),
      BoxAllocEnv 32 evsShim →
      FitsEnv M lim (M.stepEvents evsShim st)
        (StoreEnv
          { call :=
              { call :=
                  { addrA := x.peerA
                    addr := x.peer
                    recA := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x128#64
                    g := ⟨0#64, 8#64,
                          some (initAcceptSessionGhost x hdr dataPtr opkId reg padVal w1_kyb sg kg)⟩
                    record := ⟨some (initAcceptSession be kp hdr reg x.peer.val ss)⟩ }
                fut := fut
                out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
            self := x.stores + 0xf0#64
            dir := StoresGhost.opened.sessions }))
    (hEnv : ∀ (fut : BitVec 64) (evsShim evsPoll evsDrop : List AllocEvent),
      BoxAllocEnv 32 evsShim →
      StoreEnv
        { call :=
            { call :=
                { addrA := x.peerA
                  addr := x.peer
                  recA := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x128#64
                  g := ⟨0#64, 8#64,
                        some (initAcceptSessionGhost x hdr dataPtr opkId reg padVal w1_kyb sg kg)⟩
                  record := ⟨some (initAcceptSession be kp hdr reg x.peer.val ss)⟩ }
              fut := fut
              out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
          self := x.stores + 0xf0#64
          dir := StoresGhost.opened.sessions } evsPoll →
      FreeOnlyEvs evsDrop →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents evsDrop
          (M.stepEvents (rustDeallocEvents 1568 1)
            (M.stepEvents (rustDeallocEvents 32 8)
              (M.stepEvents evsPoll (M.stepEvents evsShim st)))) = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩) (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) (hbe : bundleEOf? x.bundle = some be)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg)
    (hopkId : ∀ p, x.bundle.opk = some p → opkId = p.1)
    (hkeys : SignalPqxdh.Model.initiateKeys (modelPrims X ⟨W.C, W.Q⟩)
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)) = some (dk, hdr))
    (hinitSess : initializeInitiatorSession W.C (pqxdhSpqrSession ⟨W.C, W.Q⟩)
      ⟨(keyPairOf W.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩
      (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
      (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
      (HKDF.bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32)) = .ok ss)
    (hpqLen : ss.pqRatchetState.length ≤ 1208)
    (halice : sg.alice.bytes = (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize)
    (hkgBytes : kg.vec.bytes = 0x08#8 :: ofU8 hdr.kemCt)
    (hkemLen : (0x08#8 :: ofU8 hdr.kemCt).length = 1569)
    (hkyberKey : kyberKey (u8Vec 1568 hdr.kemCt) = 0x08#8 :: ofU8 hdr.kemCt)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32) (hkpkLen : x.bundle.kpk.length = 1568)
    (hfoldBundle : ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
      ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
      ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ⊢
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr)
    (hpc : s.pc = initEntryPlaced + offSaveDeallocDone)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hsp_align : s0.spAligned = true) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hfs0 : s0.fs.files = x.F) (hfss : s.fs.files = x.F)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 0xFFFFFFFFFFFFFFFE#64)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let sg₂ := initAcceptSessionGhost x hdr dataPtr opkId reg padVal w1_kyb sg kg
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
        dirAt A.repAlloc (x.stores + 0x28#64)
          (StoresGhost.opened.identity.saveUpd cliIo.rd x.F x.peer.val x.bundle.idKey).peers ∗
        dirAt A.repAlloc (x.stores + 0x50#64) StoresGhost.opened.signed ∗
        dirAt A.repAlloc (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
        dirAt A.repAlloc (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
        dirAt A.repAlloc (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        dirAt A.repAlloc (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        dirAt A.repAlloc (x.stores + 0x118#64) StoresGhost.opened.pub ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ FromRecordCallees.lsLogOff ∗
        A.pool lim st s ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗ initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        sessionStateAt A.repAlloc (fsp + 0x460#64) sg₂ ss.setUnacknowledgedPreKeyMessage ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
        stage5ScratchAt fsp w5c0 w5c8 w5d0 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Extra) Q Qp oom := by
  intro fsp sg₂
  conv => arg 4; rw [stage5ScratchAt_memcpy_split_placed]; simp only [sepConj_assoc]
  s5_have_eq hpPreMem :
      (memRegion (fsp + 0x1600#64) 48 ∗ memRegion (fsp + 0x1630#64) 296) ∗ ?remPreMem := by
    s5_ac_rfl
  refine sepWPp_weaken_pre
    (Entails.trans (Entails.of_eq hpPreMem)
      (sepConj_mono_left (Entails.of_eq (scratch_sret344_eq fsp)))) ?_
  have hssDecomp : sessionStateAt A.repAlloc (fsp + 0x460#64) sg₂ ss.setUnacknowledgedPreKeyMessage = _ :=
    RawByteMove.sessionStateAt_eq_inline_sep_heap A.repAlloc (fsp + 0x460#64) sg₂
      ss.setUnacknowledgedPreKeyMessage
  s5_rw_pre hssDecomp
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply sepWPp_exists_left; intro ssBytes
  apply sepWPp_pure_left; rintro ⟨hssLen, hssInl⟩
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpSeg :
      (initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        ((fsp + 0x460#64) ↦ₛ ssBytes) ∗
        ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
        memRegion (fsp + 0x1600#64) 344 ∗
        A.pool lim st s ∗
        stackAt fsp (stk - cliInitiateFrame)) ∗ ?remSeg := by
    s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.of_eq hpSeg)
    (stage5_memcpy_promote_seg_placed_ok hAlloc hPromote hstk hstk64 hssLen
      hpc hrun hsp hsp_align hinv htr hx20 hx26 ?_)
  intro sm6 hpc6 hrun6 hsp6 hvregs6 hinv6 htr6 hfs6 hx19_6 hx21_6
  have hmove2 := RawByteMove.sessionStateAt_move_bytes_twice A.repAlloc
    (fsp + 0x460#64) (fsp + 0x1600#64) (fsp + 0x140#64)
    sg₂ ss.setUnacknowledgedPreKeyMessage hssInl
  obtain ⟨hrecFold, hencLt, hinitEq⟩ := sessionRecord_promote_accept
    (A := A.repAlloc) (W := W) (X := X) (x := x) (be := be) (kp := kp) (dk := dk) (hdr := hdr)
    (opkId := opkId) (reg := reg) (sg := sg) (ss := ss)
    (dataPtr := dataPtr) (padVal := padVal) (w1 := w1_kyb) (kg := kg)
    fsp hbe htrusted hkp hreg hopkId hkeys hinitSess hpqLen halice hkgBytes hkemLen hkyberKey
  let sess := initAcceptSession be kp hdr reg x.peer.val ss
  have hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins =
      some (some (initAcceptStoresGhost x.F x.peer.val x.bundle.idKey
        (Record.encodeRecord ⟨some sess⟩), ())) := by
    rw [hS]; exact hinitEq
  refine sepWPp_weaken_pre ?_
    (stage5_store_and_cleanup_placed_ok (B := B) (kp := kp) (pqspkPtr := pqspkPtr) (opkId := opkId)
      (sg₂ := sg₂) (sess := sess) (w5c0 := w5c0) (w5c8 := w5c8) (w5d0 := w5d0) (b5b8 := 0#8)
      (Extra := Extra)
      hAlloc hRodataStoreSlot hStoreShim hStorePoll hFutDrop hDropSS
      hFitStoreShim hFitStorePoll hEnv
      hinitOk hstk hstk64 hekLen hkpkLen hencLt hans
      hpc6 hrun6 hsp6 hsp_align (hvregs6.trans hvregs) hinv6 htr6 hfs0 (hfs6.trans hfss)
      (hx19_6.trans hx19) hx21_6 hpost)
  conv => arg 1; dsimp only; simp only [sepConj_assoc]
  s5_have_eq hpM1 :
      (((fsp + 0x140#64) ↦ₛ ssBytes) ∗ ((fsp + 0x1600#64) ↦ₛ ssBytes) ∗
        ((fsp + 0x460#64) ↦ₛ ssBytes) ∗
        RawByteMove.sessionHeap A.repAlloc sg₂ ss.setUnacknowledgedPreKeyMessage) ∗ ?remM1 := by
    dsimp only [fsp] at *
    conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero]
    s5_ac_rfl
  refine Entails.trans (Entails.of_eq hpM1) (Entails.trans (sepConj_mono_left hmove2) ?_)
  rw [← scratch_sret344_eq fsp]
  s5_have_eq hpM2 :
      ((((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
        ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
        sessionStateAt A.repAlloc (fsp + 0x140#64) sg₂ ss.setUnacknowledgedPreKeyMessage) ∗
      (((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗
        ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest)) ∗ ?remM2 := by
    dsimp only [fsp] at *; s5_ac_rfl
  refine Entails.trans (Entails.of_eq hpM2)
    (Entails.trans (sepConj_mono_left (sepConj_mono hrecFold hfoldBundle)) ?_)
  dsimp only [stage5ScratchAt, stage5ScratchMemcpyRestPlaced, sg₂, initAcceptSessionGhost, sess,
    initAcceptSession, fsp] at *
  exact Entails.of_eq (by s5_ac_rfl)

/-- Accepted path from `offSave` (`+0x163c`): writes `local_registration_id = reg` and
`remote_registration_id = x.bundle.regId`, runs `save_identity` shim + poll + future drop + box
dealloc, and hands off to `stage5_memcpy_and_promote_placed_ok`. -/
theorem stage5_accept_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {StoreEnv : SessStorePollGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W]
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr dataPtr : BitVec 64} {opkId reg padVal w1_kyb : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))} {kg : TailVecGhost}
    {w5c8 w5d0 : BitVec 64} {BRest Extra : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRodataSaveSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliIdentityVtSym + 40#64) ↦₆₄ᵣ lsmpl.base 600) ∗ P))
    (hSaveShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 600)
      (idSaveShimSpecPlaced A lim (stk - cliInitiateFrame)))
    (hSavePoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 565)
      (idSavePollSpecPlaced cliIo.rd cliWrOk A lim SaveEnv (stk - cliInitiateFrame)))
    (hPromote : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 47)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl promoteStateEmptyBudgetSpec))
    (hRodataStoreSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliSessionVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 605) ∗ P))
    (hStoreShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 605)
      (sessStoreShimSpecPlaced A lim (stk - cliInitiateFrame)))
    (hStorePoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim StoreEnv (stk - cliInitiateFrame)))
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (hDropSS : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
          M A lim)))
    (hFitSaveShim : FitsEnv M lim st (BoxAllocEnv 32))
    (hFitSavePoll : ∀ (futSave : BitVec 64) (evsSaveShim : List AllocEvent),
      BoxAllocEnv 32 evsSaveShim →
      FitsEnv M lim (M.stepEvents evsSaveShim st)
        (SaveEnv x.F
          { call :=
              { call :=
                  { addrA := x.peerA
                    addr := x.peer
                    keyA := x.bundleA + 0x78#64
                    key := x.bundle.idKey }
                fut := futSave
                out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
            self := x.stores
            peers := StoresGhost.opened.identity.peers }))
    (hFitStoreShim : ∀ (futSave : BitVec 64) (evsSaveShim evsSavePoll : List AllocEvent),
      BoxAllocEnv 32 evsSaveShim →
      SaveEnv x.F
        { call :=
            { call :=
                { addrA := x.peerA
                  addr := x.peer
                  keyA := x.bundleA + 0x78#64
                  key := x.bundle.idKey }
              fut := futSave
              out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
          self := x.stores
          peers := StoresGhost.opened.identity.peers } evsSavePoll →
      FitsEnv M lim
        (M.stepEvents (rustDeallocEvents 32 8)
          (M.stepEvents evsSavePoll (M.stepEvents evsSaveShim st)))
        (BoxAllocEnv 32))
    (hFitStorePoll : ∀ (futSave futStore : BitVec 64)
        (evsSaveShim evsSavePoll evsStoreShim : List AllocEvent),
      BoxAllocEnv 32 evsSaveShim →
      SaveEnv x.F
        { call :=
            { call :=
                { addrA := x.peerA
                  addr := x.peer
                  keyA := x.bundleA + 0x78#64
                  key := x.bundle.idKey }
              fut := futSave
              out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
          self := x.stores
          peers := StoresGhost.opened.identity.peers } evsSavePoll →
      BoxAllocEnv 32 evsStoreShim →
      FitsEnv M lim
        (M.stepEvents evsStoreShim
          (M.stepEvents (rustDeallocEvents 32 8)
            (M.stepEvents evsSavePoll (M.stepEvents evsSaveShim st))))
        (StoreEnv
          { call :=
              { call :=
                  { addrA := x.peerA
                    addr := x.peer
                    recA := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x128#64
                    g := ⟨0#64, 8#64,
                          some (initAcceptSessionGhost x hdr dataPtr opkId reg padVal w1_kyb sg kg)⟩
                    record := ⟨some (initAcceptSession be kp hdr reg x.peer.val ss)⟩ }
                fut := futStore
                out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
            self := x.stores + 0xf0#64
            dir := StoresGhost.opened.sessions }))
    (hEnv : ∀ (futSave futStore : BitVec 64)
        (evsSaveShim evsSavePoll evsStoreShim evsStorePoll evsDrop : List AllocEvent),
      BoxAllocEnv 32 evsSaveShim →
      SaveEnv x.F
        { call :=
            { call :=
                { addrA := x.peerA
                  addr := x.peer
                  keyA := x.bundleA + 0x78#64
                  key := x.bundle.idKey }
              fut := futSave
              out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
          self := x.stores
          peers := StoresGhost.opened.identity.peers } evsSavePoll →
      BoxAllocEnv 32 evsStoreShim →
      StoreEnv
        { call :=
            { call :=
                { addrA := x.peerA
                  addr := x.peer
                  recA := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x128#64
                  g := ⟨0#64, 8#64,
                        some (initAcceptSessionGhost x hdr dataPtr opkId reg padVal w1_kyb sg kg)⟩
                  record := ⟨some (initAcceptSession be kp hdr reg x.peer.val ss)⟩ }
              fut := futStore
              out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
          self := x.stores + 0xf0#64
          dir := StoresGhost.opened.sessions } evsStorePoll →
      FreeOnlyEvs evsDrop →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents evsDrop
          (M.stepEvents (rustDeallocEvents 1568 1)
            (M.stepEvents (rustDeallocEvents 32 8)
              (M.stepEvents evsStorePoll
                (M.stepEvents evsStoreShim
                  (M.stepEvents (rustDeallocEvents 32 8)
                    (M.stepEvents evsSavePoll (M.stepEvents evsSaveShim st))))))) =
          M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩) (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hbe : bundleEOf? x.bundle = some be)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg)
    (hopkId : ∀ p, x.bundle.opk = some p → opkId = p.1)
    (hkeys : SignalPqxdh.Model.initiateKeys (modelPrims X ⟨W.C, W.Q⟩)
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)) = some (dk, hdr))
    (hinitSess : initializeInitiatorSession W.C (pqxdhSpqrSession ⟨W.C, W.Q⟩)
      ⟨(keyPairOf W.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩
      (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
      (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
      (HKDF.bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32)) = .ok ss)
    (hpqLen : ss.pqRatchetState.length ≤ 1208)
    (halice : sg.alice.bytes = (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize)
    (hkgBytes : kg.vec.bytes = 0x08#8 :: ofU8 hdr.kemCt)
    (hkemLen : (0x08#8 :: ofU8 hdr.kemCt).length = 1569)
    (hkyberKey : kyberKey (u8Vec 1568 hdr.kemCt) = 0x08#8 :: ofU8 hdr.kemCt)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32) (hkpkLen : x.bundle.kpk.length = 1568)
    (hfoldBundle :
      ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ⊢
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr)
    (hpc : s.pc = initEntryPlaced + offSave)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hsp_align : s0.spAligned = true) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hfs0 : s0.fs.files = x.F) (hfss : s.fs.files = x.F)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hx27 : (s.readReg64 (.gpr 27#5)).setWidth 32 = reg)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
    let basePk : PublicKey := ⟨u8Vec 32 hdr.ekAPk⟩
    let pg : TailVecGhost :=
      { vec := ⟨33#64, dataPtr, basePk.serialize⟩
        tail := unpack32 opkFlag ++ unpack32 opkId ++ unpack64 0#64 ++
                  unpack32 x.bundle.spkId ++ unpack32 padVal }
    let kg' : TailVecGhost := { vec := kg.vec, tail := unpack32 x.bundle.kpkId ++ unpack32 w1_kyb }
    let sg₁ : SessionGhost := { sg with pending := some pg, kyber := some kg' }
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
        dirAt A.repAlloc (x.stores + 0x28#64) StoresGhost.opened.identity.peers ∗
        dirAt A.repAlloc (x.stores + 0x50#64) StoresGhost.opened.signed ∗
        dirAt A.repAlloc (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
        dirAt A.repAlloc (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
        dirAt A.repAlloc (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        dirAt A.repAlloc (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        dirAt A.repAlloc (x.stores + 0x118#64) StoresGhost.opened.pub ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ FromRecordCallees.lsLogOff ∗
        A.pool lim st s ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗ initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        sessionStateAt A.repAlloc (fsp + 0x460#64) sg₁ ss.setUnacknowledgedPreKeyMessage ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
        stage5ScratchAt fsp (fsp + 0x460#64) w5c8 w5d0 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Extra) Q Qp oom := by
  intro fsp opkFlag basePk pg kg' sg₁
  let sg₂ := initAcceptSessionGhost x hdr dataPtr opkId reg padVal w1_kyb sg kg
  conv =>
    arg 4
    rw [initArgsAtPlaced_save_split, stage5ScratchAt_save_split_placed]
    simp only [sepConj_assoc]
  s5_have_eq hpPre1 :
      (((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
        ((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
        ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
        ((fsp + 0x100#64) ↦₆₄ x.bundleA) ∗
        ((fsp + 0x120#64) ↦₆₄ (x.bundleA + 0x78#64)) ∗
        dirAt A.repAlloc (x.stores + 0x28#64) StoresGhost.opened.identity.peers ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗
        FromRecordCallees.lsLogOff ∗
        sessionStateAt A.repAlloc (fsp + 0x460#64) sg₁ ss.setUnacknowledgedPreKeyMessage ∗
        ((fsp + 0x5c0#64) ↦₆₄ (fsp + 0x460#64)) ∗
        ((fsp + 0x5c8#64) ↦₆₄ w5c8) ∗
        memRegion (fsp + 0x1600#64) 48 ∗
        A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ ?remSv1 := by
    s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.of_eq hpPre1)
    (stage5_save_shim_poll_placed_ok (sg₂ := sg₂) hRodataSaveSlot hSaveShim hSavePoll
      hFitSaveShim hFitSavePoll hinitOk rfl hpc hrun hsp hsp_align hinv htr hfss hx27 ?_)
  intro sm2 futSave evsSaveShim evsSavePoll gr pAns JunkRO1 hboxSaveShim hstSavePoll hgr' hpAns
    hpc2 hrun2 hsp2 hvregs2 hinv2 htr2 hfs2 hx19_2 hx20_2
  obtain ⟨cg, hsaveOk, hpeersEq⟩ := idSave_ok_of_trusted htrusted hgr' hpAns
  have hpeersDirEq :
      idSavePeers StoresGhost.opened.identity.peers x.peer.val.name x.bundle.idKey pAns =
        (StoresGhost.opened.identity.saveUpd cliIo.rd x.F x.peer.val x.bundle.idKey).peers :=
    congrArg IdGhost.peers hpeersEq
  conv => arg 4; dsimp only; rw [hsaveOk, hpeersDirEq]; simp only [sepConj_assoc]
  s5_have_eq hpPre2 :
      (A.live futSave 32 8 ∗
        idSaveBoxAt futSave x.stores x.peerA (x.bundleA + 0x78#64) 1#8 ∗
        idSaveOutAt A.repAlloc (fsp + 0x1600#64) (.ok cg) ∗
        ((fsp + 0x5c0#64) ↦₆₄ futSave) ∗
        ((fsp + 0x5c8#64) ↦₆₄ lsρ idSaveFutVtSym) ∗
        A.pool lim (M.stepEvents evsSavePoll (M.stepEvents evsSaveShim st)) sm2 ∗
        stackAt fsp (stk - cliInitiateFrame)) ∗ ?remSv2 := by
    dsimp only [fsp] at *; s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.of_eq hpPre2)
    (stage5_save_drop_dealloc_placed_ok (B := B) hAlloc hFutDrop hstk hstk64
      hpc2 hrun2 hsp2 hsp_align hinv2 htr2 ?_)
  intro sm4 JunkRO2 hpc4 hrun4 hsp4 hvregs4 hinv4 htr4 hfs4 hx19_4 hx20_4 hx26_4
  refine sepWPp_weaken_pre ?_
    (stage5_memcpy_and_promote_placed_ok (B := B)
      (pqspkPtr := pqspkPtr) (dataPtr := dataPtr) (opkId := opkId)
      (padVal := padVal) (w1_kyb := w1_kyb) (sg := sg) (kg := kg)
      (w5c0 := futSave) (w5c8 := lsρ idSaveFutVtSym) (w5d0 := w5d0)
      (Extra := Extra ∗ JunkRO1 ∗ JunkRO2)
      hAlloc hPromote hRodataStoreSlot hStoreShim hStorePoll hFutDrop hDropSS
      (hFitStoreShim futSave evsSaveShim evsSavePoll hboxSaveShim hstSavePoll)
      (fun futStore evsStoreShim hboxStoreShim =>
        hFitStorePoll futSave futStore evsSaveShim evsSavePoll evsStoreShim
          hboxSaveShim hstSavePoll hboxStoreShim)
      (fun futStore evsStoreShim evsStorePoll evsDrop hboxStoreShim hstStorePoll hfree =>
        hEnv futSave futStore evsSaveShim evsSavePoll evsStoreShim evsStorePoll evsDrop
          hboxSaveShim hstSavePoll hboxStoreShim hstStorePoll hfree)
      hS hinitOk hstk hstk64
      hbe htrusted hkp hreg hopkId hkeys hinitSess hpqLen halice hkgBytes hkemLen hkyberKey
      hekLen hkpkLen hfoldBundle
      hpc4 hrun4 hsp4 hsp_align (hvregs4.trans (hvregs2.trans hvregs)) hinv4 htr4
      hfs0 (hfs4.trans hfs2) (hx19_4.trans (hx19_2.trans hx19))
      (hx20_4.trans (hx20_2.trans hx20)) hx26_4 hpost)
  conv => arg 1; dsimp only; simp only [sepConj_assoc]
  s5_have_eq hpScr :
      ((((fsp + 0x5c0#64) ↦₆₄ futSave) ∗
        ((fsp + 0x5c8#64) ↦₆₄ lsρ idSaveFutVtSym) ∗
        memRegion (fsp + 0x1600#64) 48) ∗ stage5ScratchSaveRestPlaced fsp w5d0) ∗ ?remScr := by
    dsimp only [fsp] at *; s5_ac_rfl
  rw [← stage5ScratchAt_save_split_placed] at hpScr
  refine Entails.trans (Entails.of_eq hpScr) ?_
  s5_have_eq hpArgs :
      ((((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
        ((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
        ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
        ((fsp + 0x100#64) ↦₆₄ x.bundleA) ∗
        ((fsp + 0x120#64) ↦₆₄ (x.bundleA + 0x78#64))) ∗
        initArgsSaveRestPlaced fsp x s0) ∗ ?remArgs := by
    dsimp only [fsp] at *; s5_ac_rfl
  rw [← initArgsAtPlaced_save_split] at hpArgs
  refine Entails.trans (Entails.of_eq hpArgs) ?_
  exact Entails.of_eq (by dsimp only [sg₂, fsp] at *; s5_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailPlacedBudget

end
