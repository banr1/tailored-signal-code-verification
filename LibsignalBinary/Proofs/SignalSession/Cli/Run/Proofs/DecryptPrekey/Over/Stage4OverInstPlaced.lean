/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4

/-!
# Relocatable CLI Poll Stage P4 Over-Path (`Path C`) Instantiation

Proves `cliPollSess_prev1KitPlacedOk` and instantiates `Poll.StageP4Prev1VRegsPlacedStmt` for the
placed CLI 4-kit store bundle.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Obj Arm64.Process ProofLib
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced
  StageP4RawBranchPlaced StageP4BranchPlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over hiding
  StageP4Prev1RawBranchPlaced StageP4Prev1BranchPlaced
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst hiding
  cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced cliKyberPreKeyStoreSpecPlaced
  cliPreKeyStoreSpecPlaced_quiet cliSignedPreKeyStoreSpecPlaced_quiet

/-! ## 1. Placed `Prev1` Vtable & `SessionPrev1KitPlacedOkSE` Instantiation -/

theorem cliPollSess_prev1VtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk)
    (hDropNz : lsmpl.base 547 ≠ 0#64) :
    SessionOnlyVtablesPlacedOk (cliPollSessPrev1KitPlaced A F0 peer σ) :=
  cliSessionOnlyVtablesPlacedOk
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, lsDropOffPlaced_eq hDropNz, lsDropOffPlaced_eq hDropNz,
      rfl, rfl⟩

theorem cliPollSess_prev1StoreShim_rocl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let kit := cliPollSessPrev1KitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + kit.storeShimOff) (withLsRoCl lsmpl (kitStoreShimSpec kit)) := by
  intro kit
  exact SessKit.cliSessStoreShim_rocl_placed_ok
    (rd := cliIo.rd) (F0 := F0) (pathOk := cliWrOk) (Scope := Slots.scopeKit) (peer := peer)
    (s1 := (cliKitStk B).sessLoadShim) (s2 := (cliKitStk B).sessLoadPoll)
    (s3 := (cliKitStk B).sessStoreShim) (s4 := (cliKitStk B).sessStorePoll)
    (vtSym := cliSessionVtSym) (idVtSym := cliIdentityVtSym)
    hh.alloc hh.panics (Nat.le_refl _) hblk

theorem cliPollSess_prev1StorePoll_rocl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let kit := cliPollSessPrev1KitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + kit.storePollOff)
      (withLsRoCl lsmpl (Over.kitStorePollPrev1PlacedSpecE kit cliPollStorePrev1OpsPlaced)) := by
  intro kit
  have hAddr := SessKit.cliAddrText_placed_ok hh
  have hSer := Over.serializePrev1Body_placed_lscro_of_serContractsX
    (callerProg := lsProg_570 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (callerBlk := 570)
    (cliSerContractsX_placed_ok mmpl gh W hh) (by decide)
  have hPut := SessKit.cliDirPut_placed_ok hh
  have h570 := Store.StoreSessionPrev1.sessStorePollPrev1_placed_ok_of_deps
    hAddr hSer hPut (stk := (cliKitStk B).sessStorePoll) (by dsimp only [cliKitStk]; decide)
  have h570_kit : subroutine_ok (lsProg_570 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 570)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (Over.kitStorePollPrev1PlacedSpecE kit cliPollStorePrev1OpsPlaced)) := by
    refine subroutine_ok_map_panic h570 ?_
    rintro ⟨call, self, d⟩ R s0 hpre
    dsimp only [StoreKit.withLsCodeRoLoaded, Over.kitStorePollPrev1PlacedSpecE, withEnvPre,
      Over.kitStorePollPrev1PlacedSpec, kit, cliPollSessPrev1KitPlaced, cliPollSessPrev1Kit,
      cliPollSessKit, cliSessionStoreSpec, cliSessPrev1StoreAt, cliPollStorePrev1OpsPlaced] at hpre
    have hpre' : s0.mem ⊨
        ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          (E2E.Record.Serialization.CanonSession call.G call.sess ∧
            (Over.encodeRecordPrev1 call.sess call.enc).length < 2 ^ 32) ∧
          call.addr.val = peer.val⌝ ∗
        (⌜CliSessPrev1Inv peer d⌝ ∗
        (sessStoreBoxAt call.fut self call.addrA call.recA 0#8 ∗
          dirAt E2E.HooksE.A0 self d ∗ memRegion call.out 48 ∗
          protocolAddressAt E2E.HooksE.A0 call.addr call.addrA ∗
          sessionRecordPrevAt E2E.HooksE.A0 call.recA ⟨call.prevCap, call.prevPtr, some call.G⟩
            [call.enc] ⟨some call.sess⟩ ∗
          E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).sessStorePoll ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨_hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, ⟨hcan, hlen⟩, haddr⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    let x : Store.StoreSessionPrev1.SessStorePollPrev1Ghost :=
      ⟨call.fut, self, call.out, call.addrA, call.addr, call.recA,
       call.prevCap, call.prevPtr, call.G, call.sess, call.enc, d⟩
    have hm_hop : s0.mem ⊨
        (Store.StoreSessionPrev1.sessStorePollPrev1SpecPlaced E2E.HooksE.A0
          (cliKitStk B).sessStorePoll).pre x s0 ∗ R := by
      dsimp only [Store.StoreSessionPrev1.sessStorePollPrev1SpecPlaced,
        StoreKit.withLsCodeRoLoaded, x]
      have h1 : s0.mem ⊨
          ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
            call.addr.name.bytes.length < 2 ^ 32 ∧
            E2E.Record.Serialization.CanonSession call.G call.sess ∧
            (Over.encodeRecordPrev1 call.sess call.enc).length < 2 ^ 32 ∧
            d.changed.length < 2 ^ 32⌝ ∗
          (sessStoreBoxAt call.fut self call.addrA call.recA 0#8 ∗
            dirAt E2E.HooksE.A0 self d ∗ memRegion call.out 48 ∗
            protocolAddressAt E2E.HooksE.A0 call.addr call.addrA ∗
            sessionRecordPrevAt E2E.HooksE.A0 call.recA ⟨call.prevCap, call.prevPtr, some call.G⟩
              [call.enc] ⟨some call.sess⟩ ∗
            E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).sessStorePoll ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hname ▸ hinv.nameLt, hcan, hlen, hinv.changedLt.1⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨x, R, hm_hop, ?_, fun _ hpan => hpan⟩
    intro sf hpost
    dsimp only [Store.StoreSessionPrev1.sessStorePollPrev1SpecPlaced,
      StoreKit.withLsCodeRoLoaded, x] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨htr, hm⟩ := hpost
    have hinv_put : CliSessPrev1Inv peer
        (d.put (Cli.addressText call.addr.val) (Over.encodeRecordPrev1 call.sess call.enc)) := by
      rw [haddr]
      exact ⟨hinv.nameLt,
        Store.StoreSessionPrev1.changedLt_put_self
          (Over.encodeRecordPrev1 call.sess call.enc) hinv.changedLt⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, Over.kitStorePollPrev1PlacedSpecE, withEnvPre,
      Over.kitStorePollPrev1PlacedSpec, kit, cliPollSessPrev1KitPlaced, cliPollSessPrev1Kit,
      cliPollSessKit, cliSessionStoreSpec, cliSessPrev1StoreAt, cliPollStorePrev1OpsPlaced]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨.ok (), ?_⟩
    dsimp only [storePollPlacedOutAt]
    have hgoal : sf.mem ⊨
        ⌜(Except.ok () : Except Unit Unit) = .ok () ∧ sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliSessPrev1Inv peer
            (d.put (Cli.addressText call.addr.val) (Over.encodeRecordPrev1 call.sess call.enc))⌝ ∗
          (sessStoreBoxAt call.fut self call.addrA call.recA 1#8 ∗
            dirAt E2E.HooksE.A0 self (d.put (Cli.addressText call.addr.val)
              (Over.encodeRecordPrev1 call.sess call.enc)) ∗
            (call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (call.out + 8#64) 40 ∗
            protocolAddressAt E2E.HooksE.A0 call.addr call.addrA ∗
            sessionRecordPrevAt E2E.HooksE.A0 call.recA ⟨call.prevCap, call.prevPtr, some call.G⟩
              [call.enc] ⟨some call.sess⟩ ∗
            E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).sessStorePoll ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨rfl, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hinv_put, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  change subroutine_ok callerProg (0#64 + lsmpl.base 570) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 570)
    h570_kit hblk (by decide) (by decide)

theorem cliPollSess_prev1KitPlacedOk [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost) (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    Over.SessionPrev1KitPlacedOkSE
      (cliPollSessPrev1KitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      cliPollStorePrev1OpsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  storeShim hblk := cliPollSess_prev1StoreShim_rocl mmpl gh W B F0 peer hh hblk
  storePollPrev1 hblk := cliPollSess_prev1StorePoll_rocl mmpl gh W B F0 peer hh hblk
  storeFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact SessKit.cliSessFutDrop_rocl_placed_ok hblk

/-! ## 2. Placed `Prev1` Stage P4 Outcome Bridge & `StageP4Prev1VRegsPlacedStmt` Instantiation -/

private theorem stageP4Prev1BranchPlaced_of_over [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {ops : Over.StorePrev1Ops kit}
    {ikit : IdentityStoreSpec A 0#64}
    {pkKit : PreKeyStoreSpec A 0#64} {kpkKit : KyberPreKeyStoreSpec A 0#64}
    {s0 s : State}
    {coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64}
    {opkId? : Option (BitVec 32)} {kyberPreKeyId signedPreKeyId : BitVec 32}
    {pt enc : List (BitVec 8)} {peer : AddrGhost} {remoteIk : IdentityKey} {baseKey : PublicKey}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {pst0 : pkKit.PkState} {kst0 : kpkKit.KpkState}
    {G : SessionGhost} {ss : Session (List (BitVec 8))} {sf : State} {Pf : SepProp}
    (h : Over.StageP4Prev1BranchPlaced kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
      ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
      baseKey sst0 ist0 pst0 kst0 G ss sf Pf) :
    StageP4Prev1BranchPlaced 0#64 kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
      ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
      baseKey sst0 ist0 pst0 kst0 G ss sf Pf := by
  cases h with
  | ok c hsave hmark hrem hstore htr hpost => exact .ok c hsave hmark hrem hstore htr hpost
  | saveErr hsave htr hpost => exact .saveErr hsave htr hpost
  | markErr c e hsave hmark htr hpost => exact .markErr c e hsave hmark htr hpost
  | removeErr opkId c e hopk hsave hmark hrem htr hpost =>
    exact .removeErr opkId c e hopk hsave hmark hrem htr hpost
  | storeErr c hsave hmark hrem hstore htr hpost =>
    exact .storeErr c hsave hmark hrem hstore htr hpost

/-- Instantiates `Poll.StageP4Prev1VRegsPlacedStmt` via
`Over.stageP4_prev1_vregs_mark_remove_placed_ok`. -/
theorem stageP4Prev1_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP4Prev1VRegsPlacedStmt := by
  intro mmpl gh W B F0 peer pid kpkId spkId kbk σ kit ops ikit pkKit kpkKit hh hread
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
    opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc remoteIk baseKey
    sst0 ist0 pst0 kst0 G ss
    hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok
    hpt_le hcap_lt hptr_nz hsp_ub hfs hcro hpc hrun hsp_align htr_pfx
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  have hdealloc : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec E2E.HooksE.A0) :=
    ls_hook_ok_ultra_of_mem hh.codecHooks.dealloc (by decide)
  have hDrop : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec E2E.HooksE.A0)) :=
    cliDropSessionStructure4_placed_ok_at mmpl gh W hh
      (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
  have hSkit : Over.SessionPrev1KitPlacedOkSE kit ops
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliPollSess_prev1KitPlacedOk mmpl gh W B F0 peer hDropNz hh
  have hSvt : SessionOnlyVtablesPlacedOk kit :=
    cliPollSess_prev1VtablesPlacedOk F0 peer σ hDropNz
  have hIkit : IdentityStoreKitPlacedOkI ikit (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliIdKitPlacedOkI_full
      (IdKit.cliIdKitOkIE_placed
        (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
        hDropNz (fun _ hp => hp.2) hh
        (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hread)
        (cliGhostExterns_blackBox mmpl gh W)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (by decide) (by decide))
  have hIvt : IdentityVtablesPlacedOk ikit := cliPollId_vtablesPlacedOk F0 peer σ hDropNz
  have hPkKit : PreKeyRemoveKitPlacedOk pkKit (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliPollPk_removeKitPlacedOk mmpl gh W B F0 pid hDropNz hh hread
  have hPkVt : PreKeyVtablesPlacedOk pkKit := cliPollPk_vtablesPlacedOk F0 pid σ hDropNz
  have hKpkKit : KyberPreKeyMarkKitPlacedOk kpkKit (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliPollKpk_markKitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hread
  have hKpkVt : KyberPreKeyVtablesPlacedOk kpkKit :=
    cliPollKpk_vtablesPlacedOk F0 kpkId spkId kbk σ hDropNz
  refine SepWPp.mono_post_panic ?_ (fun _ _ h => h)
    (Over.stageP4_prev1_vregs_mark_remove_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))
      kit ops ikit pkKit kpkKit
      hdealloc hDrop hSkit hSvt hIkit hIvt hPkKit hPkVt hKpkKit hKpkVt
      s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
      opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
      sst0 ist0 pst0 kst0 G ss
      hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok
      hpt_le hcap_lt hptr_nz hsp_ub hfs hcro hpc hrun hsp_align htr_pfx
      hx19 hx24 hx25 hx26 hx27 hx28 hvregs)
  rintro sf Pf ⟨hst, hspf, hcsf, hvregsf, hcrof, hbr⟩
  exact ⟨hst, hspf, hcsf, hvregsf, hcrof, stageP4Prev1BranchPlaced_of_over hbr⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
