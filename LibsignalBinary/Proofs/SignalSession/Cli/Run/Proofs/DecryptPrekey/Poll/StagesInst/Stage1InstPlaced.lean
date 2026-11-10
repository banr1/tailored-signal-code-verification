/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1OkTrapPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.StringClonePlaced

/-!
# Relocatable `[LibsignalPlacement]` Poll Stage P1 Instantiation

Proves `stageP1_ok_trap_placed_inst : StageP1OkTrapPlacedStmt` and
`stageP1_untrusted_trap_placed_inst : StageP1UntrustedTrapPlacedStmt` from
`stageP1_ok_kit_x_ext_placed` and `stageP1_untrusted_ok_kit_x_ext_placed`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Proofs.Common.StringClonePlaced (stringClone_placed_codeLoaded_ok)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1OkTrapPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlaced

private theorem stageP1ProgPlaced_dpPollProgPlaced_eq [LibsignalPlacement] (ext : LibsignalHooks) :
    stageP1ProgPlaced ext = dpPollProgPlaced ext :=
  rfl

private theorem sepWPp_intro_stageP1VtablesPlacedAt [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {target : BitVec 64} {s0 : State}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {P : SepProp} {post onPanic : State → SepProp → Prop}
    (hro : CryptoVerification.LibsignalRoLoaded lsmpl s0.mem)
    (hsess : SessionOnlyVtablesPlacedOk kit)
    (hid : IdentityVtablesPlacedOk ikit)
    (hwp : SepWPp prog target s0 (stageP1VtablesPlacedAt kit ikit ∗ P)
      (fun sf P_f => ∃ Drop P_clean, (P_f ⊢ Drop ∗ P_clean) ∧ post sf P_clean)
      onPanic) :
    SepWPp prog target s0 P post onPanic := by
  have hwp' := SepWPp.congr_post_drop_left hwp
  intro R hm hL
  have hm' : s0.mem ⊨ (stageP1VtablesPlacedAt kit ikit ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact satisfies_stageP1VtablesPlacedAt hsess hid hro hm
  exact hwp' R hm' hL

private theorem cliDealloc_dpPoll_ok [LibsignalPlacement] {ext : LibsignalHooks}
    (hh : RunHooksPlaced E2E.HooksE.A0 ext) :
    subroutine_ok (dpPollProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec E2E.HooksE.A0) :=
  ls_hook_ok_ultra_of_mem hh.codecHooks.dealloc (by decide)

private theorem hookSat_session2Memcpy_of_frameless {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym framelessMemcpySpec) :
    HookSat H sym session2MemcpySpecX := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp extHookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [session2MemcpySpecX, framelessMemcpySpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [session2MemcpySpecX, framelessMemcpySpec] at hpost ⊢
    ac_nf at hpost ⊢

private theorem cliSession2Memcpy_dpPoll_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpySpecX) :=
  StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
    (ls_hook_ok_ultra_of_mem (i := 518)
      (hookSat_session2Memcpy_of_frameless hh.codecHooks.memcpy)
      (by decide))

private theorem cliStringClone_dpPoll_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 623) (StoreKit.withLsCodeRoLoaded lsmpl (stringCloneSpec E2E.HooksE.A0)) :=
  StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (stringClone_placed_codeLoaded_ok
      (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
      ((show CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec =
          CryptoVerification.LibsignalTripleRatchet.sessionShimSpec from rfl) ▸
        hh.codecHooks.shim)
      hh.codecHooks.alloc
      ((show CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
          CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec from rfl) ▸
        hh.codecHooks.memcpy)
      hh.codecHooks.panic_raw
      (by decide))

private theorem cliPollSess_kitPlacedOkSE_a0 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hread : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hdeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46) (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0)) :
    SessionOnlyKitPlacedOkSE
      (cliPollSessKitPlaced E2E.HooksE.A0 F0 Slots.scopeKit peer (cliKitStk B))
      Slots.scopeKit E2E.Record.encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  SessKit.cliSessKitOkSE_placed
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (deserProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (deserBlk := 518)
    (serProg := CryptoVerification.E2E.Record.Placed.lsProg_52
      (cliGhostExterns gh (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz (fun _ hp => hp.2) hh
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hread)
    hdeser
    (Store.SerGlueX.serializeCanonX_placed_ok_of_serContractsX
      (cliSerContractsX_placed_ok mmpl gh W hh))
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem cliPollId_kitPlacedOkI_a0 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hread : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile)) :
    IdentityStoreKitPlacedOkI
      (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliIdKitPlacedOkI_full
    (IdKit.cliIdKitOkIE_placed
      (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
      hDropNz (fun _ hp => hp.2) hh
      (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hread)
      (cliGhostExterns_blackBox mmpl gh W)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) (by decide))

private theorem cliDropSessionStructure_dpPoll_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec E2E.HooksE.A0)) :=
  StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (cliDropSessionStructure4_placed_ok_at mmpl gh W hh
      (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518))

private theorem extHookStack_le_cliPollSess_loadCallStack [LibsignalPlacement]
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    extHookStack ≤
      loadCallStack (cliPollSessKitPlaced E2E.HooksE.A0 F0 Slots.scopeKit peer (cliKitStk B)) := by
  dsimp only [extHookStack, loadCallStack, cliPollSessKitPlaced, cliPollSessKit,
    cliSessionStoreSpec, cliKitStk, SessKit.loadShimNeed, SessKit.loadPollNeed,
    allocHookStack]
  omega

private theorem extHookStack_le_cliPollId_trustCallStack [LibsignalPlacement]
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    extHookStack ≤
      trustCallStack (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)) := by
  dsimp only [extHookStack, trustCallStack, cliPollIdKitPlaced, cliIdStoreSpecFullPlaced,
    cliIdStoreSpecFull, cliIdentityStoreSpec, cliKitStk, IdKit.trustShimNeed,
    IdKit.trustPollNeed, allocHookStack]
  omega

set_option maxHeartbeats 800000 in
/-- Instantiates `Poll.StageP1OkTrapPlacedStmt` via `stageP1_ok_kit_x_ext_placed`. -/
theorem stageP1_ok_trap_placed_inst [LibsignalPlacement]
    (hDropNz : lsmpl.base 547 ≠ 0#64) : StageP1OkTrapPlacedStmt := by
  intro mmpl gh W B F0 peer remoteIdKey σ kit ikit st ist
    hh hread hdeser hstack_lt haddr_ss haddr_id hload_ok htrust_true
    s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390 b_4f2
    hcrl hfs hpc hrun hsp_align hsp_def hx0 hx1 hx2
  refine sepWPp_intro_stageP1VtablesPlacedAt hcrl.2
    (cliPollSess_vtablesPlacedOk (A := E2E.HooksE.A0) F0 Slots.scopeKit peer σ hDropNz)
    (cliPollId_vtablesPlacedOk (A := E2E.HooksE.A0) F0 peer σ hDropNz) ?_
  have hSkit := cliPollSess_kitPlacedOkSE_a0 mmpl gh W B F0 peer hDropNz hh hread hdeser
  have hIkit := cliPollId_kitPlacedOkI_a0 mmpl gh W B F0 peer hDropNz hh hread
  have hwp0 := stageP1_ok_kit_x_ext_placed
    (A := E2E.HooksE.A0) (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Scope := Slots.scopeKit) (encRecord := E2E.Record.encodeRecord)
    (kit := kit) (ikit := ikit) (st := st) (ist := ist)
    peer remoteIdKey
  rw [stageP1ProgPlaced_dpPollProgPlaced_eq] at hwp0
  have hwp := hwp0
    (cliDealloc_dpPoll_ok hh)
    (cliSession2Memcpy_dpPoll_ok mmpl gh W hh)
    (hSkit.loadShim (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (callerBlk := 518) (by decide))
    (hSkit.loadPoll (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (callerBlk := 518) (by decide))
    (hSkit.loadFutDrop (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (callerBlk := 518) (by decide))
    (hIkit.trustShim (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (callerBlk := 518) (by decide))
    (hIkit.trustPoll (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (callerBlk := 518) (by decide))
    (hIkit.trustFutDrop (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (callerBlk := 518) (by decide))
    hstack_lt
    (extHookStack_le_cliPollSess_loadCallStack B F0 peer)
    (extHookStack_le_cliPollId_trustCallStack B F0 peer)
    haddr_ss haddr_id hload_ok htrust_true
    s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390 b_4f2
    hcrl hfs hpc hrun hsp_align hsp_def hx0 hx1 hx2
  refine SepWPp.mono_run
    (SepWPp.weaken_pre (Entails.of_eq (by dsimp only [stageP1VtablesPlacedAt]; ac_rfl)) hwp)
    fun sf P_f hpost => ?_
  rcases hpost with ⟨⟨opt, hrel_load, hrel_trust, htr_f, hent⟩, hregs⟩
  refine ⟨stageP1VtablesPlacedAt kit ikit, _, ?_, ⟨opt, hrel_load, hrel_trust, htr_f, Entails.refl _⟩, hregs⟩
  refine Entails.trans hent (Entails.of_eq ?_)
  simp only [sepExists_sepConj_right]
  refine congrArg sepExists (funext fun v_a8 => ?_)
  refine congrArg sepExists (funext fun v_b8 => ?_)
  refine congrArg sepExists (funext fun v_d0 => ?_)
  dsimp only [stageP1VtablesPlacedAt]
  ac_rfl

set_option maxHeartbeats 800000 in
/-- Instantiates `Poll.StageP1UntrustedTrapPlacedStmt` via `stageP1_untrusted_ok_kit_x_ext_placed`. -/
theorem stageP1_untrusted_trap_placed_inst [LibsignalPlacement]
    (hDropNz : lsmpl.base 547 ≠ 0#64) :
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
          (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  intro mmpl gh W B F0 peer remoteIdKey σ kit ikit st ist
    hh hread hdeser hstack_lt haddr_ss haddr_id hload_ok htrust_false
    s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390
    hcrl hfs hpc hrun hsp_align hsp_def hx0 hx1 hx2
  refine sepWPp_intro_stageP1VtablesPlacedAt hcrl.2
    (cliPollSess_vtablesPlacedOk (A := E2E.HooksE.A0) F0 Slots.scopeKit peer σ hDropNz)
    (cliPollId_vtablesPlacedOk (A := E2E.HooksE.A0) F0 peer σ hDropNz) ?_
  have hSkit := cliPollSess_kitPlacedOkSE_a0 mmpl gh W B F0 peer hDropNz hh hread hdeser
  have hIkit := cliPollId_kitPlacedOkI_a0 mmpl gh W B F0 peer hDropNz hh hread
  have hwp0 := stageP1_untrusted_ok_kit_x_ext_placed
    (A := E2E.HooksE.A0) (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Scope := Slots.scopeKit) (encRecord := E2E.Record.encodeRecord)
    (kit := kit) (ikit := ikit) (st := st) (ist := ist)
    peer remoteIdKey
  rw [stageP1ProgPlaced_dpPollProgPlaced_eq] at hwp0
  have hwp := hwp0
    (cliDropSessionStructure_dpPoll_ok mmpl gh W hh)
    (cliDealloc_dpPoll_ok hh)
    (cliSession2Memcpy_dpPoll_ok mmpl gh W hh)
    (cliStringClone_dpPoll_ok mmpl gh W hh)
    (hSkit.loadShim (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (callerBlk := 518) (by decide))
    (hSkit.loadPoll (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (callerBlk := 518) (by decide))
    (hSkit.loadFutDrop (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (callerBlk := 518) (by decide))
    (hIkit.trustShim (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (callerBlk := 518) (by decide))
    (hIkit.trustPoll (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (callerBlk := 518) (by decide))
    (hIkit.trustFutDrop (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (callerBlk := 518) (by decide))
    hstack_lt
    (extHookStack_le_cliPollSess_loadCallStack B F0 peer)
    haddr_ss haddr_id hload_ok htrust_false
    s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390
    hcrl hfs hpc hrun hsp_align hsp_def hx0 hx1 hx2
  refine SepWPp.mono_run
    (SepWPp.weaken_pre (Entails.of_eq (by dsimp only [stageP1VtablesPlacedAt]; ac_rfl)) hwp)
    fun sf P_f hpost => ?_
  rcases hpost with ⟨⟨opt, hrel_load, hrel_trust, htr_f, hent⟩, hregs⟩
  refine ⟨stageP1VtablesPlacedAt kit ikit, _, ?_, ⟨opt, hrel_load, hrel_trust, htr_f, Entails.refl _⟩, hregs⟩
  refine Entails.trans hent (Entails.of_eq ?_)
  simp only [sepExists_sepConj_right]
  refine congrArg sepExists (funext fun v_a8 => ?_)
  refine congrArg sepExists (funext fun v_b8 => ?_)
  refine congrArg sepExists (funext fun v_d0 => ?_)
  dsimp only [stageP1VtablesPlacedAt]
  ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
