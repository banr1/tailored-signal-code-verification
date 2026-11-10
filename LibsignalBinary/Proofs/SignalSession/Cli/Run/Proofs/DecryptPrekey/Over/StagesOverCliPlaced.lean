/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.WrapperOverPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv

/-!
# Relocatable CLI Poll Self-Kit and Stage P1 Over-Path Adapters

Relocatable `[LibsignalPlacement]` self-identity kit proofs and Stage P1 adapters
(`OverStageP1OkCliPlacedStmt` and `OverClosureUntrustedD2cPlacedStmt`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  CliGhostHooks cliGhostExterns
)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst hiding
  cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced cliKyberPreKeyStoreSpecPlaced
  cliPreKeyStoreSpecPlaced_quiet cliSignedPreKeyStoreSpecPlaced_quiet
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel

private theorem cliPollSelf_kpShim_rocl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let skit := cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + skit.kpShimOff)
      (withLsRoCl lsmpl (IdentitySelf.kitKpShimSpec skit)) := by
  intro skit
  have h602 := Initiate.StoreCalleesProofs.idOwnShim_lift_stk_placed
    (Initiate.StoreCalleesProofs.idKeyPairShim_fixed_placed_ok hh.alloc
      (Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W))
    (stk := (cliKitStk B).kpShim)
    (by dsimp [cliKitStk, extHookStack]; omega)
    (by dsimp [cliKitStk, extHookStack]; omega)
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 602)
    h602 hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 602) _; rw [BitVec.zero_add]
  refine subroutine_ok_map_panic hrocl fun self R s0 hp => ?_
  dsimp only [withLsRoCl, IdentitySelf.kitKpShimSpec, skit, cliPollSelfKitPlaced,
    cliIdSelfSpecFullPlaced, idOwnShimSpecPlaced, StoreKit.withLsCodeRoLoaded] at hp ⊢
  exact ⟨self, R, Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp,
    fun sf hq => by
      dsimp only [idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hq ⊢
      simpa only [BitVec.zero_add] using hq,
    fun _ hpan => hpan⟩

private theorem cliPollSelf_regIdShim_rocl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let skit := cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + skit.regIdShimOff)
      (withLsRoCl lsmpl (IdentitySelf.kitRegIdShimSpec skit)) := by
  intro skit
  have h603 := Initiate.StoreCalleesProofs.idOwnShim_lift_stk_placed
    (Initiate.StoreCalleesProofs.idRegIdShim_fixed_placed_ok hh.alloc
      (Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W))
    (stk := (cliKitStk B).regIdShim)
    (by dsimp [cliKitStk, extHookStack]; omega)
    (by dsimp [cliKitStk, extHookStack]; omega)
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 603)
    h603 hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 603) _; rw [BitVec.zero_add]
  refine subroutine_ok_map_panic hrocl fun self R s0 hp => ?_
  dsimp only [withLsRoCl, IdentitySelf.kitRegIdShimSpec, skit, cliPollSelfKitPlaced,
    cliIdSelfSpecFullPlaced, idOwnShimSpecPlaced, StoreKit.withLsCodeRoLoaded] at hp ⊢
  exact ⟨self, R, Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp,
    fun sf hq => by
      dsimp only [idOwnFutBoxAtPlaced, idOwnFutBoxAt] at hq ⊢
      simpa only [BitVec.zero_add] using hq,
    fun _ hpan => hpan⟩

private theorem panic_absorb_extra_placed {φ : Prop} {extra R : SepProp} {m : Memory}
    (h : m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ (extra ∗ R)) :
    m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ R := by
  have h1 : m ⊨ ⌜φ⌝ ∗ ((anyHeap ∗ extra) ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) h
  rw [satisfies_pure_sepConj] at h1
  have h2 : m ⊨ ⌜φ⌝ ∗ (anyHeap ∗ R) := by
    rw [satisfies_pure_sepConj]
    exact ⟨h1.1, Arm64.Satisfies.mono (sepConj_mono_left (entails_anyHeap (anyHeap ∗ extra))) h1.2⟩
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) h2

private theorem cliPollSelf_kpPoll_rocl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let skit := cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + skit.kpPollOff)
      (withLsRoCl lsmpl (kitKpPollPlacedSpecI skit)) := by
  intro skit
  have hGet589 := SessKit.cliDirGet_placed_ok
    (readProg := readProg) (jRead := jRead) (fun _ hp => hp.2) hh
    (RunSkeleton.cliReadFilePlaced_rocl_ok mmpl gh W B.readFile hRead)
    hjRead hjRead_unmut
  have hGet567 := Store.PlacedCommon.ls_transfer_lscro
    (callerProg := lsProg_567 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (j := 589) hGet589
  have hDec567 := Store.PlacedCommon.ls_transfer_lscro
    (callerProg := lsProg_567 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (j := 84)
    (cliIdentityKeyPairTryFrom_placed_ok mmpl gh W hh)
  have h567 := Initiate.IdKeyPairPoll.idKeyPairPoll_placed_ok_of_deps
    (stk := (cliKitStk B).kpPoll)
    hh.alloc hGet567 hDec567
    (by rw [dirGetNeed_eta B]; dsimp [cliKitStk, Initiate.IdKeyPairPoll.kpCalleeStk]; omega)
  have hhop := Store.PlacedCommon.ls_transfer_lscro
    (callerProg := callerProg) (j := 567) h567 hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 567) _; rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded (subroutine_ok_map_panic hhop ?_)
  rintro ⟨fut, out, self, g⟩ R s0 hpre
  change IdGhost at g
  dsimp only [StoreKit.withLsCodeRoLoaded, kitKpPollPlacedSpecI, withLsLogOff,
    IdentitySelf.kitKpPollSpecE, IdentitySelf.kitKpPollSpec, withEnvPre,
    skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, cliPollIdKitPlaced,
    cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
    cliIdentityStoreSpec, cliIdStoreAt] at hpre
  have hpre' : s0.mem ⊨
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      (⌜s0.fs.files = F0⌝ ∗
      (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out⌝ ∗
      (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
      (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
      (idOwnFutBoxAt fut self 0#8 ∗ dirAt E2E.HooksE.A0 self g.own ∗
        memRegion out 72 ∗ FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
        stackAt s0.sp (cliKitStk B).kpPoll ∗
        (dirAt E2E.HooksE.A0 (self + 0x28#64) g.peers ∗ R)))))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8⟩, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hown, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
  let frameKpCore : SepProp :=
    ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
    ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
    dirAt E2E.HooksE.A0 (self + 0x28#64) g.peers
  have hhop_pure :
      s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        g.own.path.length < 2 ^ 32 ∧
        cliWrOk (pathOf g.own.path (utf8 "identity-key-pair")) ∧
        ∀ bs, g.own.get cliIo.rd s0.fs.files (utf8 "identity-key-pair") = .ok bs →
          bs.length < 2 ^ 32 :=
    ⟨hx0, hx8, hown.ownPathLt, hown.kpPathOk, fun bs hbs =>
      hown.kpSizeOk bs (hfiles ▸ hbs)⟩
  have hm_hop :
      s0.mem ⊨ (idKeyPairPollSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 (cliKitStk B).kpPoll).pre
          ⟨fut, out, self, g.own⟩ s0 ∗ (frameKpCore ∗ R) := by
    dsimp only [idKeyPairPollSpecPlaced, StoreKit.withLsCodeRoLoaded, frameKpCore]
    have h1 : s0.mem ⊨
        ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          g.own.path.length < 2 ^ 32 ∧
          cliWrOk (pathOf g.own.path (utf8 "identity-key-pair")) ∧
          ∀ bs, g.own.get cliIo.rd s0.fs.files (utf8 "identity-key-pair") = .ok bs →
            bs.length < 2 ^ 32⌝ ∗
        (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
        (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
        (idOwnFutBoxAt fut self 0#8 ∗ dirAt E2E.HooksE.A0 self g.own ∗
          memRegion out 72 ∗ FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp (cliKitStk B).kpPoll ∗
          (dirAt E2E.HooksE.A0 (self + 0x28#64) g.peers ∗ R))))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hhop_pure, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hown, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hinv, hspatial⟩
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
  refine ⟨⟨fut, out, self, g.own⟩, frameKpCore ∗ R, hm_hop, ?_, fun sf hpan => by
    dsimp only [idKeyPairPollSpecPlaced, kitKpPollPlacedSpecI, StoreKit.withLsCodeRoLoaded,
      withLsLogOff, IdentitySelf.kitKpPollSpecE, IdentitySelf.kitKpPollSpec, withEnvPre] at hpan ⊢
    exact panic_absorb_extra_placed hpan⟩
  intro sf hpost
  dsimp only [idKeyPairPollSpecPlaced, StoreKit.withLsCodeRoLoaded, frameKpCore] at hpost
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hpost
  obtain ⟨ans0, ⟨hans0, htr⟩, hm⟩ := hpost
  rw [hfiles, IdGhost.keyPair_mk_own] at hans0
  dsimp only [StoreKit.withLsCodeRoLoaded, kitKpPollPlacedSpecI, withLsLogOff,
    IdentitySelf.kitKpPollSpecE, IdentitySelf.kitKpPollSpec, withEnvPre,
    skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, cliPollIdKitPlaced,
    cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
    cliIdentityStoreSpec, cliIdStoreAt]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  cases ans0 with
  | ok kp =>
    have hrel : cliKpRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok kp) :=
      (cliKpRel_ok_iff (E := CliSelfSpeErr) cliIo.rd F0 g kp).2 hans0.symm
    refine ⟨.ok kp, ?_⟩
    dsimp only [IdentitySelf.kpPollOutAt, idKeyPairOutAt] at hm ⊢
    have hgoal : sf.mem ⊨
        ⌜cliKpRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok kp) ∧ sf.trace = s0.trace ++ []⌝ ∗
        (idKeyPairOutAt E2E.HooksE.A0 out (.ok kp) ∗ idOwnFutBoxAt fut self 1#8 ∗
          dirAt E2E.HooksE.A0 self g.own ∗ FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp (cliKitStk B).kpPoll ∗
          ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
          ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
          dirAt E2E.HooksE.A0 (self + 0x28#64) g.peers ∗ R) := by
      dsimp only [idKeyPairOutAt]
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, hm⟩
    dsimp only [idKeyPairOutAt] at hgoal
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  | error u =>
    cases u
    have herr_ent :
        idKeyPairOutAt E2E.HooksE.A0 out (.error ()) ⊢
          ∃∗ e : skit.KpErr, IdentitySelf.kpPollOutAt skit out (.error e) :=
      (cliIdentitySelf_kpErr_layout_placed E2E.HooksE.A0 F0
        (peer := peer) (t1 := (cliKitStk B).idTrustShim) (t2 := (cliKitStk B).idTrustPoll)
        (t3 := (cliKitStk B).idSaveShim) (t4 := (cliKitStk B).idSavePoll)
        (k1 := (cliKitStk B).kpShim) (k2 := (cliKitStk B).kpPoll)
        (k3 := (cliKitStk B).regIdShim) (k4 := (cliKitStk B).regIdPoll) out).2
    have hm' := Arm64.Satisfies.mono (sepConj_mono_left herr_ent) hm
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
    obtain ⟨e, hme⟩ := hm'
    have hrel : cliKpRel cliIo.rd F0 g (.error e) :=
      (cliKpRel_error_iff cliIo.rd F0 g e).2 hans0.symm
    refine ⟨.error e, ?_⟩
    dsimp only [skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced,
      IdentitySelf.kpPollOutAt] at hme ⊢
    have hgoal : sf.mem ⊨
        ⌜cliKpRel cliIo.rd F0 g (.error e) ∧ sf.trace = s0.trace ++ []⌝ ∗
        (((out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
            speErrAt (cliSelfSpeErrSpec E2E.HooksE.A0) (out + 8#64) e ∗
            memRegion (out + 0x38#64) 16) ∗
          idOwnFutBoxAt fut self 1#8 ∗
          dirAt E2E.HooksE.A0 self g.own ∗ FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp (cliKitStk B).kpPoll ∗
          ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
          ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
          dirAt E2E.HooksE.A0 (self + 0x28#64) g.peers ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, hme⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal

private theorem cliPollSelf_regIdPoll_rocl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let skit := cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)
    subroutine_ok callerProg (0#64 + skit.regIdPollOff)
      (withLsRoCl lsmpl (kitRegIdPollPlacedSpecI skit)) := by
  intro skit
  have hGet589 := SessKit.cliDirGet_placed_ok
    (readProg := readProg) (jRead := jRead) (fun _ hp => hp.2) hh
    (RunSkeleton.cliReadFilePlaced_rocl_ok mmpl gh W B.readFile hRead)
    hjRead hjRead_unmut
  have hGet568 := Store.PlacedCommon.ls_transfer_lscro
    (callerProg := lsProg_568 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (j := 589) hGet589
  have h568 := Initiate.IdRegIdPoll.idRegIdPoll_placed_ok_of_deps
    (stk := (cliKitStk B).regIdPoll)
    hh.alloc (Slots.cliGhostExterns_panic_handle_error mmpl gh W) hGet568
    (by rw [dirGetNeed_eta B]; dsimp [cliKitStk, Initiate.IdRegIdPoll.regCalleeStk]; omega)
  have hhop := Store.PlacedCommon.ls_transfer_lscro
    (callerProg := callerProg) (j := 568) h568 hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 568) _; rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded (subroutine_ok_map_panic hhop ?_)
  rintro ⟨fut, out, self, g⟩ R s0 hpre
  change IdGhost at g
  dsimp only [StoreKit.withLsCodeRoLoaded, kitRegIdPollPlacedSpecI, withLsLogOff,
    IdentitySelf.kitRegIdPollSpecE, IdentitySelf.kitRegIdPollSpec, withEnvPre,
    skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, cliPollIdKitPlaced,
    cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
    cliIdentityStoreSpec, cliIdStoreAt] at hpre
  have hpre' : s0.mem ⊨
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      (⌜s0.fs.files = F0⌝ ∗
      (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out⌝ ∗
      (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
      (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
      (idOwnFutBoxAt fut self 0#8 ∗ dirAt E2E.HooksE.A0 self g.own ∗
        memRegion out 48 ∗ E2E.HooksE.A0.pool ∗
        stackAt s0.sp (cliKitStk B).regIdPoll ∗
        (dirAt E2E.HooksE.A0 (self + 0x28#64) g.peers ∗ FromRecordCallees.lsLogOff ∗ R)))))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8⟩, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hown, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
  let frameRegCore : SepProp :=
    ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
    ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
    dirAt E2E.HooksE.A0 (self + 0x28#64) g.peers ∗ FromRecordCallees.lsLogOff
  have hhop_pure :
      s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        g.own.path.length < 2 ^ 32 ∧
        cliWrOk (pathOf g.own.path (utf8 "registration-id")) :=
    ⟨hx0, hx8, hown.ownPathLt, hown.regPathOk⟩
  have hm_hop :
      s0.mem ⊨ (idRegIdPollSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 (cliKitStk B).regIdPoll).pre
          ⟨fut, out, self, g.own⟩ s0 ∗ (frameRegCore ∗ R) := by
    dsimp only [idRegIdPollSpecPlaced, StoreKit.withLsCodeRoLoaded, frameRegCore]
    have h1 : s0.mem ⊨
        ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          g.own.path.length < 2 ^ 32 ∧
          cliWrOk (pathOf g.own.path (utf8 "registration-id"))⌝ ∗
        (⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
        (⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
        (idOwnFutBoxAt fut self 0#8 ∗ dirAt E2E.HooksE.A0 self g.own ∗
          memRegion out 48 ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp (cliKitStk B).regIdPoll ∗
          (dirAt E2E.HooksE.A0 (self + 0x28#64) g.peers ∗ FromRecordCallees.lsLogOff ∗ R))))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hhop_pure, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hown, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨hinv, hspatial⟩
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
  refine ⟨⟨fut, out, self, g.own⟩, frameRegCore ∗ R, hm_hop, ?_, fun sf hpan => by
    dsimp only [idRegIdPollSpecPlaced, kitRegIdPollPlacedSpecI, StoreKit.withLsCodeRoLoaded,
      withLsLogOff, IdentitySelf.kitRegIdPollSpecE, IdentitySelf.kitRegIdPollSpec, withEnvPre] at hpan ⊢
    exact panic_absorb_extra_placed hpan⟩
  intro sf hpost
  dsimp only [idRegIdPollSpecPlaced, StoreKit.withLsCodeRoLoaded, frameRegCore] at hpost
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hpost
  obtain ⟨ans0, ⟨hans0, htr⟩, hm⟩ := hpost
  rw [hfiles, IdGhost.regId_mk_own] at hans0
  dsimp only [StoreKit.withLsCodeRoLoaded, kitRegIdPollPlacedSpecI, withLsLogOff,
    IdentitySelf.kitRegIdPollSpecE, IdentitySelf.kitRegIdPollSpec, withEnvPre,
    skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced, cliPollIdKitPlaced,
    cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
    cliIdentityStoreSpec, cliIdStoreAt]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  cases ans0 with
  | ok reg =>
    have hrel : cliRegIdRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok reg) :=
      (cliRegIdRel_ok_iff (E := CliSelfSpeErr) cliIo.rd F0 g reg).2 hans0.symm
    refine ⟨.ok reg, ?_⟩
    dsimp only [IdentitySelf.regIdPollOutAt, idRegIdOutAt] at hm ⊢
    have hgoal : sf.mem ⊨
        ⌜cliRegIdRel (E := CliSelfSpeErr) cliIo.rd F0 g (.ok reg) ∧ sf.trace = s0.trace ++ []⌝ ∗
        (((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₃₂ reg) ∗
            memRegion (out + 12#64) 36) ∗
          idOwnFutBoxAt fut self 1#8 ∗
          dirAt E2E.HooksE.A0 self g.own ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp (cliKitStk B).regIdPoll ∗
          ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
          ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
          dirAt E2E.HooksE.A0 (self + 0x28#64) g.peers ∗ FromRecordCallees.lsLogOff ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, hm⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  | error u =>
    cases u
    have herr_ent :
        idRegIdOutAt E2E.HooksE.A0 out (.error ()) ⊢
          ∃∗ e : skit.RegIdErr, IdentitySelf.regIdPollOutAt skit out (.error e) :=
      (cliIdentitySelf_regIdErr_layout_placed E2E.HooksE.A0 F0
        (peer := peer) (t1 := (cliKitStk B).idTrustShim) (t2 := (cliKitStk B).idTrustPoll)
        (t3 := (cliKitStk B).idSaveShim) (t4 := (cliKitStk B).idSavePoll)
        (k1 := (cliKitStk B).kpShim) (k2 := (cliKitStk B).kpPoll)
        (k3 := (cliKitStk B).regIdShim) (k4 := (cliKitStk B).regIdPoll) out).2
    have hm' := Arm64.Satisfies.mono (sepConj_mono_left herr_ent) hm
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
    obtain ⟨e, hme⟩ := hm'
    have hrel : cliRegIdRel cliIo.rd F0 g (.error e) :=
      (cliRegIdRel_error_iff cliIo.rd F0 g e).2 hans0.symm
    refine ⟨.error e, ?_⟩
    dsimp only [skit, cliPollSelfKitPlaced, cliIdSelfSpecFullPlaced,
      IdentitySelf.regIdPollOutAt] at hme ⊢
    have hgoal : sf.mem ⊨
        ⌜cliRegIdRel cliIo.rd F0 g (.error e) ∧ sf.trace = s0.trace ++ []⌝ ∗
        (speErrAt (cliSelfSpeErrSpec E2E.HooksE.A0) out e ∗ idOwnFutBoxAt fut self 1#8 ∗
          dirAt E2E.HooksE.A0 self g.own ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp (cliKitStk B).regIdPoll ∗
          ⌜CliIdOwnInv cliIo.rd F0 cliWrOk g.own⌝ ∗
          ⌜CliIdInv cliIo.rd F0 cliWrOk peer g⌝ ∗
          dirAt E2E.HooksE.A0 (self + 0x28#64) g.peers ∗ FromRecordCallees.lsLogOff ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, hme⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal

theorem cliPollSelf_kitPlacedOk [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost) (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    IdentitySelfStoreKitPlacedOkI
      (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  kpShim hblk := cliPollSelf_kpShim_rocl mmpl gh W B F0 peer hh hblk
  kpPoll hblk := cliPollSelf_kpPoll_rocl mmpl gh W B F0 peer hh hRead hjRead hjRead_unmut hblk
  kpFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]; exact IdKit.cliIdFutDrop_rocl_placed_ok hblk
  regIdShim hblk := cliPollSelf_regIdShim_rocl mmpl gh W B F0 peer hh hblk
  regIdPoll hblk := cliPollSelf_regIdPoll_rocl mmpl gh W B F0 peer hh hRead hjRead hjRead_unmut hblk
  regIdFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]; exact IdKit.cliIdFutDrop_rocl_placed_ok hblk

/-! ## 2. Placed Stage P1 CLI Adapters (`OverStageP1OkCliPlacedStmt`, `OverClosureUntrustedD2cPlacedStmt`) -/

theorem overStageP1OkCli_of_trap [LibsignalPlacement]
    (h : StageP1OkTrapPlacedStmt) : OverStageP1OkCliPlacedStmt := by
  intro mmpl gh W B F0 peer remoteIdKey _σ _kit _ikit hh hRead hDeser hp1_64 hload htrust
    s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390 b_4f2
    hro0 hfiles0 hpc hrun hsp_align0 hsp_eq hx0 hx1 hx2
  exact h mmpl gh W B F0 peer remoteIdKey
    StoresGhost.opened.sessions StoresGhost.opened.identity
    hh hRead hDeser hp1_64 rfl rfl hload htrust
    s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390 b_4f2
    hro0 (cliPollStageP1_fsAt_placed hh F0 Slots.scopeKit peer B hfiles0)
    hpc hrun hsp_align0 hsp_eq hx0 hx1 hx2

set_option maxHeartbeats 800000 in
theorem closure_untrusted_d2c_trap_placed_ok [LibsignalPlacement]
    (hUntrusted : StageP1UntrustedTrapPlacedStmt) :
    OverClosureUntrustedD2cPlacedStmt := by
  intro mmpl gh W X B S Scope hh hReadFile hDeser hinjK hsub hS stk' hneed hstk63 y R s0
    hpc hrun hsp hro0 hx0 hx1 hx2 hfiles0 hfPeer hdecOk htrusted hm_base
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
    Arm64.Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
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
    Arm64.Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
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
      rw [hS, decPkDefD2c_eq_decPkDef_of_untrusted X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins (by rw [htrusted]; decide)]
      exact decPkDef_of_trust_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadRec (Or.inr htrusted)
    have hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) s0.trace sf.trace :=
      slotOutTr_of_err StoresGhost.opened s0.trace sf.trace nofun nofun hans
    have hmf1 := Arm64.Satisfies.mono (sepConj_mono_left hent_f) hmf
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
      refine Arm64.Satisfies.mono ?_ hmf2
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
      Arm64.Satisfies.mono (sepConj_mono_left
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
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · intro sf P_f hoom _hsteps hmf
    rw [← sepConj_assoc] at hmf
    exact dpPollOnPanic_of_closOom_placed stk' y hoom hmf

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
