/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1Inst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.BranchesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.EpiloguePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4

/-!
# Relocatable `[LibsignalPlacement]` Poll Stage P4 Instantiations

Proves `stageP4Matched_placed_inst : Poll.StageP4MatchedPlacedStmt` and
`stageP4PathA_placed_inst : Poll.StageP4PathAPlacedStmt` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced StageP4RawBranchPlaced StageP4BranchPlaced
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst hiding
  cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced cliKyberPreKeyStoreSpecPlaced
  cliPreKeyStoreSpecPlaced_quiet cliSignedPreKeyStoreSpecPlaced_quiet
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns cliGhostExterns_other)

private theorem panic_absorb_extra_placed {φ : Prop} {extra R : SepProp} {m : Memory}
    (h : m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ (extra ∗ R)) : m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ R := by
  have h1 : m ⊨ ⌜φ⌝ ∗ ((anyHeap ∗ extra) ∗ R) := Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) h
  rw [satisfies_pure_sepConj] at h1
  have h2 : m ⊨ ⌜φ⌝ ∗ (anyHeap ∗ R) := (satisfies_pure_sepConj ..).mpr
    ⟨h1.1, Satisfies.mono (sepConj_mono_left (entails_anyHeap (anyHeap ∗ extra))) h1.2⟩
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) h2

private theorem saveUpd_own_placed (rd : ReadRule) (F0 : FsFiles) (g : IdGhost)
    (addr : AddrVal) (key : IdentityKey) : (IdGhost.saveUpd rd F0 g addr key).own = g.own := by
  unfold IdGhost.saveUpd; cases IdGhost.peer rd F0 g addr <;> rfl

theorem cliIdKitPlacedOkI_full [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {t1 t2 t3 t4 : Nat}
    (hBase : IdentityStoreKitPlacedOkI
      (IdKit.cliIdentityKitSpecPlaced A rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym) H) :
    IdentityStoreKitPlacedOkI (cliIdStoreSpecFullPlaced A rd F0 pathOk peer t1 t2 t3 t4) H where
  trustShim := hBase.trustShim
  trustFutDrop := hBase.trustFutDrop
  saveShim := hBase.saveShim
  saveFutDrop := hBase.saveFutDrop
  trustPoll hblk := by
    refine subroutine_ok_map_panic (hBase.trustPoll hblk) ?_
    rintro ⟨x, d, self, g⟩ R s0 hpre; change IdGhost at g
    dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
      kitTrustPollPlacedSpec, withEnvPre, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull] at hpre
    have hpre' : s0.mem ⊨ (withLsRoCl lsmpl (kitTrustPollPlacedSpecI
        (IdKit.cliIdentityKitSpecPlaced A rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym))).pre (x, d, self, g) s0 ∗
        (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R) := by
      dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        kitTrustPollPlacedSpec, withEnvPre, IdKit.cliIdentityKitSpecPlaced]
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    refine ⟨(x, d, self, g), ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R, hpre', ?_, fun _ hpan => panic_absorb_extra_placed hpan⟩
    intro sf hpost
    dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE, kitTrustPollPlacedSpec,
      withEnvPre, IdKit.cliIdentityKitSpecPlaced, cliIdentityStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
      cliIdStoreAtFull] at hpost ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
    obtain ⟨ans, hm⟩ := hpost; exact ⟨ans, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm⟩
  savePoll hblk := by
    refine subroutine_ok_map_panic (hBase.savePoll hblk) ?_
    rintro ⟨x, self, g⟩ R s0 hpre; change IdGhost at g
    dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
      kitSavePollPlacedSpec, withEnvPre, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull] at hpre
    have hpre' : s0.mem ⊨ (withLsRoCl lsmpl (kitSavePollPlacedSpecI
        (IdKit.cliIdentityKitSpecPlaced A rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym))).pre (x, self, g) s0 ∗
        (⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R) := by
      dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        kitSavePollPlacedSpec, withEnvPre, IdKit.cliIdentityKitSpecPlaced]
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    refine ⟨(x, self, g), ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R, hpre', ?_, fun _ hpan => panic_absorb_extra_placed hpan⟩
    intro sf hpost
    dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE, kitSavePollPlacedSpec,
      withEnvPre, IdKit.cliIdentityKitSpecPlaced, cliIdentityStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
      cliIdStoreAtFull] at hpost ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
    obtain ⟨ans, hm⟩ := hpost; rw [saveUpd_own_placed]; exact ⟨ans, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm⟩

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

theorem cliGhostExterns_blackBox (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook :=
  (cliGhostExterns_other gh (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (CryptoVerification.SignalSession.Cli.RunGlue.cliExternsPlaced_row mmpl W
      (List.mem_append_right _ (List.mem_of_getElem? (i := 11) rfl)))

theorem cliSerContractsX_placed_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    Proofs.libsignal.Hooks2.SerContractsXPlaced E2E.HooksE.A0
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  Proofs.libsignal.Hooks2.SerContractsXPlaced.of_hooks
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    hh.codecHooks.realloc
    ((show CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec =
        CryptoVerification.LibsignalTripleRatchet.sessionShimSpec from rfl) ▸
      hh.codecHooks.shim)
    ⟨hookMemmove,
     (cliGhostExterns_other gh (cliExternsPlaced mmpl W)
       (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
       (cliExternsPlaced_memmove mmpl W),
     hookMemmove_trace_ok Proofs.libsignal.Stage1X.extHookStack⟩
    (by
      refine ProofLib.HookSat.mono hh.codecHooks.memcpy fun ⟨dst, src, bs⟩ R s0 hpre =>
        ⟨(dst, src, bs), stackAt s0.sp extHookStack ∗ R, ?_, fun sf hpost => ?_⟩
      · dsimp only [CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
          ProofLib.libcMemcpySpec,
          CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
          ProofLib.memcpyRegionSpec] at hpre ⊢
        ac_nf at hpre ⊢
      · dsimp only [CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
          CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hpost ⊢
        ac_nf at hpost ⊢)
    hh.codecHooks.panic_raw
    hh.codecHooks.panic_alloc

private theorem cliSerializeCanonX_placed_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      (CryptoVerification.E2E.Record.Placed.lsProg_52
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.serializeCanonSpecX E2E.HooksE.A0)) :=
  Store.SerGlueX.serializeCanonX_placed_ok_of_serContractsX (cliSerContractsX_placed_ok mmpl gh W hh)

private theorem stageP4MatchedBranchPlaced_of_matched [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {s0 s : State}
    {coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64}
    {opkHi kyberPreKeyId signedPreKeyId : BitVec 32} {pt : List (BitVec 8)}
    {peer : AddrGhost} {remoteIk : IdentityKey} {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {ss : Session (List (BitVec 8))} {sf : State} {Pf : SepProp}
    (h : Matched.StageP4MatchedBranchPlaced kit ikit encRecord s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt
      ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk sst0 ist0 ss sf Pf) :
    StageP4MatchedBranchPlaced kit ikit encRecord s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt
      ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk sst0 ist0 ss sf Pf := by
  cases h with
  | ok c hsave hstore htr hpost => exact .ok c hsave hstore htr hpost
  | saveErr hsave htr hpost => exact .saveErr hsave htr hpost
  | storeErr c hsave hstore htr hpost => exact .storeErr c hsave hstore htr hpost

/-- Instantiates `Poll.StageP4MatchedPlacedStmt` via `Matched.stageP4_matched_placed_ok`. -/
theorem stageP4Matched_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP4MatchedPlacedStmt := by
  intro mmpl gh W B F0 peer σ kit ikit hh hread hdeser
    s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId b_2c0 pt
    remoteIk sst0 ist0 g G ss hex hrec hka hia hpt1 hpt2 hpt3 hstk
    hfs hcro hpc hrun hsp htr hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  have hext : Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      cliGhostExterns gh (cliExternsPlaced mmpl W) := withPanics_cliGhostExterns_eq mmpl gh W
  have hdealloc : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec E2E.HooksE.A0) :=
    ls_hook_ok_ultra_of_mem hh.codecHooks.dealloc (by decide)
  have hDrop : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec E2E.HooksE.A0)) :=
    cliDropSessionStructure4_placed_ok_at mmpl gh W hh
      (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
  have hSkit : SessionOnlyKitPlacedOkSE kit Slots.scopeKit E2E.Record.encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    SessKit.cliSessKitOkSE_placed
      (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
      (deserProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (deserBlk := 518)
      (serProg := CryptoVerification.E2E.Record.Placed.lsProg_52
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) (serBlk := 52)
      hDropNz (fun _ hp => hp.2) hh
      (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hread)
      hdeser
      (cliSerializeCanonX_placed_ok mmpl gh W hh)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hSvt : SessionOnlyVtablesPlacedOk kit := cliPollSess_vtablesPlacedOk F0 Slots.scopeKit peer σ hDropNz
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
  have hwp0 := Matched.stageP4_matched_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Scope := Slots.scopeKit) (encRecord := E2E.Record.encodeRecord) kit ikit
  rw [hext] at hwp0
  have hwp := hwp0 hdealloc hDrop hSkit hSvt hIkit hIvt
    s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId b_2c0 pt
    peer remoteIk sst0 ist0 g G ss hex hrec hka hia hpt1 hpt2 hpt3 hstk
    hfs hcro hpc hrun hsp htr hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  intro R hm hL; obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL; refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc', hrun', Pf, hmm, hs1, hs2, hs3, hs4, hs5, hbr⟩ | hpan
  · exact Or.inl ⟨hpc', hrun', Pf, hmm, hs1, hs2, hs3, hs4, hs5, stageP4MatchedBranchPlaced_of_matched hbr⟩
  · exact Or.inr hpan

private theorem cliPollKpk_markShim_rocl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B)
    subroutine_ok callerProg (0#64 + kpkKit.markShimOff) (withLsRoCl lsmpl (kitKpkMarkShimSpec kpkKit)) := by
  intro kpkKit
  have h613 := Store.PkShims.kpkMarkShim_placed_ok_of_deps hh.alloc hh.panics
    (stk := (cliKitStk B).kpkMarkShim) (by dsimp [cliKitStk]; omega)
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 613)
    h613 hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 613) _; rw [BitVec.zero_add]
  refine subroutine_ok_map_panic hrocl fun x R s0 hp => ?_
  dsimp only [withLsRoCl, kitKpkMarkShimSpec, kpkKit, cliPollKpkKitPlaced,
    cliKpkStoreSpecFullPlaced, Poll.cliKyberPreKeyStoreSpecPlaced, cliKyberPreKeyStoreSpec, cliKpkStoreSpec] at hp ⊢
  have hp1 : s0.mem ⊨ ⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = x.self ∧
      s0.readReg32 .x1 = x.id ∧ s0.readReg32 .x2 = x.signedId ∧ s0.readReg64 .x3 = x.baseKeyA⌝ ∗
    (E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).kpkMarkShim ∗ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp
  rw [satisfies_pure_sepConj] at hp1
  have hp2 : s0.mem ⊨ ⌜s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id ∧
      s0.readReg32 .x2 = x.signedId ∧ s0.readReg64 .x3 = x.baseKeyA⌝ ∗
    (E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).kpkMarkShim ∗ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R) :=
    (satisfies_pure_sepConj ..).mpr ⟨hp1.1.2, hp1.2⟩
  refine ⟨⟨x.self, x.id, x.signedId, x.baseKeyA⟩, R, Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp2,
    fun sf hq => by simpa only [BitVec.zero_add] using hq, fun _ hpan => hpan⟩

private theorem cliPollKpk_markPoll_rocl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hread : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B)
    subroutine_ok callerProg (0#64 + kpkKit.markPollOff)
      (withLsRoCl lsmpl (kitKpkMarkPollSpecE kpkKit)) := by
  intro kpkKit
  have hDecimal := SessKit.cliDecimal_placed_ok hh
  have hGet := SessKit.cliDirGet_placed_ok
    (readProg := readProg) (jRead := jRead) (fun _ hp => hp.2) hh
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hread) hjRead hjRead_unmut
  have hPut := SessKit.cliDirPut_placed_ok hh
  have hhop := Store.KpkMarkPoll.kpkMarkPoll_placed_caller_ok_of_deps
    (callerProg := callerProg) (callerBlk := callerBlk)
    (decProg := lsProg_597 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decBlk := 597)
    (getProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (getBlk := 589)
    (putProg := lsProg_570 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (putBlk := 570)
    (stk := (cliKitStk B).kpkMarkPoll)
    hh.alloc hh.panics hh.bcmp hDecimal hGet hPut
    (hh.fs (lsProg_578 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 578) (Nat.le_refl _) hblk
  have hbase := subroutine_ok_rocl_of_withLsCodeRoLoaded
    (KitInst.cliKpkStoreSpecPlaced_markPoll (F0 := F0) (kid := kpkId) (ksid := spkId) (kbk := kbk)
      (cliKpkGetSide E2E.HooksE.A0 cliIo.rd F0 cliWrOk kpkId)
      (s1 := (cliKitStk B).kpkGetShim) (s2 := (cliKitStk B).kpkGetPoll)
      (s3 := (cliKitStk B).kpkMarkShim) pkBoxAt_memRegion kpkMarkBoxAt_memRegion hhop)
  change subroutine_ok callerProg (0#64 + lsmpl.base 578) _
  rw [BitVec.zero_add]
  refine subroutine_ok_map_panic hbase ?_
  rintro ⟨⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0⟩ R s0 hpre
  change KyberGhost at st0
  let baseKit := KitInst.cliKpkStoreSpecPlaced E2E.HooksE.A0 cliIo.rd F0 cliWrOk kpkId spkId kbk
    (cliKpkGetSide E2E.HooksE.A0 cliIo.rd F0 cliWrOk kpkId)
    (cliKitStk B).kpkGetShim (cliKitStk B).kpkGetPoll
    (cliKitStk B).kpkMarkShim (cliKitStk B).kpkMarkPoll pkBoxAt_memRegion kpkMarkBoxAt_memRegion
  dsimp only [withLsRoCl, kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec, kpkKit,
    cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, Poll.cliKyberPreKeyStoreSpecPlaced,
    cliKyberPreKeyStoreSpec, cliKpkStoreSpec, cliKpkStoreAtFull] at hpre
  have hp1 : s0.mem ⊨ ⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
      (kid' = kpkId ∧ ksid' = spkId ∧ kbk' = kbk)⌝ ∗
    (⌜CliKpkInvFull cliIo.rd F0 cliWrOk kpkId spkId kbk st0⌝ ∗
      (⌜s0.fs.files = F0⌝ ∗ kpkMarkBoxAt fut self baseKeyA kid' ksid' 0#8 ∗
        dirAt E2E.HooksE.A0 self st0.oneTime ∗ dirAt E2E.HooksE.A0 (self + 0x28#64) st0.lastResort ∗
        memRegion out 48 ∗ (baseKeyA ↦ₛ kbk'.bytes.toList) ∗ E2E.HooksE.A0.pool ∗
        stackAt s0.sp (cliKitStk B).kpkMarkPoll ∗ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R)) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hp1; obtain ⟨⟨hb0, hx0, hx8, rfl, rfl, rfl⟩, hp1⟩ := hp1
  rw [satisfies_pure_sepConj] at hp1; obtain ⟨hinv, hp1⟩ := hp1
  have hpre' : s0.mem ⊨ (withLsRoCl lsmpl (kitKpkMarkPollSpecE baseKit)).pre
      (⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0) s0 ∗ R := by
    dsimp only [withLsRoCl, kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec, baseKit,
      KitInst.cliKpkStoreSpecPlaced, cliKpkStoreSpec, cliKpkStoreAt]
    have hp2 : s0.mem ⊨ ⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        (kid' = kid' ∧ ksid' = ksid' ∧ kbk' = kbk')⌝ ∗
      (⌜CliKpkInv cliIo.rd F0 cliWrOk kid' ksid' kbk' st0⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗ kpkMarkBoxAt fut self baseKeyA kid' ksid' 0#8 ∗
          dirAt E2E.HooksE.A0 self st0.oneTime ∗ dirAt E2E.HooksE.A0 (self + 0x28#64) st0.lastResort ∗
          memRegion out 48 ∗ (baseKeyA ↦ₛ kbk'.bytes.toList) ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp (cliKitStk B).kpkMarkPoll ∗ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R)) :=
      (satisfies_pure_sepConj ..).mpr ⟨⟨hb0, hx0, hx8, rfl, rfl, rfl⟩,
        (satisfies_pure_sepConj ..).mpr ⟨hinv.markInv, hp1⟩⟩
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp2
  refine ⟨(⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0), R, hpre', ?_, fun _ hpan => hpan⟩
  intro sf hpost
  dsimp only [withLsRoCl, kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec, kpkKit, baseKit,
    cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, Poll.cliKyberPreKeyStoreSpecPlaced,
    KitInst.cliKpkStoreSpecPlaced, cliKyberPreKeyStoreSpec, cliKpkStoreSpec,
    cliKpkStoreAtFull, cliKpkStoreAt, kpkMarkPollOutAt] at hpost ⊢
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
  let relProp (a : Except CliKpkMarkErr Unit) : Prop :=
    match a with
    | .ok () => (kpkMarkOf cliIo.rd F0 st0 kid' ksid' kbk').1 = .ok
    | .error e => (kpkMarkOf cliIo.rd F0 st0 kid' ksid' kbk').1 = e.ans
  obtain ⟨ans, hm⟩ := hpost; refine ⟨ans, ?_⟩
  have hm1 : sf.mem ⊨ ⌜CliKpkInv cliIo.rd F0 cliWrOk kid' ksid' kbk'
      (kpkMarkOf cliIo.rd F0 st0 kid' ksid' kbk').2⌝ ∗
    (⌜StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗ ⌜relProp ans ∧ sf.trace = s0.trace ++ []⌝ ∗
      kpkMarkBoxAt fut self baseKeyA kid' ksid' 1#8 ∗
      dirAt E2E.HooksE.A0 self (kpkMarkOf cliIo.rd F0 st0 kid' ksid' kbk').2.oneTime ∗
      dirAt E2E.HooksE.A0 (self + 0x28#64) (kpkMarkOf cliIo.rd F0 st0 kid' ksid' kbk').2.lastResort ∗
      unitSpePollOutAt (cliKpkMarkErrSpec E2E.HooksE.A0) out ans ∗
      (baseKeyA ↦ₛ kbk'.bytes.toList) ∗ E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).kpkMarkPoll ∗ R) :=
    Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [relProp]; ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  exact Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [relProp]; ac_rfl))
    ((satisfies_pure_sepConj ..).mpr ⟨hinv.mark, hm1.2⟩)

theorem cliPollKpk_markKitPlacedOk [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey) (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hread : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    KyberPreKeyMarkKitPlacedOk
      (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  markShim hblk := cliPollKpk_markShim_rocl mmpl gh W B F0 kpkId spkId kbk hh hblk
  markPoll hblk := cliPollKpk_markPoll_rocl mmpl gh W B F0 kpkId spkId kbk hh hread hjRead hjRead_unmut hblk
  markFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]; exact IdKit.cliIdFutDrop_rocl_placed_ok hblk

private theorem cliPollPk_removeShim_rocl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (pkId : BitVec 32)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 F0 pkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + pkKit.removeShimOff)
      (withLsRoCl lsmpl (kitPreKeyRemoveShimSpec pkKit)) := by
  intro pkKit
  have h610 := Store.PkShims.pkRemoveShim_placed_ok_of_deps hh.alloc hh.panics
    (stk := (cliKitStk B).pkRemoveShim) (by dsimp [cliKitStk]; omega)
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 610)
    h610 hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 610) _; rw [BitVec.zero_add]
  refine subroutine_ok_map_panic hrocl fun x R s0 hp => ?_
  dsimp only [withLsRoCl, kitPreKeyRemoveShimSpec, pkKit, cliPollPkKitPlaced,
    Poll.cliPreKeyStoreSpecPlaced, cliPreKeyStoreSpec] at hp ⊢
  have hp1 : s0.mem ⊨ ⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id⌝ ∗
    (E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).pkRemoveShim ∗
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R) := Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp
  rw [satisfies_pure_sepConj] at hp1
  have hp2 : s0.mem ⊨ ⌜s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id⌝ ∗
    (E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).pkRemoveShim ∗
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R) := (satisfies_pure_sepConj ..).mpr ⟨hp1.1.2, hp1.2⟩
  refine ⟨⟨x.self, x.id⟩, R, Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp2, fun sf hq => ?_, fun _ hpan => hpan⟩
  simpa only [BitVec.zero_add] using hq

section LocalPkRemovePoll
open Arm64.Obj CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers
attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero calleeSavedVRegs_writeVReg128_0 setWidth_32_setWidth_64
  extractLsb_0_64_append_p extractLsb_64_64_append_p setWidth_64_append_p
  Store.PkRemovePoll.Helpers.fs_setPC Store.PkRemovePoll.Helpers.fs_advancePC
  Store.PkRemovePoll.Helpers.fs_setMem Store.PkRemovePoll.Helpers.fs_setPState
  Store.PkRemovePoll.Helpers.fs_writeReg64 Store.PkRemovePoll.Helpers.fs_writeReg32
  Store.PkRemovePoll.Helpers.fs_writeReg Store.PkRemovePoll.Helpers.fs_writeVReg128
  Store.PkRemovePoll.Helpers.fs_applyWriteback

private theorem sepWP_to_sepWPp_local {prog : Program} {ret mid : BitVec 64} {s : State}
    {pl : MultiPlacement} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm P_m => StoreKit.LibsignalCodeRoLoaded pl sm.mem → SepWPp prog ret sm P_m Q Qp)) :
    SepWPp prog ret s P Q Qp := StoreKit.sepWPp_seq_lscro hcrl h

private theorem pkrm_post_entails_local [LibsignalPlacement] (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustAlloc) (stk : Nat)
    (x : PkPollGhost) (s0 sf : State) (res : Except Unit Unit × DirGhost)
    (hres : res = pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧ sf.trace = s0.trace) :
    (pkRemoveOutAt A x.out res.1 ∗ dirAt A x.self res.2 ∗ pkBoxAt x.fut x.self x.id 1#8 ∗ A.pool ∗ stackAt s0.sp stk) ⊢
      (pkRemovePollSpecPlaced rd pathOk A stk).post x s0 sf := by
  simp only [pkRemovePollSpecPlaced, StoreKit.withLsCodeRoLoaded, sepExists_sepConj_left, sepConj_assoc]
  exact Entails.sepExists_right res (Entails.pure_right hres (Entails.refl _))

set_option maxHeartbeats 400000 in
private theorem pkrm_branch_err_local [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H) (x : PkPollGhost) (R : SepProp) (s0 sm2 : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8)) (q_sp0 : BitVec 128)
    (hstk : pollMinStk decStk getStk putStk ≤ stk) (hstk_hi : stk ≤ 2 ^ 64)
    (hnlen : nameBs.length ≤ nameCap.toNat) (hnlt : nameCap.toNat < 2 ^ 63) (_hnptr : namePtr ≠ 0#64)
    (hgr : Except.error () = x.dir.get rd s0.fs.files (keyName x.id) ∧ sm2.trace = s0.trace)
    (hpc : sm2.pc = (blkPl_575).base + 88#64) (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64) (hsp : sm2.sp = s0.sp - 0xc0#64)
    (hfp : sm2.readReg64 .x29 = s0.sp - 0x60#64) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl sm2.mem)
    (hx28 : sm2.readReg64 .x28 = s0.readReg64 .x28) (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.fut) (hx20 : sm2.readReg64 .x20 = x.out) (hx21 : sm2.readReg64 .x21 = namePtr) :
    SepWP ((blkPC_575).rebase (blkPl_575).base H) (s0.readReg64 Reg.lr) sm2
      (getResultAt A (s0.sp - 0xa8#64) (.error ()) ∗ postGetCommon_placed A s0 x decStk getStk putStk stk nameCap namePtr nameBs q_sp0)
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A stk).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_c0 hsp_align hsp
  have hmin_hi : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hext_le : extHookStack ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hne : (speWord 1 + 2#64 == 0#64) = false := speWord_one_add_two_ne_zero
  have hep := @pkrm_epilogue_108_placed _ H; unfold postGetCommon_placed
  change SepWP _ _ _ (speAt A (utf8 "read") (s0.sp - 0xa8#64) .invalidState ∗ _) _
  rw [speAt_read_invalidState_eq A (s0.sp - 0xa8#64) (s0.sp - 0xa0#64) (s0.sp - 0x98#64)
        (s0.sp - 0x90#64) (s0.sp - 0x88#64) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega),
      subStack_split s0.sp hext_le hmin_hi]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun errBs => SepWP.exists_elim fun errCap =>
    SepWP.exists_elim fun errPtr => SepWP.exists_elim fun fnPtr => ?_
  let q_err : BitVec 128 := BitVec.ofNat 64 (utf8 "read").length ++ fnPtr
  let F_err : SepProp :=
    ((s0.sp - 0xa8#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0xa0#64) ↦₆₄ errCap) ∗ ((s0.sp - 0x98#64) ↦₆₄ errPtr) ∗
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗ ((s0.sp - 0x88#64) ↦₁₂₈ q_err) ∗
    speReadHeap A errBs errCap errPtr fnPtr ∗ ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗ dirAt A x.self x.dir
  have hdone : ∀ (sf : State) (P_f : SepProp), sf.trace = sm2.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err ∗
        stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_err) →
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hres_f : (Except.error (), x.dir) = pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        sf.trace = s0.trace := ⟨by rw [← hgr.1]; rfl, htr_eq.trans hgr.2⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf (Entails.trans ?_ (pkrm_post_entails_local rd pathOk A stk x s0 sf (.error (), x.dir) hres_f))
    refine Entails.trans ?_ (finish_common_reassemble_placed A s0 x hstk hstk_hi (.error (), x.dir) q_err)
    have hout := speAt_read_invalidState_intro A x.out errBs errCap errPtr fnPtr
    have hslot := slot_a8_err_collapse s0.sp (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err
    have h24 := header3_entails_memRegion24 (s0.sp - 0x78#64) (s0.sp - 0x70#64) (s0.sp - 0x68#64)
      nameCap namePtr (BitVec.ofNat 64 nameBs.length) (by bv_omega) (by bv_omega)
    have hgrp : epilogueOut s0 x (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err ∗
        stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_err =
      (((x.out ↦₆₄ speWord 1) ∗ ((x.out + 8#64) ↦₆₄ errCap) ∗ ((x.out + 0x10#64) ↦₆₄ errPtr) ∗
          ((x.out + 0x18#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗ ((x.out + 0x20#64) ↦₁₂₈ q_err) ∗
          speReadHeap A errBs errCap errPtr fnPtr) ∗
        (((s0.sp - 0xa8#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0xa0#64) ↦₆₄ errCap) ∗ ((s0.sp - 0x98#64) ↦₆₄ errPtr) ∗
          ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗ ((s0.sp - 0x88#64) ↦₁₂₈ q_err)) ∗
        (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
        (dirAt A x.self x.dir ∗ ((s0.sp - 0xc0#64) ↦₁₂₈ q_err) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗ savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗ A.pool)) := by unfold epilogueOut F_err q_err; ac_rfl
    rw [hgrp]; exact Entails.trans (sepConj_mono hout (sepConj_mono hslot (sepConj_mono_left h24))) (Entails.of_eq (by ac_rfl))
  have hb8 : s0.sp - 0xc0#64 + 8#64 = s0.sp - 184#64 := by bv_omega
  have h80 : s0.sp - 0x88#64 + 8#64 = s0.sp - 128#64 := by bv_omega
  unfold Arm64.pointsTo128; simp only [hb8, h80, extractLsb_0_64_append_p, extractLsb_64_64_append_p, sepConj_assoc]
  by_cases hncap : nameCap = 0#64
  · subst hncap; refine SepWP.fold (vecU8_free_zero A namePtr hnlen) (by sep_focus) ?_
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_575).base + 264#64) hcrl; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs); intro _hcrl_108
    refine hep x s0 _ (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err _
      (stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_err)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hsp_align
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by unfold epiloguePre F_err q_err Arm64.pointsTo128
          simp only [hb8, h80, extractLsb_0_64_append_p, extractLsb_64_64_append_p, sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf => hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
        (Entails.trans hPf (Entails.of_eq (by ac_rfl)))
  · obtain ⟨hcap_pos, hpow1, hcap_hi⟩ := layoutOk_u8_of_ne_zero hncap hnlt
    have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
    refine SepWP.fold (vecU8_free_ne A (ptr := namePtr) hncap hnlen hnlt) (by sep_focus) ?_
    apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs); intro hcrl_da
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_575).base + 220#64) hcrl_da
    wp_call_lscro (pkrm_dealloc_placed_ok hC) hcrl_da (namePtr, nameCap.toNat, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcrl_dc
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_575).base + 264#64) hcrl_dc; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs); intro _hcrl_108
    refine hep x s0 _ (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err _
      (stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_err)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hsp_align
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by unfold epiloguePre F_err q_err Arm64.pointsTo128
          simp only [hsp, hb8, h80, extractLsb_0_64_append_p, extractLsb_64_64_append_p, sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf => hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
        (Entails.trans hPf (Entails.of_eq (by ac_rfl)))

set_option maxHeartbeats 400000 in
private theorem pkrm_branch_ok_nil_local [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H) (x : PkPollGhost) (R : SepProp) (s0 sm2 : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8)) (q_sp0 : BitVec 128)
    (hstk : pollMinStk decStk getStk putStk ≤ stk) (hstk_hi : stk ≤ 2 ^ 64)
    (hnlen : nameBs.length ≤ nameCap.toNat) (hnlt : nameCap.toNat < 2 ^ 63) (hnptr : namePtr ≠ 0#64)
    (hgr : Except.ok ([] : List (BitVec 8)) = x.dir.get rd s0.fs.files (keyName x.id) ∧ sm2.trace = s0.trace)
    (hpc : sm2.pc = (blkPl_575).base + 88#64) (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64) (hsp : sm2.sp = s0.sp - 0xc0#64)
    (hfp : sm2.readReg64 .x29 = s0.sp - 0x60#64) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl sm2.mem)
    (hx28 : sm2.readReg64 .x28 = s0.readReg64 .x28) (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.fut) (hx20 : sm2.readReg64 .x20 = x.out) (hx21 : sm2.readReg64 .x21 = namePtr) :
    SepWP ((blkPC_575).rebase (blkPl_575).base H) (s0.readReg64 Reg.lr) sm2
      (getResultAt A (s0.sp - 0xa8#64) (.ok []) ∗ postGetCommon_placed A s0 x decStk getStk putStk stk nameCap namePtr nameBs q_sp0)
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A stk).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_c0 hsp_align hsp
  have hmin_hi : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hext_le : extHookStack ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hok_tag : (okTagVec + 2#64 == 0#64) = true := okTagVec_add_two_eq_zero
  have hff4 := pkrm_finish_f4_placed hC; unfold postGetCommon_placed
  rw [getResultAt_ok_unpack_placed A s0.sp [], subStack_split s0.sp hext_le hmin_hi]
  simp only [List.length_nil, sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun bytesCap => SepWP.exists_elim fun bytesPtr =>
    SepWP.pure_elim fun ⟨_hblen, hblt, _hbptr⟩ => ?_
  let F_nil : SepProp :=
    ((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗ ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
    ((s0.sp - 0x90#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0x88#64) 16 ∗ ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗ dirAt A x.self x.dir
  have hdone : ∀ (sf : State) (P_f : SepProp), sf.trace = sm2.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x okTagVec bytesCap bytesPtr 0#64 q_sp0 ∗
        ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_nil) →
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hres_f : (Except.ok (), x.dir) = pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        sf.trace = s0.trace := ⟨by rw [← hgr.1]; rfl, htr_eq.trans hgr.2⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf (Entails.trans ?_ (pkrm_post_entails_local rd pathOk A stk x s0 sf (.ok (), x.dir) hres_f))
    refine Entails.trans ?_ (finish_common_reassemble_placed A s0 x hstk hstk_hi (.ok (), x.dir) q_sp0)
    have hok := pkRemoveOutAt_ok_reassemble A x.out bytesCap bytesPtr 0#64 q_sp0
    have hslot := slot_a8_ok_collapse s0.sp okTagVec bytesCap bytesPtr 0#64
    have h24 := header3_entails_memRegion24 (s0.sp - 0x78#64) (s0.sp - 0x70#64) (s0.sp - 0x68#64)
      nameCap namePtr (BitVec.ofNat 64 nameBs.length) (by bv_omega) (by bv_omega)
    have hgrp : epilogueOut s0 x okTagVec bytesCap bytesPtr 0#64 q_sp0 ∗
        ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_nil =
      (((x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((x.out + 8#64) ↦₆₄ bytesCap) ∗ ((x.out + 0x10#64) ↦₆₄ bytesPtr) ∗
          ((x.out + 0x18#64) ↦₆₄ 0#64) ∗ ((x.out + 0x20#64) ↦₁₂₈ q_sp0)) ∗
        (((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗ ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
          ((s0.sp - 0x90#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0x88#64) 16) ∗
        (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
        (dirAt A x.self x.dir ∗ ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗ savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗ A.pool)) := by unfold epilogueOut F_nil okTagVec; ac_rfl
    rw [hgrp]; exact Entails.trans (sepConj_mono hok (sepConj_mono hslot (sepConj_mono_left h24))) (Entails.of_eq (by ac_rfl))
  by_cases hbcap : bytesCap = 0#64
  · subst hbcap; refine SepWP.fold (vecU8_free_zero A bytesPtr (bs := []) (Nat.zero_le _)) (by sep_focus) ?_
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_575).base + 244#64) hcrl; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs); intro hcrl_f4
    refine hff4 x s0 _ nameCap namePtr nameBs okTagVec 0#64 bytesPtr 0#64 q_sp0 _ F_nil
      hnlen hnlt hnptr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hsp_align
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcrl_f4
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by unfold epiloguePre F_nil; simp only [sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf => hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf
  · obtain ⟨hb_pos, hb_pow1, hb_hi⟩ := layoutOk_u8_of_ne_zero hbcap hblt
    have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
    refine SepWP.fold (vecU8_free_ne A (ptr := bytesPtr) hbcap (Nat.zero_le _) hblt) (by sep_focus) ?_
    apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs); intro hcrl_da
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_575).base + 244#64) hcrl_da
    wp_call_lscro (pkrm_dealloc_placed_ok hC) hcrl_da (bytesPtr, bytesCap.toNat, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcrl_f4
    refine hff4 x s0 _ nameCap namePtr nameBs okTagVec bytesCap bytesPtr 0#64 q_sp0 _ F_nil
      hnlen hnlt hnptr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hsp_align
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcrl_f4
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by unfold epiloguePre F_nil; simp only [hsp, sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf => hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf

set_option maxHeartbeats 400000 in
private theorem pkrm_branch_ok_cons_local [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hDec : subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hPut : subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (lsmpl.base 542) (dirPutSpecPlaced A putStk))
    (x : PkPollGhost) (R : SepProp) (s0 sm2 : State) (b0 : BitVec 8) (bsRest : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8)) (q_sp0 : BitVec 128)
    (hstk : pollMinStk decStk getStk putStk ≤ stk) (hstk_hi : stk ≤ 2 ^ 64) (hdchg : x.dir.changed.length < 2 ^ 32)
    (hnlen : nameBs.length ≤ nameCap.toNat) (hnlt : nameCap.toNat < 2 ^ 63) (hnptr : namePtr ≠ 0#64)
    (hgr : Except.ok (b0 :: bsRest) = x.dir.get rd s0.fs.files (keyName x.id) ∧ sm2.trace = s0.trace)
    (hpc : sm2.pc = (blkPl_575).base + 88#64) (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64) (hsp : sm2.sp = s0.sp - 0xc0#64)
    (hfp : sm2.readReg64 .x29 = s0.sp - 0x60#64) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl sm2.mem)
    (hx28 : sm2.readReg64 .x28 = s0.readReg64 .x28) (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.fut) (hx20 : sm2.readReg64 .x20 = x.out)
    (hx21 : sm2.readReg64 .x21 = namePtr) (hx22 : sm2.readReg64 .x22 = x.self)
    (hx23 : sm2.readReg64 .x23 = BitVec.setWidth 64 x.id) :
    SepWPp ((blkPC_575).rebase (blkPl_575).base H) (s0.readReg64 Reg.lr) sm2
      (getResultAt A (s0.sp - 0xa8#64) (.ok (b0 :: bsRest)) ∗ postGetCommon_placed A s0 x decStk getStk putStk stk nameCap namePtr nameBs q_sp0)
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A stk).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A stk).onPanic x s0 sf ∗ R)) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_c0 hsp_align hsp
  have hmin_hi : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hdec_le : decStk ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hput_le : putStk ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hext_le : extHookStack ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hok_tag : (okTagVec + 2#64 == 0#64) = true := okTagVec_add_two_eq_zero
  have hpan_fn : ∀ (sf : State) (P_f : SepProp), (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) →
      (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A stk).onPanic x s0 sf ∗ R) := by
    intro sf P_f halloc hmf; dsimp only [pkRemovePollSpecPlaced, StoreKit.withLsCodeRoLoaded]
    simpa only [sepConj_assoc] using allowPanic_panicked halloc hmf
  have hdb6c := @pkrm_drop_both_6c_placed _ A H hC; have hep := @pkrm_epilogue_108_placed _ H; clear hC
  unfold postGetCommon_placed; rw [getResultAt_ok_unpack_placed A s0.sp (b0 :: bsRest), subStack_split s0.sp hext_le hmin_hi]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bytesCap => SepWPp.exists_elim fun bytesPtr =>
    SepWPp.pure_elim fun ⟨hblen, hblt, hbptr⟩ => ?_
  have hbcap : bytesCap ≠ 0#64 := by intro hc; subst hc; simp at hblen
  have hlen_beq : (BitVec.ofNat 64 (b0 :: bsRest).length == 0#64) = false := by
    apply beq_eq_false_iff_ne.mpr; intro heq; have h1 := congrArg BitVec.toNat heq
    have h2 : bsRest.length + 1 < 2 ^ 64 := by have : (b0 :: bsRest).length = bsRest.length + 1 := rfl; omega
    simp only [List.length_cons, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2] at h1; exact Nat.succ_ne_zero _ h1
  let F_drop : SepProp :=
    ((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗ ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗ memRegion (s0.sp - 0x88#64) 16 ∗
    ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗ ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗ savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion x.out 48 ∗ pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.dir
  apply sepWP_to_sepWPp_local (mid := (blkPl_575).base + 148#64) hcrl
  apply StoreKit.sepWP_seq_lscro (mid := (blkPl_575).base + 108#64) hcrl; wp_steps; let _ := hlen_beq
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs); intro hcrl_6c
  refine hdb6c s0 _ bytesCap bytesPtr (b0 :: bsRest) nameCap namePtr nameBs _ F_drop
    hbcap hblen hblt hbptr hnlen hnlt hnptr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hsp_align
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcrl_6c
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by unfold F_drop; sep_focus)
    fun sm3 hpcm3 hrunm3 hspm3 _hcrlm3 htrm3 hx19_3 hx20_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3 => ?_
  apply SepWP.done hpcm3 (by wp_norm_lhs); intro hcrlm3
  have hx19_m3 : sm3.readReg64 .x19 = x.fut := hx19_3.trans (by simp only [arm64_norm, *])
  have hx20_m3 : sm3.readReg64 .x20 = x.out := hx20_3.trans (by simp only [arm64_norm, *])
  have hx22_m3 : sm3.readReg64 .x22 = x.self := hx22_3.trans (by simp only [arm64_norm, *])
  have hx23_m3 : sm3.readReg64 .x23 = BitVec.setWidth 64 x.id := hx23_3.trans (by simp only [arm64_norm, *])
  have hx24_m3 : sm3.readReg64 .x24 = bytesCap := hx24_3
  have hx25_m3 : sm3.readReg64 .x25 = bytesPtr := hx25_3
  have hx26_m3 : sm3.readReg64 .x26 = okTagVec := hx26_3.trans (by simp only [arm64_norm, *])
  have hx27_m3 : sm3.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length := hx27_3.trans (by simp only [arm64_norm, *])
  have htr_m3 : sm3.trace = s0.trace := htrm3.trans (by simp only [hgr.2, arm64_norm, *])
  have hsp_al3 : sm3.spAligned = true := spAligned_sub_c0 hsp_align hspm3
  clear htrm3 hx19_3 hx20_3 hx22_3 hx23_3 hx26_3 hx27_3 hdb6c
  have hrestk_dec :
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - extHookStack) ∗
        stackAt (s0.sp - 0xc0#64) extHookStack =
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - decStk) ∗
        stackAt (s0.sp - 0xc0#64) decStk := by
    rw [← subStack_split s0.sp hext_le hmin_hi, subStack_split s0.sp hdec_le hmin_hi]
  have h24_name := header3_entails_memRegion24 (s0.sp - 0x78#64) (s0.sp - 0x70#64) (s0.sp - 0x68#64)
    nameCap namePtr (BitVec.ofNat 64 nameBs.length) (by bv_omega) (by bv_omega)
  let F_dec2 : SepProp :=
    ((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗ ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗ memRegion (s0.sp - 0x88#64) 16 ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗ savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - decStk) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion x.out 48 ∗ pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.dir
  have hprep_dec : (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_drop) ⊢
      (memRegion (s0.sp - 0x78#64) 24 ∗ stackAt (s0.sp - 0xc0#64) decStk ∗ A.pool) ∗ F_dec2 := by
    have hpull : (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_drop) =
      ((((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗ ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
        (memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack) ∗ A.pool ∗
        (((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗ ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
          ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗ memRegion (s0.sp - 0x88#64) 16 ∗
          ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗ savedCalleeSlots s0 ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          memRegion x.out 48 ∗ pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.dir)) := by unfold F_drop; ac_rfl
    rw [hpull, hrestk_dec]; refine Entails.trans (sepConj_mono_left h24_name) ?_; unfold F_dec2; exact Entails.of_eq (by ac_rfl)
  refine sepWPp_conseq hprep_dec ?_
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 597) hcrlm3; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs); intro hcrl_dec2
  refine sepWPp_name_state_placed fun s4 hs4 => ?_
  have hs4_pc : s4.pc = lsmpl.base 597 := by rw [hs4]; simp only [wp_norm, arm64_norm, *]; try bv_omega
  have hs4_lr : s4.readReg64 Reg.lr = (blkPl_575).base + 160#64 := by rw [hs4]; simp only [wp_norm, arm64_norm, *]
  have hs4_run : s4.status = .Running := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_sp : s4.sp = s0.sp - 0xc0#64 := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_tr : s4.trace = s0.trace := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x0 : s4.readReg64 .x0 = s0.sp - 0x78#64 := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x1 : s4.readReg32 .x1 = x.id := by rw [hs4]; simp only [arm64_norm, *]
  rw [← hs4] at hcrl_dec2
  refine pkrm_call_decimal_placed hDec { n := x.id, ret := s0.sp - 0x78#64 } F_dec2 (s0 := s0)
    hs4_pc hs4_run (spAligned_sub_c0 hsp_align hs4_sp) hs4_lr hs4_tr hcrl_dec2
    hs4_x0 hs4_x1 hpan_fn (Entails.of_eq (by rw [hs4_sp])) fun sm4 hpcm4 hrunm4 hspm4 hcsm4 hcrlm4 htrm4 => ?_
  rw [hs4_sp]
  obtain ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hfp_4, hvregs_4⟩ := hcsm4
  have hsp_m4 : sm4.sp = s0.sp - 0xc0#64 := hspm4.trans hs4_sp
  have hsp_al4 : sm4.spAligned = true := spAligned_sub_c0 hsp_align hsp_m4
  have hx19_m4 : sm4.readReg64 .x19 = x.fut := hx19_4.trans (by rw [hs4]; simp only [arm64_norm, *])
  have hx20_m4 : sm4.readReg64 .x20 = x.out := hx20_4.trans (by rw [hs4]; simp only [arm64_norm, *])
  have hx22_m4 : sm4.readReg64 .x22 = x.self := hx22_4.trans (by rw [hs4]; simp only [arm64_norm, *])
  have hx24_m4 : sm4.readReg64 .x24 = bytesCap := hx24_4.trans (by rw [hs4]; simp only [arm64_norm, *])
  have hx25_m4 : sm4.readReg64 .x25 = bytesPtr := hx25_4.trans (by rw [hs4]; simp only [arm64_norm, *])
  have hx26_m4 : sm4.readReg64 .x26 = okTagVec := hx26_4.trans (by rw [hs4]; simp only [arm64_norm, *])
  have hx27_m4 : sm4.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length := hx27_4.trans (by rw [hs4]; simp only [arm64_norm, *])
  have hx28_m4 : sm4.readReg64 .x28 = s0.readReg64 .x28 := hx28_4.trans (by rw [hs4]; simp only [arm64_norm, *])
  have hfp_m4 : sm4.readReg64 .x29 = s0.sp - 0x60#64 := hfp_4.trans (by rw [hs4]; simp only [arm64_norm, *])
  have hvregs_m4 : calleeSavedVRegs sm4 = calleeSavedVRegs s0 := hvregs_4.trans (by rw [hs4]; simp only [arm64_norm, *])
  have htr_m4 : sm4.trace = s0.trace := htrm4.trans hs4_tr
  clear hs4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hfp_4 hvregs_4
  have hrestk_put :
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - decStk) ∗
        stackAt (s0.sp - 0xc0#64) decStk =
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - putStk) ∗
        stackAt (s0.sp - 0xc0#64) putStk := by
    rw [← subStack_split s0.sp hdec_le hmin_hi, subStack_split s0.sp hput_le hmin_hi]
  unfold F_dec2
  refine sepWPp_conseq (P' := ((memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - decStk) ∗ stackAt (s0.sp - 0xc0#64) decStk) ∗
      ((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗ ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
      vecU8 A (s0.sp - 0x78#64) (keyName x.id) ∗ dirAt A x.self x.dir ∗ A.pool ∗
      ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗ memRegion (s0.sp - 0x88#64) 16 ∗
      ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗ savedCalleeSlots s0 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
      memRegion x.out 48 ∗ pkBoxAt x.fut x.self x.id 0#8)) (Entails.of_eq (by unfold keyName; ac_rfl)) ?_
  rw [hrestk_put]; simp only [sepConj_assoc]
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 542) hcrlm4; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs); intro hcrl_put
  refine sepWPp_name_state_placed fun s5 hs5 => ?_
  have hs5_pc : s5.pc = lsmpl.base 542 := by rw [hs5]; simp only [wp_norm, arm64_norm, *]; try bv_omega
  have hs5_lr : s5.readReg64 Reg.lr = (blkPl_575).base + 188#64 := by rw [hs5]; simp only [wp_norm, arm64_norm, *]
  have hs5_run : s5.status = .Running := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_sp : s5.sp = s0.sp - 0xc0#64 := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_tr : s5.trace = s0.trace := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x0 : s5.readReg64 .x0 = x.self := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x1 : s5.readReg64 .x1 = s0.sp - 0x78#64 := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x2 : s5.readReg64 .x2 = s0.sp - 0xa8#64 := by rw [hs5]; simp only [arm64_norm, *]
  rw [← hs5] at hcrl_put
  let F_put : SepProp :=
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗ memRegion (s0.sp - 0x88#64) 16 ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗ savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - putStk) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗ memRegion x.out 48 ∗ pkBoxAt x.fut x.self x.id 0#8
  refine pkrm_call_dirPut_placed hPut
    { self := x.self, dir := x.dir, nameV := s0.sp - 0x78#64, name := keyName x.id, bytesV := s0.sp - 0xa8#64, bytes := [] } F_put (s0 := s0)
    hs5_pc hs5_run (spAligned_sub_c0 hsp_align hs5_sp) hs5_lr hs5_tr hcrl_put hs5_x0 hs5_x1 hs5_x2 hdchg hpan_fn
    (by rw [hs5_sp]
        have hemp_v := vecU8_empty_of_zero_one_zero A (s0.sp - 0xa8#64) (s0.sp - 0xa0#64) (s0.sp - 0x98#64) (by bv_omega) (by bv_omega)
        refine Entails.trans (Q := (((s0.sp - 0xa8#64) ↦₆₄ 0#64) ∗ ((s0.sp - 0xa0#64) ↦₆₄ 1#64) ∗ ((s0.sp - 0x98#64) ↦₆₄ 0#64)) ∗
          (dirAt A x.self x.dir ∗ vecU8 A (s0.sp - 0x78#64) (keyName x.id) ∗ stackAt (s0.sp - 0xc0#64) putStk ∗ A.pool ∗ F_put))
          (Entails.of_eq (by unfold F_put; ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hemp_v) (Entails.of_eq (by dsimp only; ac_rfl)))
    fun sm5 hpcm5 hrunm5 hspm5 hcsm5 hcrlm5 htrm5 => ?_
  rw [hs5_sp]
  obtain ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hfp_5, hvregs_5⟩ := hcsm5
  have hsp_m5 : sm5.sp = s0.sp - 0xc0#64 := hspm5.trans hs5_sp
  have hx19_m5 : sm5.readReg64 .x19 = x.fut := hx19_5.trans (by rw [hs5]; simp only [arm64_norm, *])
  have hx20_m5 : sm5.readReg64 .x20 = x.out := hx20_5.trans (by rw [hs5]; simp only [arm64_norm, *])
  have hx24_m5 : sm5.readReg64 .x24 = bytesCap := hx24_5.trans (by rw [hs5]; simp only [arm64_norm, *])
  have hx25_m5 : sm5.readReg64 .x25 = bytesPtr := hx25_5.trans (by rw [hs5]; simp only [arm64_norm, *])
  have hx26_m5 : sm5.readReg64 .x26 = okTagVec := hx26_5.trans (by rw [hs5]; simp only [arm64_norm, *])
  have hx27_m5 : sm5.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length := hx27_5.trans (by rw [hs5]; simp only [arm64_norm, *])
  have hx28_m5 : sm5.readReg64 .x28 = s0.readReg64 .x28 := hx28_5.trans (by rw [hs5]; simp only [arm64_norm, *])
  have hvregs_m5 : calleeSavedVRegs sm5 = calleeSavedVRegs s0 := hvregs_5.trans (by rw [hs5]; simp only [arm64_norm, *])
  have htr_m5 : sm5.trace = s0.trace := htrm5.trans hs5_tr
  clear hs5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hfp_5 hvregs_5; apply sepWPp_of_sepWP_final_placed
  have hrestk_ext :
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - putStk) ∗
        stackAt (s0.sp - 0xc0#64) putStk =
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - extHookStack) ∗
        stackAt (s0.sp - 0xc0#64) extHookStack := by
    rw [← subStack_split s0.sp hput_le hmin_hi, subStack_split s0.sp hext_le hmin_hi]
  let F_end : SepProp :=
    dirAt A x.self (x.dir.put (keyName x.id) []) ∗ memRegion (s0.sp - 0x78#64) 24 ∗ memRegion (s0.sp - 0xa8#64) 24 ∗
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗ memRegion (s0.sp - 0x88#64) 16 ∗ memRegion (s0.sp - 0xb0#64) 8 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - extHookStack) ∗
    stackAt (s0.sp - 0xc0#64) extHookStack ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗ A.pool
  have hdone : ∀ (sf : State) (P_f : SepProp), sf.trace = s0.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x okTagVec bytesCap bytesPtr (BitVec.ofNat 64 (b0 :: bsRest).length) q_sp0 ∗ F_end) →
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hres_f : (Except.ok (), x.dir.put (keyName x.id) []) =
        pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧ sf.trace = s0.trace := ⟨by rw [← hgr.1]; rfl, htr_eq⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf (Entails.trans ?_
      (pkrm_post_entails_local rd pathOk A stk x s0 sf (.ok (), x.dir.put (keyName x.id) []) hres_f))
    refine Entails.trans ?_ (finish_common_reassemble_placed A s0 x hstk hstk_hi (.ok (), x.dir.put (keyName x.id) []) q_sp0)
    have hok := pkRemoveOutAt_ok_reassemble A x.out bytesCap bytesPtr (BitVec.ofNat 64 (b0 :: bsRest).length) q_sp0
    have hslot := slot_a8_put_collapse s0.sp (BitVec.ofNat 64 (b0 :: bsRest).length)
    have hgrp : epilogueOut s0 x okTagVec bytesCap bytesPtr (BitVec.ofNat 64 (b0 :: bsRest).length) q_sp0 ∗ F_end =
      (((x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((x.out + 8#64) ↦₆₄ bytesCap) ∗ ((x.out + 0x10#64) ↦₆₄ bytesPtr) ∗
          ((x.out + 0x18#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗ ((x.out + 0x20#64) ↦₁₂₈ q_sp0)) ∗
        (memRegion (s0.sp - 0xa8#64) 24 ∗ ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗ memRegion (s0.sp - 0x88#64) 16) ∗
        (dirAt A x.self (x.dir.put (keyName x.id) []) ∗ memRegion (s0.sp - 0x78#64) 24 ∗ ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
          memRegion (s0.sp - 0xb0#64) 8 ∗ savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗ A.pool)) := by unfold epilogueOut F_end okTagVec; ac_rfl
    rw [hgrp]; exact Entails.trans (sepConj_mono hok (sepConj_mono_left hslot)) (Entails.of_eq (by ac_rfl))
  apply StoreKit.sepWP_seq_lscro (mid := (blkPl_575).base + 264#64) hcrlm5; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs); intro _hcrl_108
  refine hep x s0 _ okTagVec bytesCap bytesPtr (BitVec.ofNat 64 (b0 :: bsRest).length) q_sp0 _ F_end
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hsp_align
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by have hpull : ((dirAt A x.self (x.dir.put (keyName x.id) []) ∗ memRegion (s0.sp - 0x78#64) 24 ∗
            memRegion (s0.sp - 0xa8#64) 24 ∗ stackAt (s0.sp - 0xc0#64) putStk ∗ A.pool) ∗ F_put) =
          ((memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - putStk) ∗
              stackAt (s0.sp - 0xc0#64) putStk) ∗ epiloguePre s0 x q_sp0 ∗
            (dirAt A x.self (x.dir.put (keyName x.id) []) ∗ memRegion (s0.sp - 0x78#64) 24 ∗ memRegion (s0.sp - 0xa8#64) 24 ∗
              ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗ memRegion (s0.sp - 0x88#64) 16 ∗ memRegion (s0.sp - 0xb0#64) 8 ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗ A.pool)) := by unfold F_put epiloguePre; ac_rfl
        rw [hpull, hrestk_ext]; unfold F_end; exact Entails.of_eq (by ac_rfl))
    fun sf P_f htr_f hsp_f hcs_f hPf => hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf

set_option maxHeartbeats 400000 in
private theorem pkRemovePoll_local_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hDecimal : subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hPut : subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (lsmpl.base 542) (dirPutSpecPlaced A putStk))
    (hFs : TraceFsSound ((blkPC_575).rebase (blkPl_575).base H)) (hstk : pollMinStk decStk getStk putStk ≤ stk) :
    subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (blkPl_575).base (pkRemovePollSpecPlaced rd pathOk A stk) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp_al0
  have hsp_align : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_al0
  have hDecFs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  have hbrErr := @pkrm_branch_err_local _ A H rd pathOk decStk getStk putStk stk hC
  have hbrNil := @pkrm_branch_ok_nil_local _ A H rd pathOk decStk getStk putStk stk hC
  have hbrCons := @pkrm_branch_ok_cons_local _ A H rd pathOk decStk getStk putStk stk hC hDecimal hPut
  clear hFs hDecimal hPut hC; refine ⟨(pkRemovePollSpecPlaced rd pathOk A stk).pre x s0, R, hpre, ?_⟩
  generalize hQ_eq : (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A stk).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q
  generalize hQp_eq : (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A stk).onPanic x s0 sf ∗ R)) = Qp
  have hpan_fn : ∀ (sf : State) (P_f : SepProp), (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f := by
    rw [← hQp_eq]; intro sf P_f halloc hmf; dsimp only [pkRemovePollSpecPlaced, StoreKit.withLsCodeRoLoaded]
    simpa only [sepConj_assoc] using allowPanic_panicked halloc hmf
  dsimp only [pkRemovePollSpecPlaced, StoreKit.withLsCodeRoLoaded]; rw [sepConj_comm]
  refine SepWPp.pure_elim fun hcrl0 => SepWPp.pure_elim fun ⟨hx0_0, hx8_0, ⟨hname_lt, hdir_lt, hpOk⟩, hdchg⟩ => ?_
  refine sepWPp_with_stk_bound (a := x.fut) (v := x.self)
    (Rest := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗ memRegion (x.fut + 0xd#64) 3 ∗
      dirAt A x.self x.dir ∗ memRegion x.out 48 ∗ A.pool) (Entails.of_eq (by unfold pkBoxAt; ac_rfl)) fun hstk_hi => ?_
  have hmin_hi : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hdec_le : decStk ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hget_le : getStk ≤ subMax decStk getStk putStk := by unfold subMax; omega
  rw [stackAt_sub_split s0.sp hstk hstk_hi, stackAt_pkRemove_eq s0.sp hmin_hi, subStack_split s0.sp hdec_le hmin_hi]
  unfold pkBoxAt pkRemoveFrameSlots; simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun q_sp0 => SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 => SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 => SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 =>
    SepWPp.exists_elim fun c10 => ?_
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 597) hcrl0; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs); intro hcrl1
  refine sepWPp_name_state_placed fun s1 hs1 => ?_
  have hs1_pc : s1.pc = lsmpl.base 597 := by rw [hs1]; simp only [wp_norm, arm64_norm, *]; try bv_omega
  have hs1_lr : s1.readReg64 Reg.lr = (blkPl_575).base + 68#64 := by rw [hs1]; simp only [wp_norm, arm64_norm, *]
  have hs1_run : s1.status = .Running := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_sp : s1.sp = s0.sp - 0xc0#64 := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_tr : s1.trace = s0.trace := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_fs : s1.fs = s0.fs := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x0 : s1.readReg64 .x0 = s0.sp - 0x78#64 := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x1 : s1.readReg32 .x1 = x.id := by rw [hs1]; simp only [arm64_norm, *]
  rw [← hs1] at hcrl1
  let F_dec1 : SepProp :=
    pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk)) (subMax decStk getStk putStk - decStk) ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗ memRegion (s0.sp - 0xa8#64) 48 ∗ savedCalleeSlots s0
  refine pkrm_call_decimal_fs_placed hDecFs { n := x.id, ret := s0.sp - 0x78#64 } F_dec1 (s0 := s0)
    hs1_pc hs1_run (spAligned_sub_c0 hsp_align hs1_sp) hs1_lr hs1_tr hcrl1
    (by rw [← hs1_fs, ← hs1_tr]; exact FsInv.of_entry s1) hs1_x0 hs1_x1 hpan_fn
    (Entails.of_eq (by rw [hs1_sp]; unfold F_dec1 pkBoxAt savedCalleeSlots
                       dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.lr]; ac_rfl))
    fun sm1 hpcm1 hrunm1 hspm1 hcsm1 hcrlm1 hfsm1 htrm1 => ?_
  rw [hs1_sp]
  obtain ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩ := hcsm1
  have hsp_m1 : sm1.sp = s0.sp - 0xc0#64 := hspm1.trans hs1_sp
  have hsp_al1 : sm1.spAligned = true := spAligned_sub_c0 hsp_align hsp_m1
  have hx19_m1 : sm1.readReg64 .x19 = x.fut := hx19_1.trans (by rw [hs1]; simp only [arm64_norm, *])
  have hx20_m1 : sm1.readReg64 .x20 = x.out := hx20_1.trans (by rw [hs1]; simp only [arm64_norm, *])
  have hx22_m1 : sm1.readReg64 .x22 = x.self := hx22_1.trans (by rw [hs1]; simp only [arm64_norm, *])
  have hx23_m1 : sm1.readReg64 .x23 = BitVec.setWidth 64 x.id := hx23_1.trans (by rw [hs1]; simp only [arm64_norm, *])
  have hx28_m1 : sm1.readReg64 .x28 = s0.readReg64 .x28 := hx28_1.trans (by rw [hs1]; simp only [arm64_norm, *])
  have hfp_m1 : sm1.readReg64 .x29 = s0.sp - 0x60#64 := hfp_1.trans (by rw [hs1]; simp only [arm64_norm, *])
  have hvregs_m1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := hvregs_1.trans (by rw [hs1]; simp only [arm64_norm, *])
  have htr_m1 : sm1.trace = s0.trace := htrm1.trans hs1_tr
  have hfiles_m1 : sm1.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfsm1 htr_m1
  clear hs1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  let nameBs := keyName x.id
  have hrestk1 :
      stackAt (s0.sp - 0xc0#64) decStk ∗
        memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - decStk) =
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - getStk) ∗ stackAt (s0.sp - 0xc0#64) getStk := by
    rw [sepConj_comm, ← subStack_split s0.sp hdec_le hmin_hi, subStack_split s0.sp hget_le hmin_hi]
  unfold F_dec1
  change SepWPp _ _ _ ((vecU8 A (s0.sp - 0x78#64) nameBs ∗ stackAt (s0.sp - 0xc0#64) decStk ∗ A.pool) ∗ _) _ _
  rw [vecU8_eq_bytes_tail A (s0.sp - 0x78#64) nameBs (s0.sp - 0x70#64) (s0.sp - 0x68#64)
        (by bv_omega) (by bv_omega)]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun nameCap => SepWPp.exists_elim fun namePtr =>
    SepWPp.pure_elim fun ⟨hnlen, hnlt, hnptr⟩ => ?_
  refine sepWPp_conseq
    (P' := ((stackAt (s0.sp - 0xc0#64) decStk ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - decStk)) ∗
      ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
      ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
      SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗ vecU8Tail A nameCap namePtr nameBs ∗
      A.pool ∗ pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
      ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗
      memRegion (s0.sp - 0xa8#64) 48 ∗ savedCalleeSlots s0))
    (Entails.of_eq (by ac_rfl)) ?_
  rw [hrestk1]; simp only [sepConj_assoc]
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 589) hcrlm1
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl2
  have hx3_len : (BitVec.ofNat 64 nameBs.length).toNat = nameBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPp_name_state_placed fun s2 hs2 => ?_
  have hs2_pc : s2.pc = lsmpl.base 589 := by rw [hs2]; simp only [wp_norm, arm64_norm, *]; try bv_omega
  have hs2_lr : s2.readReg64 Reg.lr = (blkPl_575).base + 88#64 := by rw [hs2]; simp only [wp_norm, arm64_norm, *]
  have hs2_run : s2.status = .Running := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_sp : s2.sp = s0.sp - 0xc0#64 := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_tr : s2.trace = s0.trace := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_files : s2.fs.files = s0.fs.files := by
    have hs2_fs : s2.fs = sm1.fs := by rw [hs2]; simp only [arm64_norm, *]
    rw [hs2_fs]; exact hfiles_m1
  have hs2_x0 : s2.readReg64 .x0 = s0.sp - 0xa8#64 := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x1 : s2.readReg64 .x1 = x.self := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x2 : s2.readReg64 .x2 = namePtr := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x3 : (s2.readReg64 .x3).toNat = nameBs.length := by rw [hs2]; simp only [arm64_norm, *]
  rw [← hs2] at hcrl2
  let F_get : SepProp :=
    ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗ vecU8Tail A nameCap namePtr nameBs ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗ savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - getStk) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion x.out 48 ∗ pkBoxAt x.fut x.self x.id 0#8
  refine pkrm_call_dirGet_placed hGet
    { ret := s0.sp - 0xa8#64, self := x.self, dir := x.dir,
      nameA := namePtr, name := nameBs, nameRo := false } F_get (s0 := s0)
    hs2_pc hs2_run (spAligned_sub_c0 hsp_align hs2_sp) hs2_lr hs2_tr hcrl2
    hs2_x0 hs2_x1 hs2_x2 hs2_x3 hname_lt hdir_lt hpOk hpan_fn
    (Entails.of_eq (by rw [hs2_sp]; unfold F_get; dsimp only; ac_rfl))
    fun sm2 gr hpcm2 hrunm2 hspm2 hcsm2 hcrlm2 hgr => ?_
  rw [hs2_sp]
  obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
  have hsp_m2 : sm2.sp = s0.sp - 0xc0#64 := hspm2.trans hs2_sp
  have hx19_m2 : sm2.readReg64 .x19 = x.fut := hx19_2.trans (by rw [hs2]; simp only [arm64_norm, *])
  have hx20_m2 : sm2.readReg64 .x20 = x.out := hx20_2.trans (by rw [hs2]; simp only [arm64_norm, *])
  have hx21_m2 : sm2.readReg64 .x21 = namePtr := hx21_2.trans (by rw [hs2]; simp only [arm64_norm, *])
  have hx22_m2 : sm2.readReg64 .x22 = x.self := hx22_2.trans (by rw [hs2]; simp only [arm64_norm, *])
  have hx23_m2 : sm2.readReg64 .x23 = BitVec.setWidth 64 x.id :=
    hx23_2.trans (by rw [hs2]; simp only [arm64_norm, *])
  have hx28_m2 : sm2.readReg64 .x28 = s0.readReg64 .x28 := hx28_2.trans (by rw [hs2]; simp only [arm64_norm, *])
  have hfp_m2 : sm2.readReg64 .x29 = s0.sp - 0x60#64 := hfp_2.trans (by rw [hs2]; simp only [arm64_norm, *])
  have hvregs_m2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 :=
    hvregs_2.trans (by rw [hs2]; simp only [arm64_norm, *])
  clear hs2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  have hgr0 : gr = x.dir.get rd s0.fs.files (keyName x.id) ∧ sm2.trace = s0.trace :=
    ⟨by simpa only [nameBs, hs2_files] using hgr.1, hgr.2.trans hs2_tr⟩
  clear hs2_files hgr
  have hpost_get :
      ((getResultAt A (s0.sp - 0xa8#64) gr ∗ dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
        stackAt (s0.sp - 0xc0#64) getStk ∗ A.pool) ∗ F_get) ⊢
      getResultAt A (s0.sp - 0xa8#64) gr ∗
        postGetCommon_placed A s0 x decStk getStk putStk stk nameCap namePtr nameBs q_sp0 := by
    have hstk_merge :
        memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - getStk) ∗ stackAt (s0.sp - 0xc0#64) getStk =
        stackAt (s0.sp - 0xc0#64) (subMax decStk getStk putStk) :=
      (subStack_split s0.sp hget_le hmin_hi).symm
    unfold F_get postGetCommon_placed
    have hpull :
        ((getResultAt A (s0.sp - 0xa8#64) gr ∗ dirAt A x.self x.dir ∗
          SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
          stackAt (s0.sp - 0xc0#64) getStk ∗ A.pool) ∗
          ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗ vecU8Tail A nameCap namePtr nameBs ∗
          ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗ savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - getStk) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          memRegion x.out 48 ∗ pkBoxAt x.fut x.self x.id 0#8) =
        ((memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - getStk) ∗ stackAt (s0.sp - 0xc0#64) getStk) ∗
          (getResultAt A (s0.sp - 0xa8#64) gr ∗ ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗ ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
            SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗ vecU8Tail A nameCap namePtr nameBs ∗
            ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗ memRegion (s0.sp - 0xb0#64) 8 ∗ savedCalleeSlots s0 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
            memRegion x.out 48 ∗ pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.dir ∗ A.pool)) := by ac_rfl
    rw [hpull, hstk_merge]; exact Entails.of_eq (by ac_rfl)
  refine sepWPp_conseq hpost_get ?_
  subst hQ_eq hQp_eq
  rcases gr with ⟨⟩ | ⟨_ | ⟨b0, bsRest⟩⟩
  · apply sepWPp_of_sepWP_final_placed
    exact hbrErr x R s0 sm2 nameCap namePtr nameBs q_sp0
      hstk hstk_hi hnlen hnlt hnptr hgr0
      hpcm2 hrunm2 hsp_align hsp_m2 hfp_m2 hcrlm2 hx28_m2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2
  · apply sepWPp_of_sepWP_final_placed
    exact hbrNil x R s0 sm2 nameCap namePtr nameBs q_sp0
      hstk hstk_hi hnlen hnlt hnptr hgr0
      hpcm2 hrunm2 hsp_align hsp_m2 hfp_m2 hcrlm2 hx28_m2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2
  · exact hbrCons x R s0 sm2 b0 bsRest nameCap namePtr nameBs q_sp0
      hstk hstk_hi hdchg hnlen hnlt hnptr hgr0
      hpcm2 hrunm2 hsp_align hsp_m2 hfp_m2 hcrlm2
      hx28_m2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2 hx22_m2 hx23_m2

end LocalPkRemovePoll

private theorem cliPollPk_removePoll_rocl [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (pkId : BitVec 32)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hread : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 F0 pkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + pkKit.removePollOff)
      (withLsRoCl lsmpl (kitPreKeyRemovePollSpecE pkKit)) := by
  intro pkKit
  have hDec := Store.PlacedCommon.ls_transfer_lscro
    (callerProg := lsProg_575 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (SessKit.cliDecimal_placed_ok hh) (by decide) (by decide) (by decide)
  have hGet := Store.PlacedCommon.ls_transfer_lscro
    (callerProg := lsProg_575 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (SessKit.cliDirGet_placed_ok (readProg := readProg) (jRead := jRead)
      (fun _ hp => hp.2) hh
      (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hread) hjRead hjRead_unmut)
    (by decide) (by decide) (by decide)
  have hPut := Store.PlacedCommon.ls_transfer_lscro
    (callerProg := lsProg_575 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (SessKit.cliDirPut_placed_ok hh) (by decide) (by decide) (by decide)
  have hhop0 := pkRemovePoll_local_placed_ok hh.alloc
    hDec hGet hPut (hh.fs (lsProg_575 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 575)
    (stk := (cliKitStk B).pkRemovePoll)
    (by dsimp [cliKitStk, Store.PkRemovePoll.Helpers.pollMinStk, Store.PkRemovePoll.Helpers.subMax,
      SessKit.decNeedPlaced, SessKit.dirPutNeedPlaced, SessKit.decNeed, SessKit.dirPutNeed,
      SessKit.growOneDirNeedPlaced, SessKit.growOneDirNeed, doReserveStackX, pathNeed,
      RunBudgets.dirGetNeed, extHookStack]; omega)
  have hhop := Store.PlacedCommon.ls_transfer_lscro (callerProg := callerProg) (j := 575) hhop0 hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 575) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨fut, out, self, id⟩, st0⟩ R s0 hpc hrun hpre hsp _ => ?_
  change DirGhost at st0
  obtain ⟨hcrl, hpre1⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0⌝ ∗
      ((kitPreKeyRemovePollSpec pkKit).pre (⟨fut, out, self, id⟩, st0) s0 ∗ R) := by
    change s0.mem ⊨ (⌜s0.fs.files = F0⌝ ∗
      (kitPreKeyRemovePollSpec pkKit).pre (⟨fut, out, self, id⟩, st0) s0) ∗ R at hpre1
    simpa only [sepConj_assoc] using hpre1
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨hfiles, hpre3⟩ := hpre2
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧ id = pkId⌝ ∗
      pkBoxAt fut self id 0#8 ∗ (⌜CliPkInv cliIo.rd F0 cliWrOk pkId st0⌝ ∗ dirAt E2E.HooksE.A0 self st0) ∗
      memRegion out 48 ∗ E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).pkRemovePoll) ∗ R at hpre3
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
  obtain ⟨⟨_, hx0, hx8, rfl⟩, hpre4⟩ := hpre3
  have hpre5 : s0.mem ⊨ ⌜CliPkInv cliIo.rd F0 cliWrOk id st0⌝ ∗
      (pkBoxAt fut self id 0#8 ∗ dirAt E2E.HooksE.A0 self st0 ∗ memRegion out 48 ∗
        E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).pkRemovePoll ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre4
  rw [satisfies_pure_sepConj] at hpre5
  obtain ⟨hinv, hspatial⟩ := hpre5
  let xg : PkPollGhost := ⟨fut, out, self, id, st0⟩
  have hpre_hop : s0.mem ⊨
      (pkRemovePollSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 (cliKitStk B).pkRemovePoll).pre xg s0 ∗ R := by
    dsimp only [pkRemovePollSpecPlaced, StoreKit.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hinv.nameOk, hinv.oneLt.1⟩, ?_⟩
    simpa only [sepConj_assoc] using hspatial
  refine subroutine_ok.mono_outcome hhop xg R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left ?_) hpost⟩
    show (pkRemovePollSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 (cliKitStk B).pkRemovePoll).post xg s0 sf ⊢
      (kitPreKeyRemovePollSpec pkKit).post (⟨fut, out, self, id⟩, st0) s0 sf
    dsimp only [pkRemovePollSpecPlaced, kitPreKeyRemovePollSpec, pkKit, cliPollPkKitPlaced,
      Poll.cliPreKeyStoreSpecPlaced, cliPreKeyStoreSpec, cliPkStoreAt, xg]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun res => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hres, htr⟩ => ?_
    rw [hfiles] at hres; subst hres
    set m := pkRemoveOf st0 (keyName id) (st0.get cliIo.rd F0 (keyName id))
    have hent0 := KitInst.pkRemoveOutAt_entails_pollOut_placed E2E.HooksE.A0 cliIo.rd F0 cliWrOk id
      (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
      (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll st0 id out
    dsimp only at hent0
    have hout_eq : preKeyRemovePollOutAt (KitInst.cliPreKeyStoreSpecPlaced E2E.HooksE.A0 cliIo.rd F0 cliWrOk id
        (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
        (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll) out =
      preKeyRemovePollOutAt pkKit out := by funext ans; cases ans <;> rfl
    rw [hout_eq] at hent0
    refine Entails.trans (Entails.of_eq (show _ = pkRemoveOutAt E2E.HooksE.A0 out m.1 ∗
      (dirAt E2E.HooksE.A0 self m.2 ∗ pkBoxAt fut self id 1#8 ∗
        E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).pkRemovePoll) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hent0) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ans => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hrel, heq2⟩ => ?_
    rw [heq2]
    refine Entails.sepExists_right ans (Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr⟩ ?_)
    exact Entails.trans (Entails.pure_right hinv.removePreKey (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem cliPollPk_removeKitPlacedOk [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (pkId : BitVec 32) (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hread : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    PreKeyRemoveKitPlacedOk (cliPollPkKitPlaced E2E.HooksE.A0 F0 pkId (cliKitStk B))
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  removeShim hblk := cliPollPk_removeShim_rocl mmpl gh W B F0 pkId hh hblk
  removePoll hblk := cliPollPk_removePoll_rocl mmpl gh W B F0 pkId hh hread hjRead hjRead_unmut hblk
  removeFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]; exact IdKit.cliIdFutDrop_rocl_placed_ok hblk

private theorem stageP4BranchPlaced_of_kits [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {pkKit : PreKeyStoreSpec A 0#64} {kpkKit : KyberPreKeyStoreSpec A 0#64}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {s0 s : State}
    {coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64}
    {opkId? : Option (BitVec 32)} {kyberPreKeyId signedPreKeyId : BitVec 32}
    {pt : List (BitVec 8)} {peer : AddrGhost} {remoteIk : IdentityKey} {baseKey : PublicKey}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState} {pst0 : pkKit.PkState} {kst0 : kpkKit.KpkState}
    {ss : Session (List (BitVec 8))} {sf : State} {Pf : SepProp}
    (h : Kits.StageP4BranchPlaced kit ikit pkKit kpkKit encRecord s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
      prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt peer remoteIk
      baseKey sst0 ist0 pst0 kst0 ss sf Pf) :
    StageP4BranchPlaced kit ikit pkKit kpkKit encRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr
      remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr
      v_3d0 opkId? kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf := by
  cases h with
  | ok c hsave hmark hrem hstore htr hpost => exact .ok c hsave hmark hrem hstore htr hpost
  | saveErr hsave htr hpost => exact .saveErr hsave htr hpost
  | markErr c e hsave hmark htr hpost => exact .markErr c e hsave hmark htr hpost
  | removeErr opkId c e hopk hsave hmark hrem htr hpost => exact .removeErr opkId c e hopk hsave hmark hrem htr hpost
  | storeErr c hsave hmark hrem hstore htr hpost => exact .storeErr c hsave hmark hrem hstore htr hpost

/-- Instantiates `Poll.StageP4PathAPlacedStmt` via `Kits.stageP4_v1_vregs_mark_remove_placed_ok`. -/
theorem stageP4PathA_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP4PathAPlacedStmt := by
  intro mmpl gh W B F0 peer pid kpkId spkId kbk σ kit ikit pkKit kpkKit hh hread hdeser
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId
    b_2c0 pt remoteIk baseKey sst0 ist0 pst0 kst0 G ss
    hprev_nz hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok
    hpt_le hcap_lt hptr_nz hsp_ub hfs hcro hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  have hdealloc : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec E2E.HooksE.A0) :=
    ls_hook_ok_ultra_of_mem hh.codecHooks.dealloc (by decide)
  have hDrop : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec E2E.HooksE.A0)) :=
    cliDropSessionStructure4_placed_ok_at mmpl gh W hh
      (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
  have hSkit : SessionOnlyKitPlacedOkSE kit Slots.scopeKit E2E.Record.encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    SessKit.cliSessKitOkSE_placed
      (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
      (deserProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (deserBlk := 518)
      (serProg := CryptoVerification.E2E.Record.Placed.lsProg_52
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) (serBlk := 52)
      hDropNz (fun _ hp => hp.2) hh
      (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hread)
      hdeser
      (cliSerializeCanonX_placed_ok mmpl gh W hh)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hSvt : SessionOnlyVtablesPlacedOk kit := cliPollSess_vtablesPlacedOk F0 Slots.scopeKit peer σ hDropNz
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
  have hKpkVt : KyberPreKeyVtablesPlacedOk kpkKit := cliPollKpk_vtablesPlacedOk F0 kpkId spkId kbk σ hDropNz
  refine SepWPp.mono_post_panic ?_ (fun _ _ h => h)
    (Kits.stageP4_v1_vregs_mark_remove_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.scopeKit E2E.Record.encodeRecord kit ikit pkKit kpkKit
      hdealloc hDrop hSkit hSvt hIkit hIvt hPkKit hPkVt hKpkKit hKpkVt
      s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId
      b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
      hprev_nz hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok
      hpt_le hcap_lt hptr_nz hsp_ub hfs hcro hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs)
  rintro sf Pf ⟨hst, hspf, hcsf, hvregsf, hcrof, hbr⟩
  exact ⟨hst, hspf, hcsf, hvregsf, hcrof, stageP4BranchPlaced_of_kits hbr⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
