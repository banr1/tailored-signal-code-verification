/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Assembly
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.CliExternsWitness
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4

/-!
# Relocatable Top-Level Stage Assembly for `signal_session_handshake::initiate`

Composes `signal_session_coins_fill_placed_ok_at_init`, `initStoreCallees_placed_ok`,
`initLocalCallees_placed_ok`, and Stages 1–5 on block `521` (`initProgPlaced mmpl gh W`) under
`[LibsignalPlacement]`, and transfers the contract to caller blocks `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  LibsignalCodeRoLoaded withLsCodeRoLoaded extract_withLsCodeRoLoaded
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-- Stage 2 (`0x0390 → 0x0760`) continuation contract under `[LibsignalPlacement]`. -/
def Stage2PlacedOk [LibsignalPlacement] (A : RustAlloc) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) : Prop :=
  ∀ {x : InitGhost} {be : PreKeyBundleFields} {stk : Nat} {s0 s2 : State}
    {Q Qp : State → SepProp → Prop},
    RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    (∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk))) →
    InitStoreCalleesPlaced A mmpl gh W B stk →
    InitLocalCalleesPlaced A mmpl gh W stk →
    S.initiate = initDef X ⟨W.C, W.Q⟩ →
    InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
    x.coins.length < 2 ^ 63 →
    cliInitiateNeed B ≤ stk →
    stk ≤ 2 ^ 63 →
    stk ≤ s0.sp.toNat →
    AtStage2Placed W X x be s0 s2 →
    (∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf) →
    (∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf) →
    (∀ (s3 : State) (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
        (pqspkPtr : BitVec 64) (opkId : BitVec 32),
      AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
        (stage3MemPlaced A x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0)) →
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s2
      (stage2MemPlaced A x stk s0) Q Qp (initOom s0)

/-- Stage 3 (`0x0760 → 0x10a4`) continuation contract under `[LibsignalPlacement]`. -/
def Stage3PlacedOk [LibsignalPlacement] (A : RustAlloc) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem) : Prop :=
  ∀ {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop},
    RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    (∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk))) →
    InitLocalCalleesPlaced A mmpl gh W stk →
    S.initiate = initDef X ⟨W.C, W.Q⟩ →
    InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
    x.coins.length < 2 ^ 63 →
    cliInitiateNeed B ≤ stk →
    stk ≤ 2 ^ 63 →
    stk ≤ s0.sp.toNat →
    AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
    (∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf) →
    (∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf) →
    (∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
        Q Qp (initOom s0)) →
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0)

theorem subroutine_ok_of_sepWPp_init_placed [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {stk : Nat}
    (h : ∀ (x : InitGhost) (R : SepProp) (s0 : State),
      s0.pc = initEntryPlaced →
      s0.status = .Running →
      (s0.mem ⊨ (initSlotSpecPlaced A S stk).pre x s0 ∗ R) →
      s0.spAligned = true →
      ∃ P0, (s0.mem ⊨ P0 ∗ R) ∧
        SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s0 P0
          (fun sf Pf =>
            ((sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (initSlotSpecPlaced A S stk).post x s0 sf ∗ R)) ∧
              sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf Pf =>
            (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (initSlotSpecPlaced A S stk).onPanic x s0 sf ∗ R))
          (initOom s0)) :
    subroutine_ok (initProgPlaced mmpl gh W) initEntryPlaced (initSlotSpecPlaced A S stk) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal hL
  obtain ⟨P0, hm0, hwp⟩ := h x R s0 hpc hrun hpre hal
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm0 hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpcsf, hrunsf, Pf, hmPf, hpost, hsp, hcs⟩ | ⟨hpansf, Pf, hmPf, hpan⟩ | ⟨hoomsf, hmOom⟩
  · exact Or.inl ⟨⟨hpcsf, hsp, hrunsf⟩, ⟨hsp, hcs⟩, hpost hmPf⟩
  · exact Or.inr (Or.inl ⟨hpansf, hpan hmPf⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨hoomsf, hmOom⟩))

/-- Relocatable top-level `initiate` slot theorem on block `521` (`initProgPlaced mmpl gh W`). -/
theorem cliInitiate_placed_ok_proof [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced A mmpl gh W)
    (hStage2 : Stage2PlacedOk A mmpl gh W X B S)
    (hStage3 : Stage3PlacedOk A mmpl gh W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) initEntryPlaced (initSlotSpecPlaced A S stk) := by
  have : InitTraceFsSound mmpl gh W := ⟨hh.fs⟩
  have hStore : InitStoreCalleesPlaced A mmpl gh W B stk :=
    initStoreCallees_placed_ok mmpl gh W B hh hExist stk hstk hstk64
  have hLocal : InitLocalCalleesPlaced A mmpl gh W stk :=
    initLocalCallees_placed_ok mmpl gh W B hh ha4 stk hstk hstk64
  have hCoinsRoCl : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsRoCl lsmpl (coinsFillSpecPlacedW3 cStk)) :=
    fun hc1 hc2 => signal_session_coins_fill_placed_ok_at_init mmpl gh W hh.allocFs hc1 hc2
  have hCoins : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)) := by
    intro cStk hc1 hc2
    exact subroutine_ok_mono (hCoinsRoCl hc1 hc2)
      (fun _ _ _ hp => hp)
      (fun _ _ _ _ hq => by
        dsimp only [withLsRoCl, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
  apply subroutine_ok_of_sepWPp_init_placed
  intro x R s0 hpc hrun0 hpre hal
  have hpre' : s0.mem ⊨
      ⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      ⌜s0.readReg64 .x0 = x.peerA ∧ s0.readReg64 .x1 = x.meA ∧
        s0.readReg64 .x2 = x.stores + 0xf0#64 ∧ s0.readReg64 .x3 = lsρ cliSessionVtSym ∧
        s0.readReg64 .x4 = x.stores ∧ s0.readReg64 .x5 = lsρ cliIdentityVtSym ∧
        s0.readReg64 .x6 = x.bundleA ∧ s0.readReg64 .x7 = 0#64 ∧
        s0.readReg64 .x8 = x.ret ∧ s0.fs.files = x.F ∧
        S.filesOk x.F x.peer.val x.me.val ∧ S.initOk x.F x.peer.val x.me.val ∧
        stk ≤ s0.sp.toNat⌝ ∗
      slotFramePlaced A x.toSlotCtx ∗
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ R := by
    dsimp only [initSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  simp only [slotFramePlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  obtain ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfs0, hfilesOk, hsInitOk, hspk⟩,
    hcoinsLt, hm⟩ := hpre'
  have hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val :=
    hok x.F x.peer.val x.me.val hfilesOk hsInitOk
  have hs0 : AtInitEntryPlaced x s0 :=
    { pc := hpc
      run := hrun0
      inv := hinv
      spAligned := hal
      x0 := hx0
      x1 := hx1
      x2 := hx2
      x3 := hx3
      x4 := hx4
      x5 := hx5
      x6 := hx6
      x7 := hx7
      x8 := hx8
      files := hfs0 }
  refine ⟨initEntryMemPlaced A x stk s0, ?_, ?_⟩
  · simpa only [initEntryMemPlaced, sepConj_assoc] using hm
  · have hpostK : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf →
        (((sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (initSlotSpecPlaced A S stk).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
      intro sf Pf ⟨hsp, hcs, hent⟩
      exact ⟨fun hmPf => Satisfies.mono (sepConj_mono_left hent) hmPf, hsp, hcs⟩
    have hpanicK : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf →
        ((sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (initSlotSpecPlaced A S stk).onPanic x s0 sf ∗ R)) := by
      intro sf Pf hent hmPf
      exact Satisfies.mono (sepConj_mono_left hent) hmPf
    exact initiate_stage1_placed_ok hh hStore hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs0
      hpostK hpanicK fun s2 be hs2 =>
        hStage2 hh @hCoins hStore hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs2
          hpostK hpanicK fun s3 kp ekASk ekAPk pqspkPtr opkId hs3 =>
            hStage3 hh @hCoins hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs3
              hpostK hpanicK fun s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr hs4 =>
                initiate_stage4_placed_ok hh @hCoinsRoCl hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs4
                  hpostK hpanicK fun s5 sg ss hs5 =>
                    initiate_stage5_placed_ok hh hStore hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs5
                      hpostK hpanicK

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
